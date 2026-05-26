//! Static checks that admit a module: scope/arity well-formedness, and the
//! totality guarantee — structural recursion plus a ban on mutual recursion.
//!
//! These are what make [`super::reduce::normalize`] terminate, so they are part
//! of the trust story even though they are not the proof kernel itself.
//!
//! Not done in M0 (no type checker yet): type correctness of expressions and
//! `match` exhaustiveness. Tracked in ROADMAP.

use std::collections::{HashMap, HashSet};

use super::ast::*;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CheckError {
    UnboundVar { func: String, var: String },
    UnknownCtor { func: String, ctor: String },
    CtorArity { func: String, ctor: String, expected: usize, got: usize },
    UnknownFn { func: String, callee: String },
    FnArity { func: String, callee: String, expected: usize, got: usize },
    /// A self-recursive function with no argument that strictly decreases.
    NonStructuralRecursion { func: String },
    /// Two functions that (transitively) call each other; out of pilot scope.
    MutualRecursion { a: String, b: String },
}

pub fn check_module(m: &Module) -> Result<(), Vec<CheckError>> {
    let mut errs = Vec::new();
    for f in &m.fns {
        check_wellformed(m, f, &mut errs);
        check_structural_recursion(f, &mut errs);
    }
    check_no_mutual_recursion(m, &mut errs);
    if errs.is_empty() { Ok(()) } else { Err(errs) }
}

// --- well-formedness: every var is bound, every ctor/fn exists with right arity

fn check_wellformed(m: &Module, f: &FnDef, errs: &mut Vec<CheckError>) {
    let scope: HashSet<String> = f.params.iter().map(|p| p.name.clone()).collect();
    walk(m, f, &f.body, &scope, errs);
}

fn walk(m: &Module, f: &FnDef, e: &Expr, scope: &HashSet<String>, errs: &mut Vec<CheckError>) {
    match e {
        Expr::Var { name } => {
            if !scope.contains(name) {
                errs.push(CheckError::UnboundVar { func: f.name.clone(), var: name.clone() });
            }
        }
        Expr::Ctor { name, args } => {
            match m.ctor_def(name) {
                None => errs.push(CheckError::UnknownCtor { func: f.name.clone(), ctor: name.clone() }),
                Some(c) if c.fields.len() != args.len() => errs.push(CheckError::CtorArity {
                    func: f.name.clone(),
                    ctor: name.clone(),
                    expected: c.fields.len(),
                    got: args.len(),
                }),
                _ => {}
            }
            for a in args {
                walk(m, f, a, scope, errs);
            }
        }
        Expr::Call { name, args } => {
            match m.fn_def(name) {
                None => errs.push(CheckError::UnknownFn { func: f.name.clone(), callee: name.clone() }),
                Some(g) if g.params.len() != args.len() => errs.push(CheckError::FnArity {
                    func: f.name.clone(),
                    callee: name.clone(),
                    expected: g.params.len(),
                    got: args.len(),
                }),
                _ => {}
            }
            for a in args {
                walk(m, f, a, scope, errs);
            }
        }
        Expr::Match { scrutinee, arms } => {
            walk(m, f, scrutinee, scope, errs);
            for arm in arms {
                match m.ctor_def(&arm.ctor) {
                    None => errs.push(CheckError::UnknownCtor { func: f.name.clone(), ctor: arm.ctor.clone() }),
                    Some(c) if c.fields.len() != arm.binds.len() => errs.push(CheckError::CtorArity {
                        func: f.name.clone(),
                        ctor: arm.ctor.clone(),
                        expected: c.fields.len(),
                        got: arm.binds.len(),
                    }),
                    _ => {}
                }
                let mut inner = scope.clone();
                inner.extend(arm.binds.iter().cloned());
                walk(m, f, &arm.body, &inner, errs);
            }
        }
    }
}

// --- structural recursion
//
// Provenance of a variable, relative to the function's parameters:
//   Param(i)   == the value of parameter i
//   Smaller(i) == a strict subterm of parameter i (obtained by matching)
// A self-call decreases at position j when argument j is a variable that is a
// strict subterm of parameter j. The recursion terminates if some single
// position j decreases in *every* self-call, so we require the intersection of
// the per-call "good position" sets to be non-empty.

#[derive(Clone, Copy)]
enum Prov {
    Param(usize),
    Smaller(usize),
    Unknown,
}

fn check_structural_recursion(f: &FnDef, errs: &mut Vec<CheckError>) {
    let mut prov: HashMap<String, Prov> = HashMap::new();
    for (i, p) in f.params.iter().enumerate() {
        prov.insert(p.name.clone(), Prov::Param(i));
    }
    let mut good_sets: Vec<HashSet<usize>> = Vec::new();
    collect_self_calls(f, &f.body, &prov, &mut good_sets);

    if good_sets.is_empty() {
        return; // not self-recursive
    }
    let common = good_sets
        .iter()
        .skip(1)
        .fold(good_sets[0].clone(), |acc, s| acc.intersection(s).copied().collect());
    if common.is_empty() {
        errs.push(CheckError::NonStructuralRecursion { func: f.name.clone() });
    }
}

fn collect_self_calls(
    f: &FnDef,
    e: &Expr,
    prov: &HashMap<String, Prov>,
    out: &mut Vec<HashSet<usize>>,
) {
    match e {
        Expr::Var { .. } => {}
        Expr::Ctor { args, .. } => {
            for a in args {
                collect_self_calls(f, a, prov, out);
            }
        }
        Expr::Call { name, args } => {
            if name == &f.name {
                let mut good = HashSet::new();
                for (j, a) in args.iter().enumerate() {
                    if let Expr::Var { name: vn } = a
                        && let Some(&Prov::Smaller(i)) = prov.get(vn)
                        && i == j
                    {
                        good.insert(j);
                    }
                }
                out.push(good);
            }
            for a in args {
                collect_self_calls(f, a, prov, out);
            }
        }
        Expr::Match { scrutinee, arms } => {
            collect_self_calls(f, scrutinee, prov, out);
            // Matching on (a subterm of) parameter i makes the bound fields
            // strict subterms of parameter i.
            let origin = match scrutinee.as_ref() {
                Expr::Var { name } => match prov.get(name) {
                    Some(Prov::Param(i)) | Some(Prov::Smaller(i)) => Some(*i),
                    _ => None,
                },
                _ => None,
            };
            for arm in arms {
                let mut inner = prov.clone();
                let p = origin.map_or(Prov::Unknown, Prov::Smaller);
                for b in &arm.binds {
                    inner.insert(b.clone(), p);
                }
                collect_self_calls(f, &arm.body, &inner, out);
            }
        }
    }
}

// --- mutual recursion: reject any cycle of length > 1 in the call graph

#[allow(clippy::needless_range_loop)] // square adjacency matrix; indices read row k, write row i
fn check_no_mutual_recursion(m: &Module, errs: &mut Vec<CheckError>) {
    let names: Vec<&str> = m.fns.iter().map(|f| f.name.as_str()).collect();
    let index: HashMap<&str, usize> = names.iter().enumerate().map(|(i, n)| (*n, i)).collect();
    let n = names.len();

    let mut reach = vec![vec![false; n]; n];
    for (i, f) in m.fns.iter().enumerate() {
        let mut callees = HashSet::new();
        collect_callees(&f.body, &mut callees);
        for c in callees {
            if let Some(&j) = index.get(c.as_str()) {
                reach[i][j] = true;
            }
        }
    }
    // Transitive closure.
    for k in 0..n {
        for i in 0..n {
            if reach[i][k] {
                for j in 0..n {
                    if reach[k][j] {
                        reach[i][j] = true;
                    }
                }
            }
        }
    }
    for i in 0..n {
        for j in (i + 1)..n {
            if reach[i][j] && reach[j][i] {
                errs.push(CheckError::MutualRecursion {
                    a: names[i].to_string(),
                    b: names[j].to_string(),
                });
                return;
            }
        }
    }
}

fn collect_callees(e: &Expr, out: &mut HashSet<String>) {
    match e {
        Expr::Var { .. } => {}
        Expr::Ctor { args, .. } => {
            for a in args {
                collect_callees(a, out);
            }
        }
        Expr::Call { name, args } => {
            out.insert(name.clone());
            for a in args {
                collect_callees(a, out);
            }
        }
        Expr::Match { scrutinee, arms } => {
            collect_callees(scrutinee, out);
            for arm in arms {
                collect_callees(&arm.body, out);
            }
        }
    }
}
