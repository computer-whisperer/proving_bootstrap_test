//! The trusted kernel. Everything else can be wrong; if this accepts a proof,
//! the claim holds under the object language's semantics.

use std::collections::{HashMap, HashSet};

use crate::obj_lang::ast::*;
use crate::obj_lang::reduce::{reduce_iota, unfold_one};
use crate::obj_lang::subst::{free_vars, fresh_name, subst};

use super::ast::*;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProofError {
    /// `Refl` on a goal whose sides are not syntactically equal.
    NotReflexive { lhs: Box<Expr>, rhs: Box<Expr> },
    /// Induct on a variable not in the context.
    UnknownVar(String),
    /// Induct on a variable whose type is not an inductive type in the module.
    UnknownType(String),
    /// `Hyp(i)` out of range.
    NoHyp(usize),
    /// `Lemma(name)` not in the theory.
    NoLemma(String),
    /// A rewrite found no occurrence of the equation's pattern.
    RewriteNoMatch,
    /// `Unfold` of a function not defined in the module.
    UnfoldUnknownFn(String),
    /// An induction left a constructor with no matching `Case`.
    MissingCase { ctor: String },
}

/// A proof obligation: prove `lhs = rhs` for all `vars`, with `hyps` available.
#[derive(Clone, Debug)]
pub struct Sequent {
    pub vars: Vec<Param>,
    pub hyps: Vec<ForallEq>,
    pub lhs: Expr,
    pub rhs: Expr,
}

/// Lemmas proven so far, citable by name.
#[derive(Clone, Debug, Default)]
pub struct Theory {
    lemmas: Vec<(String, ForallEq)>,
}

impl Theory {
    pub fn get(&self, name: &str) -> Option<&ForallEq> {
        self.lemmas.iter().rev().find(|(n, _)| n == name).map(|(_, eq)| eq)
    }
    fn push(&mut self, name: String, eq: ForallEq) {
        self.lemmas.push((name, eq));
    }
}

/// Check a list of theorems in order, each able to cite the earlier ones.
/// Returns the accumulated theory on success.
pub fn check_theory(module: &Module, theorems: &[Theorem]) -> Result<Theory, (String, ProofError)> {
    let mut theory = Theory::default();
    for thm in theorems {
        check_theorem(module, &theory, thm).map_err(|e| (thm.name.clone(), e))?;
        theory.push(thm.name.clone(), thm.claim.clone());
    }
    Ok(theory)
}

/// Check a single theorem against an existing theory.
pub fn check_theorem(module: &Module, theory: &Theory, thm: &Theorem) -> Result<(), ProofError> {
    let seq = Sequent {
        vars: thm.claim.vars.clone(),
        hyps: Vec::new(),
        lhs: thm.claim.lhs.clone(),
        rhs: thm.claim.rhs.clone(),
    };
    check_sequent(module, theory, &seq, &thm.proof)
}

fn check_sequent(module: &Module, theory: &Theory, seq: &Sequent, proof: &Proof) -> Result<(), ProofError> {
    match proof {
        Proof::Refl => {
            if seq.lhs == seq.rhs {
                Ok(())
            } else {
                Err(ProofError::NotReflexive { lhs: Box::new(seq.lhs.clone()), rhs: Box::new(seq.rhs.clone()) })
            }
        }
        Proof::Then { step, rest } => {
            let next = apply_step(module, theory, seq, step)?;
            check_sequent(module, theory, &next, rest)
        }
        Proof::Induct { var, cases } => {
            let subgoals = do_induct(module, seq, var)?;
            for (ctor, subgoal) in subgoals {
                let case = cases
                    .iter()
                    .find(|c| c.ctor == ctor)
                    .ok_or(ProofError::MissingCase { ctor: ctor.clone() })?;
                check_sequent(module, theory, &subgoal, &case.proof)?;
            }
            Ok(())
        }
    }
}

// --- steps

fn apply_step(module: &Module, theory: &Theory, seq: &Sequent, step: &Step) -> Result<Sequent, ProofError> {
    let mut next = seq.clone();
    match step {
        Step::Unfold { func, side } => {
            if module.fn_def(func).is_none() {
                return Err(ProofError::UnfoldUnknownFn(func.clone()));
            }
            apply_side(&mut next, *side, |e| Ok(unfold_one(module, func, e)))?;
        }
        Step::Reduce { side } => {
            apply_side(&mut next, *side, |e| Ok(reduce_iota(e)))?;
        }
        Step::Rewrite { using, dir, side } => {
            let eq = resolve_eq(theory, seq, using)?;
            let (pat, rep) = match dir {
                Dir::Lr => (&eq.lhs, &eq.rhs),
                Dir::Rl => (&eq.rhs, &eq.lhs),
            };
            let pat_vars: HashSet<String> = eq.vars.iter().map(|p| p.name.clone()).collect();
            apply_side(&mut next, *side, |e| {
                rewrite_first(e, pat, rep, &pat_vars).ok_or(ProofError::RewriteNoMatch)
            })?;
        }
    }
    Ok(next)
}

/// Apply `f` to the requested side(s). For `Both`, succeeds if it applies to at
/// least one side (so a rewrite need not match both).
fn apply_side(
    seq: &mut Sequent,
    side: Side,
    f: impl Fn(&Expr) -> Result<Expr, ProofError>,
) -> Result<(), ProofError> {
    match side {
        Side::Lhs => seq.lhs = f(&seq.lhs)?,
        Side::Rhs => seq.rhs = f(&seq.rhs)?,
        Side::Both => {
            let l = f(&seq.lhs);
            let r = f(&seq.rhs);
            match (l, r) {
                (Err(_), Err(e)) => return Err(e),
                (l, r) => {
                    if let Ok(l) = l {
                        seq.lhs = l;
                    }
                    if let Ok(r) = r {
                        seq.rhs = r;
                    }
                }
            }
        }
    }
    Ok(())
}

fn resolve_eq(theory: &Theory, seq: &Sequent, eqref: &EqRef) -> Result<ForallEq, ProofError> {
    match eqref {
        EqRef::Hyp(i) => seq.hyps.get(*i).cloned().ok_or(ProofError::NoHyp(*i)),
        EqRef::Lemma(name) => theory.get(name).cloned().ok_or_else(|| ProofError::NoLemma(name.clone())),
    }
}

// --- induction
//
// Provenance of correctness: for an inductive type, proving the property for
// every constructor (assuming it for the recursive children) proves it for all
// values. The children are universal too, so field vars join the context; the
// hypothesis re-quantifies the goal's *other* variables.

fn do_induct(module: &Module, seq: &Sequent, var: &str) -> Result<Vec<(String, Sequent)>, ProofError> {
    let pos = seq
        .vars
        .iter()
        .position(|p| p.name == var)
        .ok_or_else(|| ProofError::UnknownVar(var.to_string()))?;
    let ty_name = seq.vars[pos].ty.clone();
    let tydef = module.type_def(&ty_name).ok_or_else(|| ProofError::UnknownType(ty_name.clone()))?;
    let rest: Vec<Param> = seq.vars.iter().enumerate().filter(|(i, _)| *i != pos).map(|(_, p)| p.clone()).collect();

    // Names already spoken for, so fresh field vars avoid them.
    let mut used: HashSet<String> = seq.vars.iter().map(|p| p.name.clone()).collect();
    used.extend(free_vars(&seq.lhs));
    used.extend(free_vars(&seq.rhs));
    for h in &seq.hyps {
        used.extend(free_vars(&h.lhs));
        used.extend(free_vars(&h.rhs));
    }

    let mut out = Vec::new();
    for ctor in &tydef.ctors {
        // Fresh variable per constructor field.
        let mut fields: Vec<Param> = Vec::new();
        for fty in &ctor.fields {
            let name = fresh_name(&used);
            used.insert(name.clone());
            fields.push(Param { name, ty: fty.clone() });
        }
        let ctor_expr = Expr::Ctor {
            name: ctor.name.clone(),
            args: fields.iter().map(|f| Expr::Var { name: f.name.clone() }).collect(),
        };
        let ctor_map: HashMap<String, Expr> = HashMap::from([(var.to_string(), ctor_expr)]);

        // Existing hypotheses inherit the substitution (unless they shadow var).
        let mut hyps: Vec<ForallEq> = seq
            .hyps
            .iter()
            .map(|h| {
                if h.vars.iter().any(|p| p.name == var) {
                    h.clone()
                } else {
                    ForallEq { vars: h.vars.clone(), lhs: subst(&h.lhs, &ctor_map), rhs: subst(&h.rhs, &ctor_map) }
                }
            })
            .collect();

        // One induction hypothesis per recursive field.
        for f in &fields {
            if f.ty == ty_name {
                let ih_map: HashMap<String, Expr> =
                    HashMap::from([(var.to_string(), Expr::Var { name: f.name.clone() })]);
                hyps.push(ForallEq {
                    vars: rest.clone(),
                    lhs: subst(&seq.lhs, &ih_map),
                    rhs: subst(&seq.rhs, &ih_map),
                });
            }
        }

        let mut vars = fields;
        vars.extend(rest.clone());
        out.push((
            ctor.name.clone(),
            Sequent { vars, hyps, lhs: subst(&seq.lhs, &ctor_map), rhs: subst(&seq.rhs, &ctor_map) },
        ));
    }
    Ok(out)
}

// --- first-order matching and rewriting
//
// Patterns are applicative (Var / Ctor / Call); a pattern `Match` is required to
// match structurally. The rewrite search does not descend into `match` arm
// bodies, so no binder can capture the replacement.

fn rewrite_first(e: &Expr, pat: &Expr, rep: &Expr, pat_vars: &HashSet<String>) -> Option<Expr> {
    let mut binding = HashMap::new();
    if match_expr(pat, e, pat_vars, &mut binding) {
        return Some(subst(rep, &binding));
    }
    match e {
        Expr::Var { .. } => None,
        Expr::Ctor { name, args } => rewrite_in_args(args, pat, rep, pat_vars)
            .map(|args| Expr::Ctor { name: name.clone(), args }),
        Expr::Call { name, args } => rewrite_in_args(args, pat, rep, pat_vars)
            .map(|args| Expr::Call { name: name.clone(), args }),
        Expr::Match { scrutinee, arms } => rewrite_first(scrutinee, pat, rep, pat_vars)
            .map(|s| Expr::Match { scrutinee: Box::new(s), arms: arms.clone() }),
    }
}

fn rewrite_in_args(args: &[Expr], pat: &Expr, rep: &Expr, pat_vars: &HashSet<String>) -> Option<Vec<Expr>> {
    for (i, a) in args.iter().enumerate() {
        if let Some(new_a) = rewrite_first(a, pat, rep, pat_vars) {
            let mut out = args.to_vec();
            out[i] = new_a;
            return Some(out);
        }
    }
    None
}

fn match_expr(pat: &Expr, term: &Expr, pat_vars: &HashSet<String>, binding: &mut HashMap<String, Expr>) -> bool {
    match pat {
        Expr::Var { name } if pat_vars.contains(name) => match binding.get(name) {
            Some(prev) => prev == term,
            None => {
                binding.insert(name.clone(), term.clone());
                true
            }
        },
        Expr::Var { name } => matches!(term, Expr::Var { name: t } if t == name),
        Expr::Ctor { name, args } => match term {
            Expr::Ctor { name: tn, args: ta } if tn == name && ta.len() == args.len() => {
                args.iter().zip(ta).all(|(p, t)| match_expr(p, t, pat_vars, binding))
            }
            _ => false,
        },
        Expr::Call { name, args } => match term {
            Expr::Call { name: tn, args: ta } if tn == name && ta.len() == args.len() => {
                args.iter().zip(ta).all(|(p, t)| match_expr(p, t, pat_vars, binding))
            }
            _ => false,
        },
        // No pattern variables under binders: require structural equality.
        Expr::Match { .. } => pat == term,
    }
}
