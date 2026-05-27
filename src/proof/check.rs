//! The trusted kernel. Everything else can be wrong; if this accepts a proof,
//! the claim holds under the object language's semantics.

use std::collections::{HashMap, HashSet};

use crate::obj_lang::ast::*;
use crate::obj_lang::reduce::{reduce_iota, simp, unfold_one};
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
    /// `Premise(i)` out of range.
    NoPremise(usize),
    /// A plain `Rewrite` was used with a conditional equation; use `RewriteWith`.
    RewriteNeedsPremises,
    /// `RewriteWith` given the wrong number of premise sub-proofs.
    PremiseCountMismatch { expected: usize, got: usize },
    /// `RewriteWith` on `Side::Both` (a single side is required).
    RewriteWithBothSides,
    /// `Absurd` with a conditional/quantified equation (needs a ground equation).
    AbsurdNeedsGroundEq,
    /// `Absurd` whose cited equation does not reduce to a constructor clash.
    NotAbsurd { lhs: Box<Expr>, rhs: Box<Expr> },
}

/// A proof obligation: prove `premises ⊢ lhs = rhs` for all `vars`, with `hyps`
/// available. `premises` are the goal's own assumptions (usable via
/// `EqRef::Premise`) and are what `induct` carries into the induction hypothesis.
#[derive(Clone, Debug)]
pub struct Sequent {
    pub vars: Vec<Param>,
    pub hyps: Vec<ForallEq>,
    pub premises: Vec<Equation>,
    pub lhs: Expr,
    pub rhs: Expr,
}

impl std::fmt::Display for Sequent {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let vars = self.vars.iter().map(|p| format!("{}:{}", p.name, p.ty)).collect::<Vec<_>>().join(", ");
        writeln!(f, "vars: {vars}")?;
        for (i, p) in self.premises.iter().enumerate() {
            writeln!(f, "  premise[{i}]: {} = {}", p.lhs, p.rhs)?;
        }
        for (i, h) in self.hyps.iter().enumerate() {
            let hv = h.vars.iter().map(|p| p.name.clone()).collect::<Vec<_>>().join(", ");
            let q = if hv.is_empty() { String::new() } else { format!("forall {hv}, ") };
            let prem = if h.premises.is_empty() {
                String::new()
            } else {
                let ps = h.premises.iter().map(|e| format!("{} = {}", e.lhs, e.rhs)).collect::<Vec<_>>().join(", ");
                format!("[{ps}] => ")
            };
            writeln!(f, "  hyp[{i}]: {q}{prem}{} = {}", h.lhs, h.rhs)?;
        }
        write!(f, "  goal: {} = {}", self.lhs, self.rhs)
    }
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
    /// Names of lemmas with no premises (usable via a plain `Rewrite`).
    pub fn unconditional_lemma_names(&self) -> Vec<String> {
        self.lemmas.iter().filter(|(_, eq)| eq.premises.is_empty()).map(|(n, _)| n.clone()).collect()
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
        premises: thm.claim.premises.clone(),
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
            check_branches(module, theory, subgoals, cases)
        }
        Proof::CaseOn { scrutinee, ty, cases } => {
            let subgoals = do_case_on(module, seq, scrutinee, ty)?;
            check_branches(module, theory, subgoals, cases)
        }
        Proof::RewriteWith { using, dir, side, premises, rest } => {
            let next = apply_rewrite_with(module, theory, seq, using, *dir, *side, premises)?;
            check_sequent(module, theory, &next, rest)
        }
        Proof::Absurd { using } => {
            let eq = resolve_eq(theory, seq, using)?;
            if !eq.vars.is_empty() || !eq.premises.is_empty() {
                return Err(ProofError::AbsurdNeedsGroundEq);
            }
            // The assumption eq.lhs = eq.rhs holds in this branch. If it reduces
            // to distinct constructors it is false, so the branch is vacuous.
            let l = simp(module, &eq.lhs);
            let r = simp(module, &eq.rhs);
            if head_clash(&l, &r) {
                Ok(())
            } else {
                Err(ProofError::NotAbsurd { lhs: Box::new(l), rhs: Box::new(r) })
            }
        }
    }
}

/// Two terms whose heads are different constructors can never be equal.
fn head_clash(a: &Expr, b: &Expr) -> bool {
    matches!((a, b), (Expr::Ctor { name: x, .. }, Expr::Ctor { name: y, .. }) if x != y)
}

/// Rewrite with a conditional equation: match it against the chosen side, prove
/// each instantiated premise with the supplied sub-proof, then rewrite.
fn apply_rewrite_with(
    module: &Module,
    theory: &Theory,
    seq: &Sequent,
    using: &EqRef,
    dir: Dir,
    side: Side,
    premise_proofs: &[Proof],
) -> Result<Sequent, ProofError> {
    let eq = resolve_eq(theory, seq, using)?;
    if premise_proofs.len() != eq.premises.len() {
        return Err(ProofError::PremiseCountMismatch { expected: eq.premises.len(), got: premise_proofs.len() });
    }
    let (pat, rep) = match dir {
        Dir::Lr => (&eq.lhs, &eq.rhs),
        Dir::Rl => (&eq.rhs, &eq.lhs),
    };
    let pat_vars: HashSet<String> = eq.vars.iter().map(|p| p.name.clone()).collect();

    let target = match side {
        Side::Lhs => &seq.lhs,
        Side::Rhs => &seq.rhs,
        Side::Both => return Err(ProofError::RewriteWithBothSides),
    };
    let (rewritten, binding) =
        rewrite_first_capture(target, pat, rep, &pat_vars).ok_or(ProofError::RewriteNoMatch)?;

    // Each premise, instantiated by the match, must be proven in this context.
    for (prem, proof) in eq.premises.iter().zip(premise_proofs) {
        let subgoal = Sequent {
            vars: seq.vars.clone(),
            hyps: seq.hyps.clone(),
            premises: seq.premises.clone(),
            lhs: subst(&prem.lhs, &binding),
            rhs: subst(&prem.rhs, &binding),
        };
        check_sequent(module, theory, &subgoal, proof)?;
    }

    let mut next = seq.clone();
    match side {
        Side::Lhs => next.lhs = rewritten,
        Side::Rhs => next.rhs = rewritten,
        Side::Both => unreachable!(),
    }
    Ok(next)
}

fn check_branches(
    module: &Module,
    theory: &Theory,
    subgoals: Vec<(String, Sequent)>,
    cases: &[Case],
) -> Result<(), ProofError> {
    for (ctor, subgoal) in subgoals {
        let case = cases
            .iter()
            .find(|c| c.ctor == ctor)
            .ok_or(ProofError::MissingCase { ctor: ctor.clone() })?;
        check_sequent(module, theory, &subgoal, &case.proof)?;
    }
    Ok(())
}

/// Run a list of non-branching steps against a sequent, returning the resulting
/// goal. For inspecting intermediate states while authoring proofs.
pub fn run_steps(module: &Module, theory: &Theory, seq: &Sequent, steps: &[Step]) -> Result<Sequent, ProofError> {
    let mut s = seq.clone();
    for step in steps {
        s = apply_step(module, theory, &s, step)?;
    }
    Ok(s)
}

// --- steps

pub fn apply_step(module: &Module, theory: &Theory, seq: &Sequent, step: &Step) -> Result<Sequent, ProofError> {
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
        Step::Simp { side } => {
            apply_side(&mut next, *side, |e| Ok(simp(module, e)))?;
        }
        Step::Rewrite { using, dir, side, all } => {
            let eq = resolve_eq(theory, seq, using)?;
            if !eq.premises.is_empty() {
                return Err(ProofError::RewriteNeedsPremises);
            }
            let (pat, rep) = match dir {
                Dir::Lr => (&eq.lhs, &eq.rhs),
                Dir::Rl => (&eq.rhs, &eq.lhs),
            };
            let pat_vars: HashSet<String> = eq.vars.iter().map(|p| p.name.clone()).collect();
            apply_side(&mut next, *side, |e| {
                if *all {
                    let (out, changed) = rewrite_all_pass(e, pat, rep, &pat_vars);
                    if changed { Ok(out) } else { Err(ProofError::RewriteNoMatch) }
                } else {
                    rewrite_first(e, pat, rep, &pat_vars).ok_or(ProofError::RewriteNoMatch)
                }
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
        EqRef::Premise(i) => seq
            .premises
            .get(*i)
            .map(|e| ForallEq { vars: Vec::new(), premises: Vec::new(), lhs: e.lhs.clone(), rhs: e.rhs.clone() })
            .ok_or(ProofError::NoPremise(*i)),
        EqRef::Lemma(name) => theory.get(name).cloned().ok_or_else(|| ProofError::NoLemma(name.clone())),
    }
}

fn subst_eq(e: &Equation, map: &HashMap<String, Expr>) -> Equation {
    Equation { lhs: subst(&e.lhs, map), rhs: subst(&e.rhs, map) }
}

// --- induction
//
// Provenance of correctness: for an inductive type, proving the property for
// every constructor (assuming it for the recursive children) proves it for all
// values. The children are universal too, so field vars join the context; the
// hypothesis re-quantifies the goal's *other* variables. The goal's premises
// ride along: substituted in each subgoal, and carried (conditional) into the IH.

pub fn do_induct(module: &Module, seq: &Sequent, var: &str) -> Result<Vec<(String, Sequent)>, ProofError> {
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
    for p in &seq.premises {
        used.extend(free_vars(&p.lhs));
        used.extend(free_vars(&p.rhs));
    }
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
                    ForallEq {
                        vars: h.vars.clone(),
                        premises: h.premises.iter().map(|e| subst_eq(e, &ctor_map)).collect(),
                        lhs: subst(&h.lhs, &ctor_map),
                        rhs: subst(&h.rhs, &ctor_map),
                    }
                }
            })
            .collect();

        // One induction hypothesis per recursive field — itself conditional if
        // the goal had premises.
        for f in &fields {
            if f.ty == ty_name {
                let ih_map: HashMap<String, Expr> =
                    HashMap::from([(var.to_string(), Expr::Var { name: f.name.clone() })]);
                hyps.push(ForallEq {
                    vars: rest.clone(),
                    premises: seq.premises.iter().map(|e| subst_eq(e, &ih_map)).collect(),
                    lhs: subst(&seq.lhs, &ih_map),
                    rhs: subst(&seq.rhs, &ih_map),
                });
            }
        }

        let mut vars = fields;
        vars.extend(rest.clone());
        out.push((
            ctor.name.clone(),
            Sequent {
                vars,
                hyps,
                premises: seq.premises.iter().map(|e| subst_eq(e, &ctor_map)).collect(),
                lhs: subst(&seq.lhs, &ctor_map),
                rhs: subst(&seq.rhs, &ctor_map),
            },
        ));
    }
    Ok(out)
}

// --- case analysis on an expression
//
// Splitting on the constructors of `scrutinee`'s type is exhaustive (every value
// is some constructor), so assuming `scrutinee = C(fresh…)` in each branch is
// sound. Unlike induction there is no hypothesis about subterms, and the goal is
// not substituted — the branch's equation lets the proof rewrite the scrutinee.

pub fn do_case_on(module: &Module, seq: &Sequent, scrutinee: &Expr, ty: &str) -> Result<Vec<(String, Sequent)>, ProofError> {
    let tydef = module.type_def(ty).ok_or_else(|| ProofError::UnknownType(ty.to_string()))?;

    let mut used: HashSet<String> = seq.vars.iter().map(|p| p.name.clone()).collect();
    used.extend(free_vars(&seq.lhs));
    used.extend(free_vars(&seq.rhs));
    used.extend(free_vars(scrutinee));
    for h in &seq.hyps {
        used.extend(free_vars(&h.lhs));
        used.extend(free_vars(&h.rhs));
    }

    let mut out = Vec::new();
    for ctor in &tydef.ctors {
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
        let mut vars = seq.vars.clone();
        vars.extend(fields);
        let mut hyps = seq.hyps.clone();
        // scrutinee = C(fresh…), usable as a left-to-right rewrite.
        hyps.push(ForallEq { vars: Vec::new(), premises: Vec::new(), lhs: scrutinee.clone(), rhs: ctor_expr });
        out.push((
            ctor.name.clone(),
            Sequent { vars, hyps, premises: seq.premises.clone(), lhs: seq.lhs.clone(), rhs: seq.rhs.clone() },
        ));
    }
    Ok(out)
}

// --- first-order matching and rewriting
//
// Patterns are applicative (Var / Ctor / Call); a pattern `Match` is required to
// match structurally. The rewrite search does not descend into `match` arm
// bodies, so no binder can capture the replacement.

/// Like `rewrite_first`, but also returns the match binding (needed to
/// instantiate a conditional equation's premises).
fn rewrite_first_capture(
    e: &Expr,
    pat: &Expr,
    rep: &Expr,
    pat_vars: &HashSet<String>,
) -> Option<(Expr, HashMap<String, Expr>)> {
    let mut binding = HashMap::new();
    if match_expr(pat, e, pat_vars, &mut binding) {
        let out = subst(rep, &binding);
        return Some((out, binding));
    }
    match e {
        Expr::Var { .. } => None,
        Expr::Ctor { name, args } => rewrite_capture_in_args(args, pat, rep, pat_vars)
            .map(|(args, b)| (Expr::Ctor { name: name.clone(), args }, b)),
        Expr::Call { name, args } => rewrite_capture_in_args(args, pat, rep, pat_vars)
            .map(|(args, b)| (Expr::Call { name: name.clone(), args }, b)),
        Expr::Match { scrutinee, arms } => rewrite_first_capture(scrutinee, pat, rep, pat_vars)
            .map(|(s, b)| (Expr::Match { scrutinee: Box::new(s), arms: arms.clone() }, b)),
    }
}

fn rewrite_capture_in_args(
    args: &[Expr],
    pat: &Expr,
    rep: &Expr,
    pat_vars: &HashSet<String>,
) -> Option<(Vec<Expr>, HashMap<String, Expr>)> {
    for (i, a) in args.iter().enumerate() {
        if let Some((new_a, b)) = rewrite_first_capture(a, pat, rep, pat_vars) {
            let mut out = args.to_vec();
            out[i] = new_a;
            return Some((out, b));
        }
    }
    None
}

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

/// Replace every (non-nested) occurrence in one top-down pass. Does not descend
/// into a replacement, so it terminates even if `rep` re-contains `pat`.
fn rewrite_all_pass(e: &Expr, pat: &Expr, rep: &Expr, pat_vars: &HashSet<String>) -> (Expr, bool) {
    let mut binding = HashMap::new();
    if match_expr(pat, e, pat_vars, &mut binding) {
        return (subst(rep, &binding), true);
    }
    match e {
        Expr::Var { .. } => (e.clone(), false),
        Expr::Ctor { name, args } => {
            let (args, changed) = rewrite_all_in_args(args, pat, rep, pat_vars);
            (Expr::Ctor { name: name.clone(), args }, changed)
        }
        Expr::Call { name, args } => {
            let (args, changed) = rewrite_all_in_args(args, pat, rep, pat_vars);
            (Expr::Call { name: name.clone(), args }, changed)
        }
        Expr::Match { scrutinee, arms } => {
            let (s, changed) = rewrite_all_pass(scrutinee, pat, rep, pat_vars);
            (Expr::Match { scrutinee: Box::new(s), arms: arms.clone() }, changed)
        }
    }
}

fn rewrite_all_in_args(args: &[Expr], pat: &Expr, rep: &Expr, pat_vars: &HashSet<String>) -> (Vec<Expr>, bool) {
    let mut changed = false;
    let out = args
        .iter()
        .map(|a| {
            let (a, c) = rewrite_all_pass(a, pat, rep, pat_vars);
            changed |= c;
            a
        })
        .collect();
    (out, changed)
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
