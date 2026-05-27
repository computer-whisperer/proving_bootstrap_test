//! A small, **untrusted** proof search. It explores combinations of the kernel's
//! own steps (`simp`, `rewrite`, `induct`, `case_on`, `absurd`) by bounded DFS
//! and returns a `Proof` if it finds one. Nothing here is trusted: the result is
//! an ordinary `Proof` that `check_theorem` re-validates. A found proof is
//! serde-serializable, so it doubles as a cache entry (search once, check
//! forever).
//!
//! This is the first piece of the "automation layer": today the strategy is
//! blind-ish search; an LLM (or smarter tactic) would slot in here later. The
//! kernel never changes.

use crate::obj_lang::ast::*;
use crate::obj_lang::reduce::simp;

use super::ast::*;
use super::check::{apply_step, do_case_on, do_induct, Sequent, Theory};

/// Search budget. `depth` bounds branching (induct/case nesting + step chains);
/// `nodes` is a global ceiling so a bad branch can't run away.
#[derive(Clone, Copy, Debug)]
pub struct Limits {
    pub depth: usize,
    pub nodes: usize,
}

impl Default for Limits {
    fn default() -> Self {
        Limits { depth: 6, nodes: 400_000 }
    }
}

/// Try to find a proof of `claim`. Returns a kernel-checkable `Proof`.
pub fn find_proof(module: &Module, theory: &Theory, claim: &ForallEq, limits: Limits) -> Option<Proof> {
    let seq = Sequent {
        vars: claim.vars.clone(),
        hyps: Vec::new(),
        premises: claim.premises.clone(),
        lhs: claim.lhs.clone(),
        rhs: claim.rhs.clone(),
    };
    find_from_sequent(module, theory, &seq, limits)
}

/// Search from an arbitrary goal. Lets a human supply the high-level structure
/// (the inductions / case splits) and have search discharge the leaves — the
/// usual division of labor when blind search on the whole theorem explodes.
///
/// Uses **iterative deepening**: try to find a proof of depth 1, then 2, … up to
/// `limits.depth`. This finds the shallowest proof and avoids plain DFS diving
/// down a deep wrong path. Each depth gets a fresh node budget.
pub fn find_from_sequent(module: &Module, theory: &Theory, seq: &Sequent, limits: Limits) -> Option<Proof> {
    for d in 1..=limits.depth {
        let mut budget = limits.nodes;
        if let Some(p) = search(module, theory, seq, d, &mut budget) {
            return Some(p);
        }
    }
    None
}

fn search(module: &Module, theory: &Theory, seq: &Sequent, depth: usize, budget: &mut usize) -> Option<Proof> {
    if *budget == 0 {
        return None;
    }
    *budget -= 1;

    // Terminal: reflexivity.
    if seq.lhs == seq.rhs {
        return Some(Proof::Refl);
    }
    // Terminal: a contradictory ground assumption closes any goal.
    if let Some(eqref) = contradictory_assumption(module, seq) {
        return Some(Proof::Absurd { using: eqref });
    }
    if depth == 0 {
        return None;
    }

    // Non-branching steps, best-first: normalize, then rewrite with the in-scope
    // equations (hyps/IH, then premises, then lemmas).
    for step in candidate_steps(seq, theory) {
        if let Ok(next) = apply_step(module, theory, seq, &step)
            && goal_changed(seq, &next)
            && let Some(rest) = search(module, theory, &next, depth - 1, budget)
        {
            return Some(Proof::Then { step, rest: Box::new(rest) });
        }
    }

    // Branching: induction on an inductive variable.
    for var in inductive_vars(module, seq) {
        if let Ok(subgoals) = do_induct(module, seq, &var)
            && let Some(cases) = search_cases(module, theory, &subgoals, depth - 1, budget)
        {
            return Some(Proof::Induct { var, cases });
        }
    }

    // Branching: case-split on a Bool-valued subexpression.
    for scrut in bool_subexprs(module, seq) {
        if let Ok(subgoals) = do_case_on(module, seq, &scrut, "Bool")
            && let Some(cases) = search_cases(module, theory, &subgoals, depth - 1, budget)
        {
            return Some(Proof::CaseOn { scrutinee: scrut, ty: "Bool".into(), cases });
        }
    }

    None
}

fn search_cases(
    module: &Module,
    theory: &Theory,
    subgoals: &[(String, Sequent)],
    depth: usize,
    budget: &mut usize,
) -> Option<Vec<Case>> {
    let mut cases = Vec::with_capacity(subgoals.len());
    for (ctor, sub) in subgoals {
        let proof = search(module, theory, sub, depth, budget)?;
        cases.push(Case { ctor: ctor.clone(), proof });
    }
    Some(cases)
}

/// Ordered candidate non-branching steps. `simp` first (almost always right),
/// then rewrites with hypotheses (the induction hypothesis lives here), the
/// goal's premises, and finally unconditional theory lemmas.
fn candidate_steps(seq: &Sequent, theory: &Theory) -> Vec<Step> {
    let mut steps = vec![Step::Simp { side: Side::Both }];

    let push_rewrites = |using: EqRef, steps: &mut Vec<Step>| {
        for dir in [Dir::Lr, Dir::Rl] {
            for all in [false, true] {
                steps.push(Step::Rewrite { using: using.clone(), dir, side: Side::Both, all });
            }
        }
    };

    for i in 0..seq.hyps.len() {
        push_rewrites(EqRef::Hyp(i), &mut steps);
    }
    for i in 0..seq.premises.len() {
        push_rewrites(EqRef::Premise(i), &mut steps);
    }
    for name in theory.unconditional_lemma_names() {
        push_rewrites(EqRef::Lemma(name), &mut steps);
    }
    steps
}

/// A ground (no vars, no premises) assumption that `simp`s to a constructor
/// clash, if any — usable for ex-falso.
fn contradictory_assumption(module: &Module, seq: &Sequent) -> Option<EqRef> {
    for (i, p) in seq.premises.iter().enumerate() {
        if clashes(module, &p.lhs, &p.rhs) {
            return Some(EqRef::Premise(i));
        }
    }
    for (i, h) in seq.hyps.iter().enumerate() {
        if h.vars.is_empty() && h.premises.is_empty() && clashes(module, &h.lhs, &h.rhs) {
            return Some(EqRef::Hyp(i));
        }
    }
    None
}

fn clashes(module: &Module, a: &Expr, b: &Expr) -> bool {
    matches!(
        (simp(module, a), simp(module, b)),
        (Expr::Ctor { name: x, .. }, Expr::Ctor { name: y, .. }) if x != y
    )
}

fn goal_changed(a: &Sequent, b: &Sequent) -> bool {
    a.lhs != b.lhs || a.rhs != b.rhs
}

fn inductive_vars(module: &Module, seq: &Sequent) -> Vec<String> {
    seq.vars
        .iter()
        .filter(|p| module.type_def(&p.ty).is_some())
        .map(|p| p.name.clone())
        .collect()
}

/// Bool-valued `Call` subexpressions of the goal — candidates for `case_on`.
fn bool_subexprs(module: &Module, seq: &Sequent) -> Vec<Expr> {
    let mut out = Vec::new();
    collect_bool_calls(module, &seq.lhs, &mut out);
    collect_bool_calls(module, &seq.rhs, &mut out);
    out
}

fn collect_bool_calls(module: &Module, e: &Expr, out: &mut Vec<Expr>) {
    match e {
        Expr::Var { .. } => {}
        Expr::Ctor { args, .. } => {
            for a in args {
                collect_bool_calls(module, a, out);
            }
        }
        Expr::Call { name, args } => {
            if module.fn_def(name).map(|f| f.ret == "Bool").unwrap_or(false) && !out.contains(e) {
                out.push(e.clone());
            }
            for a in args {
                collect_bool_calls(module, a, out);
            }
        }
        Expr::Match { scrutinee, arms } => {
            collect_bool_calls(module, scrutinee, out);
            for arm in arms {
                collect_bool_calls(module, &arm.body, out);
            }
        }
    }
}
