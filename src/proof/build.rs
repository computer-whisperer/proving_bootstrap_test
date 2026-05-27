//! Ergonomic constructors for proofs and claims (authoring path: Rust helpers,
//! same as the object language).

use crate::obj_lang::ast::{Expr, Param};

use super::ast::*;

pub fn forall_eq(vars: Vec<Param>, lhs: Expr, rhs: Expr) -> ForallEq {
    ForallEq { vars, premises: Vec::new(), lhs, rhs }
}

/// A conditional equation: `forall vars, premises ⊢ lhs = rhs`.
pub fn forall_eq_cond(vars: Vec<Param>, premises: Vec<Equation>, lhs: Expr, rhs: Expr) -> ForallEq {
    ForallEq { vars, premises, lhs, rhs }
}

pub fn eqn(lhs: Expr, rhs: Expr) -> Equation {
    Equation { lhs, rhs }
}

pub fn theorem(name: &str, claim: ForallEq, proof: Proof) -> Theorem {
    Theorem { name: name.into(), claim, proof }
}

// Proof tree
pub fn refl() -> Proof {
    Proof::Refl
}

/// Chain a list of non-branching steps, ending in `tail`.
pub fn steps(seq: Vec<Step>, tail: Proof) -> Proof {
    seq.into_iter().rev().fold(tail, |rest, step| Proof::Then { step, rest: Box::new(rest) })
}

pub fn induct(var: &str, cases: Vec<Case>) -> Proof {
    Proof::Induct { var: var.into(), cases }
}

pub fn case_on(scrutinee: Expr, ty: &str, cases: Vec<Case>) -> Proof {
    Proof::CaseOn { scrutinee, ty: ty.into(), cases }
}

/// Rewrite with a conditional equation; `premises` supplies one sub-proof per
/// premise (in order), each proving the instantiated premise.
pub fn rewrite_with(using: EqRef, dir: Dir, side: Side, premises: Vec<Proof>, rest: Proof) -> Proof {
    Proof::RewriteWith { using, dir, side, with: Vec::new(), premises, rest: Box::new(rest) }
}

/// Like [`rewrite_with`], but pre-instantiates the cited equation's named
/// ∀-variables (∀-elimination) — for "pivot" variables the match can't infer.
pub fn rewrite_with_inst(
    using: EqRef,
    dir: Dir,
    side: Side,
    with: Vec<(&str, Expr)>,
    premises: Vec<Proof>,
    rest: Proof,
) -> Proof {
    let with = with.into_iter().map(|(n, e)| (n.to_string(), e)).collect();
    Proof::RewriteWith { using, dir, side, with, premises, rest: Box::new(rest) }
}

/// Close any goal from a contradictory assumption.
pub fn absurd(using: EqRef) -> Proof {
    Proof::Absurd { using }
}

pub fn case(ctor: &str, proof: Proof) -> Case {
    Case { ctor: ctor.into(), proof }
}

// Steps
pub fn unfold(func: &str, side: Side) -> Step {
    Step::Unfold { func: func.into(), side }
}

pub fn reduce(side: Side) -> Step {
    Step::Reduce { side }
}

pub fn simp(side: Side) -> Step {
    Step::Simp { side }
}

pub fn rewrite(using: EqRef, dir: Dir, side: Side) -> Step {
    Step::Rewrite { using, dir, side, all: false, with: Vec::new() }
}

pub fn rewrite_all(using: EqRef, dir: Dir, side: Side) -> Step {
    Step::Rewrite { using, dir, side, all: true, with: Vec::new() }
}

/// Plain rewrite that pre-instantiates the cited equation's named ∀-variables.
pub fn rewrite_inst(using: EqRef, dir: Dir, side: Side, with: Vec<(&str, Expr)>) -> Step {
    let with = with.into_iter().map(|(n, e)| (n.to_string(), e)).collect();
    Step::Rewrite { using, dir, side, all: false, with }
}

// Equation references
pub fn hyp(i: usize) -> EqRef {
    EqRef::Hyp(i)
}

pub fn premise(i: usize) -> EqRef {
    EqRef::Premise(i)
}

pub fn lemma(name: &str) -> EqRef {
    EqRef::Lemma(name.into())
}
