//! Ergonomic constructors for proofs and claims (authoring path: Rust helpers,
//! same as the object language).

use crate::obj_lang::ast::{Expr, Param};

use super::ast::*;

pub fn forall_eq(vars: Vec<Param>, lhs: Expr, rhs: Expr) -> ForallEq {
    ForallEq { vars, lhs, rhs }
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
    Step::Rewrite { using, dir, side }
}

// Equation references
pub fn hyp(i: usize) -> EqRef {
    EqRef::Hyp(i)
}

pub fn lemma(name: &str) -> EqRef {
    EqRef::Lemma(name.into())
}
