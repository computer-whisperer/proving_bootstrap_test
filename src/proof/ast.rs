//! The proof-language AST. Persists as serde + JSON, like the object language.

use serde::{Deserialize, Serialize};

use crate::obj_lang::ast::{Expr, Param};

/// A universally-quantified equation: `forall vars, lhs = rhs`. Used for claims,
/// for proven lemmas, and for induction hypotheses.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ForallEq {
    pub vars: Vec<Param>,
    pub lhs: Expr,
    pub rhs: Expr,
}

/// A named theorem: a claim and the proof that closes it. Once checked, it can
/// be cited as a lemma by later theorems.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Theorem {
    pub name: String,
    pub claim: ForallEq,
    pub proof: Proof,
}

/// Which side(s) of the goal equation a step acts on.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Side {
    Lhs,
    Rhs,
    Both,
}

/// Rewrite direction: `Lr` replaces matches of the equation's lhs with its rhs;
/// `Rl` is the reverse.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Dir {
    Lr,
    Rl,
}

/// Which equation a `Rewrite` uses: an in-scope hypothesis (e.g. an induction
/// hypothesis, by index) or a previously-proven lemma (by name).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum EqRef {
    Hyp(usize),
    Lemma(String),
}

/// A non-branching inference step. Each is individually sound and terminating.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "step")]
pub enum Step {
    /// δ: unfold one layer of calls to `func`.
    Unfold { func: String, side: Side },
    /// ι: fire all constructor-headed matches.
    Reduce { side: Side },
    /// Replace equals by equals using a hypothesis or lemma.
    Rewrite { using: EqRef, dir: Dir, side: Side },
}

/// A proof tree.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "proof")]
pub enum Proof {
    /// Closes the goal: its two sides are syntactically identical.
    Refl,
    /// Apply `step`, then continue with `rest`.
    Then { step: Step, rest: Box<Proof> },
    /// The only branching step: induct on `var`, with one sub-proof per
    /// constructor of its type.
    Induct { var: String, cases: Vec<Case> },
}

/// One branch of an [`Proof::Induct`]: the proof for constructor `ctor`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Case {
    pub ctor: String,
    pub proof: Proof,
}
