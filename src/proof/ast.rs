//! The proof-language AST. Persists as serde + JSON, like the object language.

use serde::{Deserialize, Serialize};

use crate::obj_lang::ast::{Expr, Param};

/// An equation `lhs = rhs` (a premise, or the conclusion of a [`ForallEq`]).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Equation {
    pub lhs: Expr,
    pub rhs: Expr,
}

/// A conditional, universally-quantified equation:
/// `forall vars, premises ⊢ lhs = rhs`. Used for claims, proven lemmas, and
/// induction hypotheses. With `premises` empty it is an ordinary equation.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ForallEq {
    pub vars: Vec<Param>,
    #[serde(default)]
    pub premises: Vec<Equation>,
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

/// Which equation a rewrite uses: an in-scope hypothesis (e.g. an induction
/// hypothesis), one of the goal's own premises, or a previously-proven lemma.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum EqRef {
    Hyp(usize),
    Premise(usize),
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
    /// Guarded δ+ι: reduce, unfolding calls only where they make progress and
    /// keeping stuck calls in `f(args)` form. The usual workhorse.
    Simp { side: Side },
    /// Replace equals by equals using a hypothesis or lemma. `all` rewrites
    /// every occurrence in one pass; otherwise only the first.
    Rewrite { using: EqRef, dir: Dir, side: Side, all: bool },
}

/// A proof tree.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "proof")]
pub enum Proof {
    /// Closes the goal: its two sides are syntactically identical.
    Refl,
    /// Apply `step`, then continue with `rest`.
    Then { step: Step, rest: Box<Proof> },
    /// Induct on `var`, with one sub-proof per constructor of its type.
    Induct { var: String, cases: Vec<Case> },
    /// Case-split on the value of an arbitrary expression `scrutinee` of type
    /// `ty`. Each branch assumes the equation `scrutinee = C(fresh…)` as a
    /// hypothesis (no induction hypothesis). `ty` is named explicitly since
    /// there is no type checker. Used for Bool splits like `eq(a, b)`.
    CaseOn { scrutinee: Expr, ty: String, cases: Vec<Case> },
    /// Rewrite with a *conditional* equation, discharging each of its premises
    /// with a sub-proof (in order). The premises are instantiated by the match
    /// against the goal, then each is proven in the current context. Branches,
    /// so it carries a continuation `rest`. Acts on a single side.
    RewriteWith { using: EqRef, dir: Dir, side: Side, premises: Vec<Proof>, rest: Box<Proof> },
    /// Ex falso: close *any* goal from a contradictory assumption. The cited
    /// equation is `simp`-ed on both sides; if they are distinct constructors the
    /// context is inconsistent, so the goal holds vacuously.
    Absurd { using: EqRef },
}

/// One branch of an [`Proof::Induct`]: the proof for constructor `ctor`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Case {
    pub ctor: String,
    pub proof: Proof,
}
