//! The proof language and its trusted checker (the kernel).
//!
//! A claim is a universally-quantified equation `forall vars, lhs = rhs`
//! (OVERVIEW.md "minimal logic"). A unit test `forall x, t(x) = true` is the
//! special case `rhs = True`. A proof is a small tree of inference steps; the
//! kernel ([`check`]) replays it and answers whether it closes the claim.
//!
//! Soundness rests on: ι/δ reduction is the object language's own semantics
//! (via [`crate::obj_lang::reduce`]), `rewrite` replaces equals by equals, and
//! `induct` is the structural induction principle of an inductive type — valid
//! because the object language is total (see `obj_lang::check`).

pub mod ast;
pub mod build;
pub mod check;

pub use ast::*;
