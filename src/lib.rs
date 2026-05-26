//! Provable-software pilot. See `docs/OVERVIEW.md` for the thesis and
//! `docs/ROADMAP.md` for the staged plan.
//!
//! M0 (this slice) is the object language: a total, pure, first-order
//! functional core, its built-in inductive types, a structural-recursion
//! check, and the reduction engine that is the single source of truth for the
//! language's semantics.

pub mod obj_lang;
pub mod proof;
