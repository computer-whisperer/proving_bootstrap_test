//! The object language: where DUT functions and unit-test functions live.
//!
//! Deliberate restrictions for the pilot (see `docs/OVERVIEW.md`):
//! - **first-order**: functions are top-level, named; no lambdas as values, so
//!   the only binders are `match` arms. This avoids capture bookkeeping when the
//!   proof layer (M1) manipulates these terms.
//! - **total**: recursion must be structural (see [`check`]); evaluation always
//!   terminates.
//! - **pure**: no effects; equational reasoning is sound.

pub mod ast;
pub mod build;
pub mod builtins;
pub mod check;
pub mod reduce;
pub mod subst;

pub use ast::*;
