//! Ergonomic constructors for building object-language terms in Rust (the
//! authoring path chosen for the pilot — no surface parser). Terms still
//! round-trip through serde + JSON.

use super::ast::*;

pub fn var(name: &str) -> Expr {
    Expr::Var { name: name.into() }
}

pub fn ctor(name: &str, args: Vec<Expr>) -> Expr {
    Expr::Ctor { name: name.into(), args }
}

pub fn call(name: &str, args: Vec<Expr>) -> Expr {
    Expr::Call { name: name.into(), args }
}

pub fn match_(scrutinee: Expr, arms: Vec<Arm>) -> Expr {
    Expr::Match { scrutinee: Box::new(scrutinee), arms }
}

pub fn arm(ctor: &str, binds: &[&str], body: Expr) -> Arm {
    Arm { ctor: ctor.into(), binds: binds.iter().map(|b| b.to_string()).collect(), body }
}

// Bool
pub fn tru() -> Expr {
    ctor("True", vec![])
}
pub fn fls() -> Expr {
    ctor("False", vec![])
}

// Nat
pub fn z() -> Expr {
    ctor("Z", vec![])
}
pub fn s(e: Expr) -> Expr {
    ctor("S", vec![e])
}
/// The Peano numeral for `k`: `S^k(Z)`.
pub fn nat(k: u64) -> Expr {
    (0..k).fold(z(), |acc, _| s(acc))
}

// List
pub fn nil() -> Expr {
    ctor("Nil", vec![])
}
pub fn cons(h: Expr, t: Expr) -> Expr {
    ctor("Cons", vec![h, t])
}
/// A `List` literal: `[a, b, c]` becomes `Cons(a, Cons(b, Cons(c, Nil)))`.
pub fn list(items: Vec<Expr>) -> Expr {
    items.into_iter().rev().fold(nil(), |tail, head| cons(head, tail))
}

// Definitions
pub fn param(name: &str, ty: &str) -> Param {
    Param { name: name.into(), ty: ty.into() }
}
pub fn fndef(name: &str, params: Vec<Param>, ret: &str, body: Expr) -> FnDef {
    FnDef { name: name.into(), params, ret: ret.into(), body }
}
