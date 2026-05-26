//! Built-in inductive types for the pilot: `Bool`, `Nat`, and a monomorphic
//! `List` of `Nat`. Defined through the same general [`TypeDef`] mechanism the
//! object language uses for any inductive type — there is nothing special about
//! them beyond being pre-populated.

use super::ast::*;

pub fn bool_ty() -> TypeDef {
    TypeDef {
        name: "Bool".into(),
        ctors: vec![
            CtorDef { name: "True".into(), fields: vec![] },
            CtorDef { name: "False".into(), fields: vec![] },
        ],
    }
}

pub fn nat_ty() -> TypeDef {
    TypeDef {
        name: "Nat".into(),
        ctors: vec![
            CtorDef { name: "Z".into(), fields: vec![] },
            CtorDef { name: "S".into(), fields: vec!["Nat".into()] },
        ],
    }
}

/// Monomorphic list of `Nat` (the pilot avoids polymorphism; element type is
/// fixed). Proofs about list shape do not depend on the element type.
pub fn list_ty() -> TypeDef {
    TypeDef {
        name: "List".into(),
        ctors: vec![
            CtorDef { name: "Nil".into(), fields: vec![] },
            CtorDef { name: "Cons".into(), fields: vec!["Nat".into(), "List".into()] },
        ],
    }
}

/// A module pre-loaded with the built-in types and no functions.
pub fn prelude() -> Module {
    Module { types: vec![bool_ty(), nat_ty(), list_ty()], fns: vec![] }
}
