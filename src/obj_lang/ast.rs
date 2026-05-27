//! The object-language AST — the "crown jewel" data structure (OVERVIEW.md
//! decision 5). Everything persists as serde + JSON; this type is what the
//! proof layer will inspect, unfold, and rewrite, so it is kept small and flat.

use std::fmt;

use serde::{Deserialize, Serialize};

/// A reference to a type. The pilot is monomorphic, so a type is just its name
/// (e.g. `"Nat"`, `"List"`).
pub type TypeName = String;

/// A whole program: the inductive types in scope plus the function definitions.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Module {
    pub types: Vec<TypeDef>,
    pub fns: Vec<FnDef>,
}

impl Module {
    pub fn fn_def(&self, name: &str) -> Option<&FnDef> {
        self.fns.iter().find(|f| f.name == name)
    }

    pub fn type_def(&self, name: &str) -> Option<&TypeDef> {
        self.types.iter().find(|t| t.name == name)
    }

    /// Constructor names are unique across all types in the pilot, so a global
    /// lookup is enough.
    pub fn ctor_def(&self, name: &str) -> Option<&CtorDef> {
        self.types.iter().flat_map(|t| &t.ctors).find(|c| c.name == name)
    }
}

/// An inductive type: a name and its constructors. A constructor field whose
/// type is the enclosing type makes the type recursive (`S(Nat)`, `Cons(_, List)`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TypeDef {
    pub name: TypeName,
    pub ctors: Vec<CtorDef>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CtorDef {
    pub name: String,
    pub fields: Vec<TypeName>,
}

/// A top-level first-order function definition.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FnDef {
    pub name: String,
    pub params: Vec<Param>,
    pub ret: TypeName,
    pub body: Expr,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Param {
    pub name: String,
    pub ty: TypeName,
}

/// Expressions. The only binders are `match` arms.
///
/// JSON is internally tagged on `expr` for readability, e.g.
/// `{"expr":"Var","name":"xs"}`.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(tag = "expr")]
pub enum Expr {
    /// A variable: a function parameter or a `match`-bound field.
    Var { name: String },
    /// Constructor application, e.g. `S(e)`, `Cons(h, t)`, `True`.
    Ctor { name: String, args: Vec<Expr> },
    /// A call to a top-level function by name.
    Call { name: String, args: Vec<Expr> },
    /// Case analysis on the head constructor of a value.
    Match { scrutinee: Box<Expr>, arms: Vec<Arm> },
}

/// One arm of a `match`: on constructor `ctor`, bind its fields to `binds`
/// (positionally) and evaluate `body`.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Arm {
    pub ctor: String,
    pub binds: Vec<String>,
    pub body: Expr,
}

/// Readable rendering of terms, for inspecting goals while authoring proofs.
/// (Constructors and calls render identically as `name(args)`; context tells
/// them apart.)
impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expr::Var { name } => write!(f, "{name}"),
            Expr::Ctor { name, args } | Expr::Call { name, args } => {
                if args.is_empty() {
                    write!(f, "{name}")
                } else {
                    let inner = args.iter().map(|a| a.to_string()).collect::<Vec<_>>().join(", ");
                    write!(f, "{name}({inner})")
                }
            }
            Expr::Match { scrutinee, arms } => {
                let arms = arms
                    .iter()
                    .map(|a| {
                        let pat = if a.binds.is_empty() {
                            a.ctor.clone()
                        } else {
                            format!("{}({})", a.ctor, a.binds.join(", "))
                        };
                        format!("{pat} => {}", a.body)
                    })
                    .collect::<Vec<_>>()
                    .join("; ");
                write!(f, "match {scrutinee} {{ {arms} }}")
            }
        }
    }
}
