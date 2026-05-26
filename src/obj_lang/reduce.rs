//! The reduction engine — the single source of truth for the object language's
//! operational semantics (OVERVIEW.md "Trust"). The interpreter goes through
//! [`normalize`]; the proof kernel (M1) will too, so that what is *proven*
//! about a term matches how it actually *runs*.

use std::collections::HashMap;

use super::ast::*;
use super::subst::subst;

/// A substitution from variable name to its (already-normalized) binding.
pub type Env = HashMap<String, Expr>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReduceError {
    UnknownFn(String),
    /// A `match` scrutinee reduced to a constructor with no matching arm.
    NoMatchingArm { ctor: String },
    ArityMismatch { what: String, expected: usize, got: usize },
}

/// Normalize `expr` under `env`.
///
/// - For a **closed** term this is full evaluation; the result is built only
///   from `Ctor` nodes (a value).
/// - For an **open** term it reduces as far as possible. A `Match` whose
///   scrutinee is stuck (a free variable, not a constructor) is left as a
///   residual `Match`. M0 does not yet normalize *under* an arm's binders; M1
///   will extend this for reasoning beneath a `forall` (see ROADMAP).
///
/// Termination on closed terms rests on the structural-recursion check
/// ([`super::check`]): each recursive unfold either consumes a concrete
/// constructor or gets stuck on a free variable, so the recursion bottoms out.
pub fn normalize(module: &Module, env: &Env, expr: &Expr) -> Result<Expr, ReduceError> {
    match expr {
        // A bound variable resolves to its binding; a free one is itself.
        Expr::Var { name } => Ok(env.get(name).cloned().unwrap_or_else(|| expr.clone())),

        // Constructors are the values; normalize their arguments.
        Expr::Ctor { name, args } => {
            let args = args
                .iter()
                .map(|a| normalize(module, env, a))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Expr::Ctor { name: name.clone(), args })
        }

        // A call unfolds: normalize the arguments, bind the parameters, then
        // normalize the body. Functions are first-order, so the body's scope is
        // exactly its parameters (no closure capture).
        Expr::Call { name, args } => {
            let args = args
                .iter()
                .map(|a| normalize(module, env, a))
                .collect::<Result<Vec<_>, _>>()?;
            let f = module
                .fn_def(name)
                .ok_or_else(|| ReduceError::UnknownFn(name.clone()))?;
            if f.params.len() != args.len() {
                return Err(ReduceError::ArityMismatch {
                    what: name.clone(),
                    expected: f.params.len(),
                    got: args.len(),
                });
            }
            let mut body_env = Env::new();
            for (p, a) in f.params.iter().zip(args) {
                body_env.insert(p.name.clone(), a);
            }
            normalize(module, &body_env, &f.body)
        }

        Expr::Match { scrutinee, arms } => {
            let scrut = normalize(module, env, scrutinee)?;
            match &scrut {
                // The scrutinee is a value: select the arm and bind its fields.
                Expr::Ctor { name: cname, args } => {
                    let arm = arms
                        .iter()
                        .find(|a| &a.ctor == cname)
                        .ok_or_else(|| ReduceError::NoMatchingArm { ctor: cname.clone() })?;
                    if arm.binds.len() != args.len() {
                        return Err(ReduceError::ArityMismatch {
                            what: format!("match arm `{cname}`"),
                            expected: arm.binds.len(),
                            got: args.len(),
                        });
                    }
                    // Arms see the surrounding scope plus the freshly bound fields.
                    let mut arm_env = env.clone();
                    for (b, v) in arm.binds.iter().zip(args) {
                        arm_env.insert(b.clone(), v.clone());
                    }
                    normalize(module, &arm_env, &arm.body)
                }
                // Stuck: leave a residual match (do not descend into arms in M0).
                _ => Ok(Expr::Match { scrutinee: Box::new(scrut), arms: arms.clone() }),
            }
        }
    }
}

/// Evaluate a closed term to a value.
pub fn eval(module: &Module, expr: &Expr) -> Result<Expr, ReduceError> {
    normalize(module, &Env::new(), expr)
}

// --- Controlled reduction primitives for the proof kernel (M1).
//
// `normalize` above fully evaluates and is right for closed terms, but on open
// terms it would unfold recursive calls into residual `match`es, destroying the
// very `f(args)` shape a proof needs to rewrite with an induction hypothesis.
// So the kernel drives reduction with two single-purpose, always-terminating
// steps instead, and the proof script decides when to apply each.

/// One δ-step: replace every current `func(args)` with `func`'s body, its
/// parameters substituted (capture-avoiding). Does **not** recurse into the
/// substituted body, so recursion is exposed exactly one layer at a time. Calls
/// to other functions and the freshly introduced body are left untouched.
pub fn unfold_one(module: &Module, func: &str, e: &Expr) -> Expr {
    match e {
        Expr::Var { .. } => e.clone(),
        Expr::Ctor { name, args } => Expr::Ctor {
            name: name.clone(),
            args: args.iter().map(|a| unfold_one(module, func, a)).collect(),
        },
        Expr::Call { name, args } => {
            let args: Vec<Expr> = args.iter().map(|a| unfold_one(module, func, a)).collect();
            if name == func
                && let Some(f) = module.fn_def(func)
                && f.params.len() == args.len()
            {
                let map: HashMap<String, Expr> =
                    f.params.iter().map(|p| p.name.clone()).zip(args.iter().cloned()).collect();
                return subst(&f.body, &map);
            }
            Expr::Call { name: name.clone(), args }
        }
        Expr::Match { scrutinee, arms } => Expr::Match {
            scrutinee: Box::new(unfold_one(module, func, scrutinee)),
            arms: arms
                .iter()
                .map(|a| Arm { ctor: a.ctor.clone(), binds: a.binds.clone(), body: unfold_one(module, func, &a.body) })
                .collect(),
        },
    }
}

/// ι-reduction to normal form: fire every `match` whose scrutinee is a
/// constructor, repeatedly. Performs **no** unfolding, so it always terminates.
pub fn reduce_iota(e: &Expr) -> Expr {
    match e {
        Expr::Var { .. } => e.clone(),
        Expr::Ctor { name, args } => Expr::Ctor {
            name: name.clone(),
            args: args.iter().map(reduce_iota).collect(),
        },
        Expr::Call { name, args } => Expr::Call {
            name: name.clone(),
            args: args.iter().map(reduce_iota).collect(),
        },
        Expr::Match { scrutinee, arms } => {
            let scrut = reduce_iota(scrutinee);
            if let Expr::Ctor { name: cname, args } = &scrut
                && let Some(arm) = arms.iter().find(|a| &a.ctor == cname)
                && arm.binds.len() == args.len()
            {
                let map: HashMap<String, Expr> =
                    arm.binds.iter().cloned().zip(args.iter().cloned()).collect();
                return reduce_iota(&subst(&arm.body, &map));
            }
            // Stuck: reduce inside the arms but keep the residual match.
            Expr::Match {
                scrutinee: Box::new(scrut),
                arms: arms
                    .iter()
                    .map(|a| Arm { ctor: a.ctor.clone(), binds: a.binds.clone(), body: reduce_iota(&a.body) })
                    .collect(),
            }
        }
    }
}
