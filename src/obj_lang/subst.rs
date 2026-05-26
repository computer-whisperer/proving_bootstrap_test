//! Capture-avoiding substitution and free-variable analysis over object-language
//! terms. The only binders are `match` arms, so this stays small — but it is
//! part of the trusted path (the kernel substitutes when it unfolds, rewrites,
//! and inducts), so it is careful about capture.

use std::collections::{HashMap, HashSet};

use super::ast::*;

/// Free variables of `e` (parameters/fields not bound by an enclosing arm).
pub fn free_vars(e: &Expr) -> HashSet<String> {
    let mut out = HashSet::new();
    collect_free(e, &mut out);
    out
}

fn collect_free(e: &Expr, out: &mut HashSet<String>) {
    match e {
        Expr::Var { name } => {
            out.insert(name.clone());
        }
        Expr::Ctor { args, .. } | Expr::Call { args, .. } => {
            for a in args {
                collect_free(a, out);
            }
        }
        Expr::Match { scrutinee, arms } => {
            collect_free(scrutinee, out);
            for arm in arms {
                let mut body = HashSet::new();
                collect_free(&arm.body, &mut body);
                for b in &arm.binds {
                    body.remove(b);
                }
                out.extend(body);
            }
        }
    }
}

/// A name not present in `avoid`.
pub fn fresh_name(avoid: &HashSet<String>) -> String {
    let mut k = 0;
    loop {
        let candidate = format!("${k}");
        if !avoid.contains(&candidate) {
            return candidate;
        }
        k += 1;
    }
}

/// Capture-avoiding simultaneous substitution.
pub fn subst(e: &Expr, map: &HashMap<String, Expr>) -> Expr {
    match e {
        Expr::Var { name } => map.get(name).cloned().unwrap_or_else(|| e.clone()),
        Expr::Ctor { name, args } => Expr::Ctor {
            name: name.clone(),
            args: args.iter().map(|a| subst(a, map)).collect(),
        },
        Expr::Call { name, args } => Expr::Call {
            name: name.clone(),
            args: args.iter().map(|a| subst(a, map)).collect(),
        },
        Expr::Match { scrutinee, arms } => Expr::Match {
            scrutinee: Box::new(subst(scrutinee, map)),
            arms: arms.iter().map(|arm| subst_arm(arm, map)).collect(),
        },
    }
}

fn subst_arm(arm: &Arm, map: &HashMap<String, Expr>) -> Arm {
    // Binders shadow the substitution; only entries for non-bound keys apply.
    let mut active: HashMap<String, Expr> =
        map.iter().filter(|(k, _)| !arm.binds.contains(k)).map(|(k, v)| (k.clone(), v.clone())).collect();
    if active.is_empty() {
        return arm.clone();
    }

    // If any incoming term would be captured by a binder, rename that binder.
    let incoming_free: HashSet<String> = active.values().flat_map(free_vars).collect();
    let mut binds = arm.binds.clone();
    let mut rename: HashMap<String, Expr> = HashMap::new();
    if binds.iter().any(|b| incoming_free.contains(b)) {
        let mut avoid: HashSet<String> = incoming_free.clone();
        avoid.extend(free_vars(&arm.body));
        avoid.extend(binds.iter().cloned());
        for b in &mut binds {
            if incoming_free.contains(b) {
                let nb = fresh_name(&avoid);
                avoid.insert(nb.clone());
                rename.insert(b.clone(), Expr::Var { name: nb.clone() });
                *b = nb;
            }
        }
    }

    // Apply binder renaming, then the active substitution, to the body.
    let body = if rename.is_empty() { arm.body.clone() } else { subst(&arm.body, &rename) };
    // Renamed binders must not be clobbered by `active`.
    for nb in rename.values() {
        if let Expr::Var { name } = nb {
            active.remove(name);
        }
    }
    Arm { ctor: arm.ctor.clone(), binds, body: subst(&body, &active) }
}
