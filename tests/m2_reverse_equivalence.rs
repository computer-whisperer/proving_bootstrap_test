//! M2 — the north star. Prove the optimized `fast` reverse equals the spec
//! `rev`, for all inputs: `forall xs, fast(xs) = rev(xs)`.
//!
//! This is the whole vision in miniature: a naive spec, an accumulator-based
//! implementation, and a machine-checked proof they agree. It exercises lemma
//! citation and — the pedagogically interesting wall — hypothesis
//! generalization: `fast = rev` does not go through directly; you must first
//! prove the stronger `go(xs, acc) = append(rev(xs), acc)` for *all* `acc`.

use proving_bootstrap::obj_lang::ast::*;
use proving_bootstrap::obj_lang::build::*;
use proving_bootstrap::obj_lang::builtins::prelude;
use proving_bootstrap::obj_lang::check::check_module;
use proving_bootstrap::proof::ast::*;
use proving_bootstrap::proof::build::*;
use proving_bootstrap::proof::check::{check_theorem, check_theory, ProofError, Theory};

fn module() -> Module {
    let mut m = prelude();
    m.fns = vec![
        // append(xs, ys) = match xs { Nil => ys, Cons(h, t) => Cons(h, append(t, ys)) }
        fndef(
            "append",
            vec![param("xs", "List"), param("ys", "List")],
            "List",
            match_(
                var("xs"),
                vec![
                    arm("Nil", &[], var("ys")),
                    arm("Cons", &["h", "t"], cons(var("h"), call("append", vec![var("t"), var("ys")]))),
                ],
            ),
        ),
        // rev(xs) = match xs { Nil => Nil, Cons(h, t) => append(rev(t), Cons(h, Nil)) }   -- spec
        fndef(
            "rev",
            vec![param("xs", "List")],
            "List",
            match_(
                var("xs"),
                vec![
                    arm("Nil", &[], nil()),
                    arm("Cons", &["h", "t"], call("append", vec![call("rev", vec![var("t")]), cons(var("h"), nil())])),
                ],
            ),
        ),
        // go(xs, acc) = match xs { Nil => acc, Cons(h, t) => go(t, Cons(h, acc)) }
        fndef(
            "go",
            vec![param("xs", "List"), param("acc", "List")],
            "List",
            match_(
                var("xs"),
                vec![
                    arm("Nil", &[], var("acc")),
                    arm("Cons", &["h", "t"], call("go", vec![var("t"), cons(var("h"), var("acc"))])),
                ],
            ),
        ),
        // fast(xs) = go(xs, Nil)   -- implementation
        fndef("fast", vec![param("xs", "List")], "List", call("go", vec![var("xs"), nil()])),
    ];
    m
}

/// forall xs, append(xs, Nil) = xs
fn append_nil() -> Theorem {
    theorem(
        "append_nil",
        forall_eq(vec![param("xs", "List")], call("append", vec![var("xs"), nil()]), var("xs")),
        induct(
            "xs",
            vec![
                case("Nil", steps(vec![simp(Side::Lhs)], refl())),
                case("Cons", steps(vec![simp(Side::Lhs), rewrite(hyp(0), Dir::Lr, Side::Lhs)], refl())),
            ],
        ),
    )
}

/// forall a b c, append(append(a, b), c) = append(a, append(b, c))
fn append_assoc() -> Theorem {
    theorem(
        "append_assoc",
        forall_eq(
            vec![param("a", "List"), param("b", "List"), param("c", "List")],
            call("append", vec![call("append", vec![var("a"), var("b")]), var("c")]),
            call("append", vec![var("a"), call("append", vec![var("b"), var("c")])]),
        ),
        induct(
            "a",
            vec![
                case("Nil", steps(vec![simp(Side::Both)], refl())),
                case("Cons", steps(vec![simp(Side::Both), rewrite(hyp(0), Dir::Lr, Side::Lhs)], refl())),
            ],
        ),
    )
}

/// forall xs acc, go(xs, acc) = append(rev(xs), acc)   -- the generalized lemma
fn go_spec() -> Theorem {
    theorem(
        "go_spec",
        forall_eq(
            vec![param("xs", "List"), param("acc", "List")],
            call("go", vec![var("xs"), var("acc")]),
            call("append", vec![call("rev", vec![var("xs")]), var("acc")]),
        ),
        induct(
            "xs",
            vec![
                case("Nil", steps(vec![simp(Side::Both)], refl())),
                case(
                    "Cons",
                    steps(
                        vec![
                            // go(Cons h t, acc) -> go(t, Cons h acc);  rev side -> append(append(rev t, [h]), acc)
                            simp(Side::Both),
                            // rewrite go(t, _) with the IH
                            rewrite(hyp(0), Dir::Lr, Side::Lhs),
                            // reassociate the rev side
                            rewrite(lemma("append_assoc"), Dir::Lr, Side::Rhs),
                            // both sides now compute to append(rev t, Cons h acc)
                            simp(Side::Both),
                        ],
                        refl(),
                    ),
                ),
            ],
        ),
    )
}

/// forall xs, fast(xs) = rev(xs)   -- the theorem
fn fast_rev() -> Theorem {
    theorem(
        "fast_rev",
        forall_eq(vec![param("xs", "List")], call("fast", vec![var("xs")]), call("rev", vec![var("xs")])),
        steps(
            vec![
                // fast(xs) -> go(xs, Nil)
                simp(Side::Lhs),
                // go(xs, Nil) = append(rev(xs), Nil)   via the generalized lemma at acc := Nil
                rewrite(lemma("go_spec"), Dir::Lr, Side::Lhs),
                // append(rev(xs), Nil) = rev(xs)
                rewrite(lemma("append_nil"), Dir::Lr, Side::Lhs),
            ],
            refl(),
        ),
    )
}

#[test]
fn module_is_admitted() {
    assert_eq!(check_module(&module()), Ok(()));
}

#[test]
fn proves_lemmas_individually() {
    let m = module();
    let mut theory = Theory::default();
    // append_nil and append_assoc need nothing prior.
    assert_eq!(check_theorem(&m, &theory, &append_nil()), Ok(()), "append_nil");
    assert_eq!(check_theorem(&m, &theory, &append_assoc()), Ok(()), "append_assoc");
    // go_spec needs append_assoc in scope.
    theory = check_theory(&m, &[append_assoc()]).unwrap();
    assert_eq!(check_theorem(&m, &theory, &go_spec()), Ok(()), "go_spec");
}

#[test]
fn proves_fast_equals_rev_end_to_end() {
    // The whole chain, checked in dependency order.
    let result = check_theory(&module(), &[append_nil(), append_assoc(), go_spec(), fast_rev()]);
    assert!(result.is_ok(), "{result:?}");
}

#[test]
fn fast_rev_fails_without_its_lemmas() {
    // Citing go_spec/append_nil against an empty theory must be rejected.
    let err = check_theorem(&module(), &Theory::default(), &fast_rev()).unwrap_err();
    assert!(matches!(err, ProofError::NoLemma(_)), "{err:?}");
}

#[test]
fn whole_chain_round_trips_through_json() {
    let chain = vec![append_nil(), append_assoc(), go_spec(), fast_rev()];
    let json = serde_json::to_string_pretty(&chain).unwrap();
    let back: Vec<Theorem> = serde_json::from_str(&json).unwrap();
    assert_eq!(chain, back);
    assert!(check_theory(&module(), &back).is_ok());
}
