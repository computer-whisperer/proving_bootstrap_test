//! M1: prove two universal properties by induction, end to end through the
//! kernel — `forall n, add(n, Z) = n` and `forall xs, append(xs, Nil) = xs`.
//! Both go: induct, then in each case unfold + reduce, using the induction
//! hypothesis in the recursive case.

use proving_bootstrap::obj_lang::ast::*;
use proving_bootstrap::obj_lang::build::*;
use proving_bootstrap::obj_lang::builtins::prelude;
use proving_bootstrap::proof::ast::*;
use proving_bootstrap::proof::build::*;
use proving_bootstrap::proof::check::{check_theorem, check_theory, ProofError, Theory};

/// Module with just the two functions under test.
fn module() -> Module {
    let mut m = prelude();
    m.fns = vec![
        // add(n, m) = match n { Z => m, S(k) => S(add(k, m)) }
        fndef(
            "add",
            vec![param("n", "Nat"), param("m", "Nat")],
            "Nat",
            match_(
                var("n"),
                vec![arm("Z", &[], var("m")), arm("S", &["k"], s(call("add", vec![var("k"), var("m")])))],
            ),
        ),
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
    ];
    m
}

/// forall n, add(n, Z) = n
fn add_zero() -> Theorem {
    theorem(
        "add_zero",
        forall_eq(vec![param("n", "Nat")], call("add", vec![var("n"), z()]), var("n")),
        induct(
            "n",
            vec![
                // base: add(Z, Z) reduces to Z
                case("Z", steps(vec![unfold("add", Side::Lhs), reduce(Side::Lhs)], refl())),
                // step: add(S k, Z) -> S(add(k, Z)) -> [IH] S k
                case(
                    "S",
                    steps(
                        vec![unfold("add", Side::Lhs), reduce(Side::Lhs), rewrite(hyp(0), Dir::Lr, Side::Lhs)],
                        refl(),
                    ),
                ),
            ],
        ),
    )
}

/// forall xs, append(xs, Nil) = xs
fn append_nil() -> Theorem {
    theorem(
        "append_nil",
        forall_eq(vec![param("xs", "List")], call("append", vec![var("xs"), nil()]), var("xs")),
        induct(
            "xs",
            vec![
                case("Nil", steps(vec![unfold("append", Side::Lhs), reduce(Side::Lhs)], refl())),
                case(
                    "Cons",
                    steps(
                        vec![unfold("append", Side::Lhs), reduce(Side::Lhs), rewrite(hyp(0), Dir::Lr, Side::Lhs)],
                        refl(),
                    ),
                ),
            ],
        ),
    )
}

#[test]
fn proves_add_zero() {
    assert_eq!(check_theorem(&module(), &Theory::default(), &add_zero()), Ok(()));
}

#[test]
fn proves_append_nil() {
    assert_eq!(check_theorem(&module(), &Theory::default(), &append_nil()), Ok(()));
}

#[test]
fn theory_checks_both_in_order() {
    assert!(check_theory(&module(), &[add_zero(), append_nil()]).is_ok());
}

#[test]
fn proof_round_trips_through_json() {
    let thm = add_zero();
    let json = serde_json::to_string_pretty(&thm).unwrap();
    let back: Theorem = serde_json::from_str(&json).unwrap();
    assert_eq!(thm, back);
}

#[test]
fn rejects_refl_without_reduction() {
    // Claiming add(n,Z) = n closes by Refl alone is false: the sides differ.
    let bogus = theorem(
        "bogus",
        forall_eq(vec![param("n", "Nat")], call("add", vec![var("n"), z()]), var("n")),
        refl(),
    );
    assert!(matches!(
        check_theorem(&module(), &Theory::default(), &bogus),
        Err(ProofError::NotReflexive { .. })
    ));
}

#[test]
fn rejects_missing_induction_case() {
    // Induct on n but only handle Z; the S case is unproven.
    let bogus = theorem(
        "bogus",
        forall_eq(vec![param("n", "Nat")], call("add", vec![var("n"), z()]), var("n")),
        induct("n", vec![case("Z", steps(vec![unfold("add", Side::Lhs), reduce(Side::Lhs)], refl()))]),
    );
    assert!(matches!(
        check_theorem(&module(), &Theory::default(), &bogus),
        Err(ProofError::MissingCase { .. })
    ));
}

#[test]
fn rejects_bad_rewrite() {
    // In the S case, rewrite with a non-existent hypothesis index.
    let bogus = theorem(
        "bogus",
        forall_eq(vec![param("n", "Nat")], call("add", vec![var("n"), z()]), var("n")),
        induct(
            "n",
            vec![
                case("Z", steps(vec![unfold("add", Side::Lhs), reduce(Side::Lhs)], refl())),
                case(
                    "S",
                    steps(
                        vec![unfold("add", Side::Lhs), reduce(Side::Lhs), rewrite(hyp(5), Dir::Lr, Side::Lhs)],
                        refl(),
                    ),
                ),
            ],
        ),
    );
    assert!(matches!(check_theorem(&module(), &Theory::default(), &bogus), Err(ProofError::NoHyp(5))));
}
