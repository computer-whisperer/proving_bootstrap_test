//! M0 demo: define the reverse functions in the object language, admit the
//! module, evaluate concrete terms, and show a concrete unit test passing by
//! evaluation alone. The *universal* proof that `fast = rev` is M1/M2 work.

use proving_bootstrap::obj_lang::ast::*;
use proving_bootstrap::obj_lang::build::*;
use proving_bootstrap::obj_lang::builtins::prelude;
use proving_bootstrap::obj_lang::check::{check_module, CheckError};
use proving_bootstrap::obj_lang::reduce::eval;

/// The demo module: arithmetic and equality helpers plus the two reverses.
fn demo_module() -> Module {
    let mut m = prelude();
    m.fns = vec![
        // add(n, m) = match n { Z => m, S(k) => S(add(k, m)) }
        fndef(
            "add",
            vec![param("n", "Nat"), param("m", "Nat")],
            "Nat",
            match_(
                var("n"),
                vec![
                    arm("Z", &[], var("m")),
                    arm("S", &["k"], s(call("add", vec![var("k"), var("m")]))),
                ],
            ),
        ),
        // and(a, b) = match a { True => b, False => False }
        fndef(
            "and",
            vec![param("a", "Bool"), param("b", "Bool")],
            "Bool",
            match_(var("a"), vec![arm("True", &[], var("b")), arm("False", &[], fls())]),
        ),
        // nat_eq(a, b) = match a { Z => match b { Z => True, S _ => False },
        //                          S ka => match b { Z => False, S kb => nat_eq(ka, kb) } }
        fndef(
            "nat_eq",
            vec![param("a", "Nat"), param("b", "Nat")],
            "Bool",
            match_(
                var("a"),
                vec![
                    arm("Z", &[], match_(var("b"), vec![arm("Z", &[], tru()), arm("S", &["_kb"], fls())])),
                    arm(
                        "S",
                        &["ka"],
                        match_(
                            var("b"),
                            vec![
                                arm("Z", &[], fls()),
                                arm("S", &["kb"], call("nat_eq", vec![var("ka"), var("kb")])),
                            ],
                        ),
                    ),
                ],
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
        // rev(xs) = match xs { Nil => Nil, Cons(h, t) => append(rev(t), Cons(h, Nil)) }  -- the spec
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
        // fast(xs) = go(xs, Nil)  -- the implementation to be proven equal to rev
        fndef("fast", vec![param("xs", "List")], "List", call("go", vec![var("xs"), nil()])),
        // list_eq(xs, ys) = structural equality on lists of Nat
        fndef(
            "list_eq",
            vec![param("xs", "List"), param("ys", "List")],
            "Bool",
            match_(
                var("xs"),
                vec![
                    arm("Nil", &[], match_(var("ys"), vec![arm("Nil", &[], tru()), arm("Cons", &["_h", "_t"], fls())])),
                    arm(
                        "Cons",
                        &["hx", "tx"],
                        match_(
                            var("ys"),
                            vec![
                                arm("Nil", &[], fls()),
                                arm(
                                    "Cons",
                                    &["hy", "ty"],
                                    call(
                                        "and",
                                        vec![
                                            call("nat_eq", vec![var("hx"), var("hy")]),
                                            call("list_eq", vec![var("tx"), var("ty")]),
                                        ],
                                    ),
                                ),
                            ],
                        ),
                    ),
                ],
            ),
        ),
        // test(xs) = list_eq(fast(xs), rev(xs))  -- a unit test, as a Bool function
        fndef(
            "test",
            vec![param("xs", "List")],
            "Bool",
            call("list_eq", vec![call("fast", vec![var("xs")]), call("rev", vec![var("xs")])]),
        ),
    ];
    m
}

#[test]
fn module_is_admitted() {
    let m = demo_module();
    assert_eq!(check_module(&m), Ok(()));
}

#[test]
fn evaluates_concrete_terms() {
    let m = demo_module();
    assert_eq!(eval(&m, &call("add", vec![nat(2), nat(3)])).unwrap(), nat(5));

    let l123 = list(vec![nat(1), nat(2), nat(3)]);
    let l321 = list(vec![nat(3), nat(2), nat(1)]);
    assert_eq!(eval(&m, &call("rev", vec![l123.clone()])).unwrap(), l321);
    assert_eq!(eval(&m, &call("fast", vec![l123])).unwrap(), l321);
}

#[test]
fn concrete_unit_test_passes_by_evaluation() {
    // The whole M0 point: a unit test is a Bool function, and the concrete case
    // is discharged just by running it.
    let m = demo_module();
    let xs = list(vec![nat(4), nat(1), nat(5), nat(9), nat(2)]);
    assert_eq!(eval(&m, &call("test", vec![xs])).unwrap(), tru());
}

#[test]
fn ast_round_trips_through_json() {
    let m = demo_module();
    let json = serde_json::to_string_pretty(&m).unwrap();
    let back: Module = serde_json::from_str(&json).unwrap();
    assert_eq!(m, back);
}

#[test]
fn rejects_non_structural_recursion() {
    // loopy(n) = loopy(n): the argument never shrinks.
    let mut m = prelude();
    m.fns = vec![fndef("loopy", vec![param("n", "Nat")], "Nat", call("loopy", vec![var("n")]))];
    let errs = check_module(&m).unwrap_err();
    assert!(errs.iter().any(|e| matches!(e, CheckError::NonStructuralRecursion { .. })), "{errs:?}");
}

#[test]
fn rejects_mutual_recursion() {
    let mut m = prelude();
    m.fns = vec![
        fndef("ping", vec![param("n", "Nat")], "Nat", call("pong", vec![var("n")])),
        fndef("pong", vec![param("n", "Nat")], "Nat", call("ping", vec![var("n")])),
    ];
    let errs = check_module(&m).unwrap_err();
    assert!(errs.iter().any(|e| matches!(e, CheckError::MutualRecursion { .. })), "{errs:?}");
}
