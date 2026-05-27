//! The capstone: in-place array reverse equals functional `rev`, for arbitrary
//! memory and arbitrary length —
//!   arr_from(rev_loop(m, 0, n−1), 0, n) = rev(arr_from(m, 0, n)).
//! Specializes the per-position invariant to a full reversal, pushes it through
//! `arr_from` to a reflected-read list, and meets `rev(arr_from(...))` at the
//! shared `arr_rev`.

use super::*;

// ---------------------------------------------------------------------------
// Task #4: connect the per-position invariant to arr_from = rev.
// ---------------------------------------------------------------------------

/// forall a b, sub(a, S(b)) = pred(sub(a, b))
pub fn sub_succ_r() -> Theorem {
    theorem(
        "sub_succ_r",
        forall_eq(
            vec![param("a", "Nat"), param("b", "Nat")],
            call("sub", vec![var("a"), s(var("b"))]),
            call("pred", vec![call("sub", vec![var("a"), var("b")])]),
        ),
        induct(
            "a",
            vec![
                case("Z", induct("b", vec![case("Z", steps(vec![simp(Side::Both)], refl())), case("S", steps(vec![simp(Side::Both)], refl()))])),
                case(
                    "S",
                    induct(
                        "b",
                        vec![
                            case("Z", steps(vec![simp(Side::Both)], refl())),
                            case("S", steps(vec![simp(Side::Both), rewrite(hyp(0), Dir::Lr, Side::Lhs)], refl())),
                        ],
                    ),
                ),
            ],
        ),
    )
}

/// forall m s c, arr_from(m, s, S c) = Cons(read(m, s), arr_from(m, S s, c))
/// The defining unfold as a rewrite — peels exactly one element (unlike `simp`,
/// which unfolds the count all the way down and loses the foldable tail).
pub fn arr_from_cons() -> Theorem {
    theorem(
        "arr_from_cons",
        forall_eq(
            vec![param("m", "Mem"), param("s", "Nat"), param("c", "Nat")],
            call("arr_from", vec![var("m"), var("s"), s(var("c"))]),
            cons(call("read", vec![var("m"), var("s")]), call("arr_from", vec![var("m"), s(var("s")), var("c")])),
        ),
        steps(vec![simp(Side::Lhs)], refl()),
    )
}

/// forall m s c, arr_from(m,s,S c) = append(arr_from(m,s,c), Cons(read(m,add(s,c)), Nil))
pub fn arr_from_snoc() -> Theorem {
    theorem(
        "arr_from_snoc",
        forall_eq(
            vec![param("m", "Mem"), param("s", "Nat"), param("c", "Nat")],
            call("arr_from", vec![var("m"), var("s"), s(var("c"))]),
            call("append", vec![call("arr_from", vec![var("m"), var("s"), var("c")]), cons(call("read", vec![var("m"), call("add", vec![var("s"), var("c")])]), nil())]),
        ),
        induct(
            "c",
            vec![
                case("Z", steps(vec![simp(Side::Both), rewrite(lemma("add_z_r"), Dir::Lr, Side::Rhs)], refl())),
                case(
                    "S",
                    // Peel one element off each side (arr_from_cons), apply IH at s := S s,
                    // then align add(S s, d) = add(s, S d) via add_succ_r.
                    steps(
                        vec![
                            rewrite(lemma("arr_from_cons"), Dir::Lr, Side::Lhs),
                            rewrite(lemma("arr_from_cons"), Dir::Lr, Side::Rhs),
                            simp(Side::Rhs),
                            rewrite(hyp(0), Dir::Lr, Side::Lhs),
                            simp(Side::Lhs),
                            rewrite(lemma("add_succ_r"), Dir::Lr, Side::Rhs),
                        ],
                        refl(),
                    ),
                ),
            ],
        ),
    )
}

/// forall xs ys, rev(append(xs, ys)) = append(rev(ys), rev(xs))
pub fn rev_append() -> Theorem {
    theorem(
        "rev_append",
        forall_eq(
            vec![param("xs", "List"), param("ys", "List")],
            call("rev", vec![call("append", vec![var("xs"), var("ys")])]),
            call("append", vec![call("rev", vec![var("ys")]), call("rev", vec![var("xs")])]),
        ),
        induct(
            "xs",
            vec![
                case("Nil", steps(vec![simp(Side::Both), rewrite(lemma("append_nil"), Dir::Lr, Side::Rhs)], refl())),
                case(
                    "Cons",
                    steps(vec![simp(Side::Both), rewrite(hyp(0), Dir::Lr, Side::Lhs), rewrite(lemma("append_assoc"), Dir::Lr, Side::Lhs)], refl()),
                ),
            ],
        ),
    )
}

/// forall m n, rev(arr_from(m, 0, n)) = arr_rev(m, n)
pub fn rev_arr_from() -> Theorem {
    theorem(
        "rev_arr_from",
        forall_eq(
            vec![param("m", "Mem"), param("n", "Nat")],
            call("rev", vec![call("arr_from", vec![var("m"), z(), var("n")])]),
            call("arr_rev", vec![var("m"), var("n")]),
        ),
        induct(
            "n",
            vec![
                case("Z", steps(vec![simp(Side::Both)], refl())),
                case(
                    "S",
                    // arr_from(m,0,S k) = append(arr_from(m,0,k), [read(m,k)]); rev distributes.
                    steps(
                        vec![
                            rewrite(lemma("arr_from_snoc"), Dir::Lr, Side::Lhs),
                            rewrite(lemma("rev_append"), Dir::Lr, Side::Lhs),
                            simp(Side::Both),
                            rewrite(hyp(0), Dir::Lr, Side::Lhs),
                        ],
                        refl(),
                    ),
                ),
            ],
        ),
    )
}

/// forall m hi s count, [sub(hi, s) = pred(count)] ⊢ read_refl_arr(m, hi, s, count) = arr_rev(m, count)
pub fn read_refl_arr_eq() -> Theorem {
    theorem(
        "read_refl_arr_eq",
        forall_eq_cond(
            vec![param("m", "Mem"), param("hi", "Nat"), param("s", "Nat"), param("count", "Nat")],
            vec![eqn(call("sub", vec![var("hi"), var("s")]), call("pred", vec![var("count")]))],
            call("read_refl_arr", vec![var("m"), var("hi"), var("s"), var("count")]),
            call("arr_rev", vec![var("m"), var("count")]),
        ),
        induct(
            "count",
            vec![
                case("Z", steps(vec![simp(Side::Both)], refl())),
                case(
                    "S",
                    steps(
                        vec![simp(Side::Both), rewrite(premise(0), Dir::Lr, Side::Lhs), simp(Side::Lhs)],
                        rewrite_with(
                            hyp(0),
                            Dir::Lr,
                            Side::Lhs,
                            // discharge IH premise sub(hi, S s) = pred c
                            vec![steps(vec![rewrite(lemma("sub_succ_r"), Dir::Lr, Side::Lhs), rewrite(premise(0), Dir::Lr, Side::Lhs), simp(Side::Lhs)], refl())],
                            refl(),
                        ),
                    ),
                ),
            ],
        ),
    )
}

#[test]
fn proves_task4_list_lemmas() {
    let _ = list_theory();
}

/// forall a b, add(S(a), b) = S(add(a, b))  (the defining unfold, as a rewrite)
pub fn add_succ_l() -> Theorem {
    theorem(
        "add_succ_l",
        forall_eq(vec![param("a", "Nat"), param("b", "Nat")], call("add", vec![s(var("a")), var("b")]), s(call("add", vec![var("a"), var("b")]))),
        steps(vec![simp(Side::Lhs)], refl()),
    )
}

/// forall a b, le(S(a), S(b)) = le(a, b)  (the defining peel, as a rewrite)
pub fn le_succ_both() -> Theorem {
    theorem(
        "le_succ_both",
        forall_eq(vec![param("a", "Nat"), param("b", "Nat")], call("le", vec![s(var("a")), s(var("b"))]), call("le", vec![var("a"), var("b")])),
        steps(vec![simp(Side::Lhs)], refl()),
    )
}

/// forall m hi p, [le(p, hi) = True] ⊢ read(rev_loop(m, 0, hi), p) = read(m, sub(hi, p))
/// Specializes the per-position spec to a *full* reversal of [0, hi]: every
/// in-range position p reads the mirror sub(hi, p). Uses rev_loop_spec.
pub fn read_rev_full() -> Theorem {
    theorem(
        "read_rev_full",
        forall_eq_cond(
            vec![param("m", "Mem"), param("hi", "Nat"), param("p", "Nat")],
            vec![eqn(call("le", vec![var("p"), var("hi")]), tru())],
            call("read", vec![call("rev_loop", vec![var("m"), z(), var("hi")]), var("p")]),
            call("read", vec![var("m"), call("sub", vec![var("hi"), var("p")])]),
        ),
        steps(
            vec![
                rewrite(lemma("rev_loop_spec"), Dir::Lr, Side::Lhs), // -> expected(m,0,hi,p)
                simp(Side::Lhs),                                     // -> ite(le(p,hi), read(m,sub(hi,p)), read(m,p))
                rewrite(premise(0), Dir::Lr, Side::Lhs),             // le(p,hi) -> True
                simp(Side::Lhs),
            ],
            refl(),
        ),
    )
}

/// forall m hi s count, [le(add(s, count), S(hi)) = True] ⊢
///   arr_from(rev_loop(m, 0, hi), s, count) = read_refl_arr(m, hi, s, count)
/// Pushes read_rev_full through arr_from: extracting positions s..s+count-1 of the
/// reversed buffer reads the mirror addresses. Precondition = last position ≤ hi.
pub fn arr_from_rev_eq_refl() -> Theorem {
    // le(s, hi): s ≤ s+$0 ≤ hi.
    let le_s_hi = || {
        rewrite_with_inst(
            lemma("le_trans"),
            Dir::Lr,
            Side::Lhs,
            vec![("b", call("add", vec![var("s"), var("$0")]))],
            vec![
                steps(vec![rewrite(lemma("le_add_r"), Dir::Lr, Side::Lhs)], refl()),
                steps(vec![rewrite(lemma("le_succ_both"), Dir::Rl, Side::Lhs), rewrite(lemma("add_succ_r"), Dir::Rl, Side::Lhs), rewrite(premise(0), Dir::Lr, Side::Lhs)], refl()),
            ],
            refl(),
        )
    };
    // le(add(S s, $0), S hi) = the IH precondition (= premise modulo add_succ_{l,r}).
    // Use targeted rewrites, NOT simp (which would peel the outer le(S,S) too).
    let ih_precond = || {
        steps(
            vec![
                rewrite(lemma("add_succ_l"), Dir::Lr, Side::Lhs), // add(S s, $0) -> S(add s $0)
                rewrite(lemma("add_succ_r"), Dir::Rl, Side::Lhs), // S(add s $0) -> add(s, S $0)
                rewrite(premise(0), Dir::Lr, Side::Lhs),
            ],
            refl(),
        )
    };
    theorem(
        "arr_from_rev_eq_refl",
        forall_eq_cond(
            vec![param("m", "Mem"), param("hi", "Nat"), param("s", "Nat"), param("count", "Nat")],
            vec![eqn(call("le", vec![call("add", vec![var("s"), var("count")]), s(var("hi"))]), tru())],
            call("arr_from", vec![call("rev_loop", vec![var("m"), z(), var("hi")]), var("s"), var("count")]),
            call("read_refl_arr", vec![var("m"), var("hi"), var("s"), var("count")]),
        ),
        induct(
            "count",
            vec![
                case("Z", steps(vec![simp(Side::Both)], refl())),
                case(
                    "S",
                    steps(
                        vec![rewrite(lemma("arr_from_cons"), Dir::Lr, Side::Lhs)],
                        rewrite_with(
                            lemma("read_rev_full"),
                            Dir::Lr,
                            Side::Lhs,
                            vec![le_s_hi()],
                            steps(vec![simp(Side::Rhs)], rewrite_with(hyp(0), Dir::Lr, Side::Lhs, vec![ih_precond()], refl())),
                        ),
                    ),
                ),
            ],
        ),
    )
}

/// forall m n, arr_from(rev_loop(m, 0, pred n), 0, n) = rev(arr_from(m, 0, n))
/// THE capstone: in-place array reverse equals functional rev, for arbitrary
/// memory and arbitrary length n. LHS → read_refl_arr → arr_rev ← rev(arr_from).
pub fn reverse_eq_rev() -> Theorem {
    theorem(
        "reverse_eq_rev",
        forall_eq(
            vec![param("m", "Mem"), param("n", "Nat")],
            call("arr_from", vec![call("rev_loop", vec![var("m"), z(), call("pred", vec![var("n")])]), z(), var("n")]),
            call("rev", vec![call("arr_from", vec![var("m"), z(), var("n")])]),
        ),
        rewrite_with(
            lemma("arr_from_rev_eq_refl"),
            Dir::Lr,
            Side::Lhs,
            // le(add(0, n), S(pred n)) = True
            vec![case_on(
                var("n"),
                "Nat",
                vec![
                    case("Z", steps(vec![rewrite_all(hyp(0), Dir::Lr, Side::Lhs), simp(Side::Lhs)], refl())),
                    case("S", steps(vec![rewrite_all(hyp(0), Dir::Lr, Side::Lhs), simp(Side::Lhs), rewrite(lemma("le_refl"), Dir::Lr, Side::Lhs)], refl())),
                ],
            )],
            rewrite_with(
                lemma("read_refl_arr_eq"),
                Dir::Lr,
                Side::Lhs,
                // sub(pred n, 0) = pred n
                vec![steps(vec![simp(Side::Lhs)], refl())],
                // now LHS = arr_rev(m, n); fold the RHS rev(arr_from(...)) to match.
                steps(vec![rewrite(lemma("rev_arr_from"), Dir::Lr, Side::Rhs)], refl()),
            ),
        ),
    )
}

#[test]
#[ignore = "the capstone: in-place reverse = rev for universal n (slow: builds the full theory)"]
fn proves_reverse_eq_rev_universal() {
    let m = module();
    let theory = full_theory();
    assert_eq!(check_theorem(&m, &theory, &reverse_eq_rev()), Ok(()), "reverse_eq_rev");
}

/// forall m, arr_from(rev_loop(m, 0, n-1), 0, n) = rev(arr_from(m, 0, n))
/// for a FIXED size n, but arbitrary memory contents. Concrete indices make
/// every nat_eq/lt reduce and the list structure concrete, so the whole
/// pipeline (loop → swap → framing → functional rev) computes under `simp`,
/// leaving only the symbolic values read(m,k) — which match on both sides.
pub fn reverse_fixed_size(n: u64) -> Theorem {
    theorem(
        "reverse_fixed",
        forall_eq(
            vec![param("m", "Mem")],
            call("arr_from", vec![call("rev_loop", vec![var("m"), z(), nat(n - 1)]), z(), nat(n)]),
            call("rev", vec![call("arr_from", vec![var("m"), z(), nat(n)])]),
        ),
        steps(vec![simp(Side::Both)], refl()),
    )
}

#[test]
fn proves_reverse_for_fixed_sizes_general_memory() {
    // In-place reverse = functional rev, for arbitrary memory contents, at fixed
    // lengths. The general-n proof needs the unbounded loop invariant (see ROADMAP).
    let m = module();
    for n in 1..=5 {
        assert_eq!(check_theorem(&m, &Theory::default(), &reverse_fixed_size(n)), Ok(()), "n = {n}");
    }
}

#[test]
fn concrete_in_place_reverse_executes() {
    // Memory holding [1, 2, 3] at addresses 0, 1, 2; reverse in place; read back.
    let m = module();
    let mem0 = ctor(
        "MCell",
        vec![nat(0), nat(1), ctor("MCell", vec![nat(1), nat(2), ctor("MCell", vec![nat(2), nat(3), ctor("MNil", vec![])])])],
    );
    let thm = theorem(
        "concrete_reverse",
        forall_eq(
            vec![],
            call("arr_from", vec![call("rev_loop", vec![mem0, z(), nat(2)]), z(), nat(3)]),
            list(vec![nat(3), nat(2), nat(1)]),
        ),
        steps(vec![simp(Side::Both)], refl()),
    );
    assert_eq!(check_theorem(&m, &Theory::default(), &thm), Ok(()));
}
