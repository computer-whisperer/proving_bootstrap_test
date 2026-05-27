//! The arithmetic toolkit the loop invariant needs: order (`le`/`lt`)
//! monotonicity, `sub`/`add` identities, `nat_eq`/`read` congruence, and the
//! "mirror" lemmas about the reflected index `i + j − p`. Mostly conditional
//! equations (premise ⊢ conclusion), hand-proved by a uniform double-induction
//! pattern; the unconditional leaves are discharged by the search.

use super::*;

// --- arithmetic lemma library (toward the universal-n reverse) ---

/// forall x, and(x, True) = x
pub fn and_true_r() -> Theorem {
    theorem(
        "and_true_r",
        forall_eq(vec![param("x", "Bool")], call("and", vec![var("x"), tru()]), var("x")),
        case_on(
            var("x"),
            "Bool",
            vec![
                case("True", steps(vec![rewrite_all(hyp(0), Dir::Lr, Side::Both), simp(Side::Lhs)], refl())),
                case("False", steps(vec![rewrite_all(hyp(0), Dir::Lr, Side::Both), simp(Side::Lhs)], refl())),
            ],
        ),
    )
}

/// forall x, and(x, False) = False
pub fn and_false_r() -> Theorem {
    theorem(
        "and_false_r",
        forall_eq(vec![param("x", "Bool")], call("and", vec![var("x"), fls()]), fls()),
        case_on(
            var("x"),
            "Bool",
            vec![
                case("True", steps(vec![rewrite_all(hyp(0), Dir::Lr, Side::Lhs), simp(Side::Lhs)], refl())),
                case("False", steps(vec![rewrite_all(hyp(0), Dir::Lr, Side::Lhs), simp(Side::Lhs)], refl())),
            ],
        ),
    )
}

/// forall a, le(a, a) = True
pub fn le_refl() -> Theorem {
    theorem(
        "le_refl",
        forall_eq(vec![param("a", "Nat")], call("le", vec![var("a"), var("a")]), tru()),
        induct(
            "a",
            vec![
                case("Z", steps(vec![simp(Side::Lhs)], refl())),
                case("S", steps(vec![simp(Side::Lhs), rewrite(hyp(0), Dir::Lr, Side::Lhs)], refl())),
            ],
        ),
    )
}

/// forall a, lt(a, a) = False
pub fn lt_irrefl() -> Theorem {
    theorem(
        "lt_irrefl",
        forall_eq(vec![param("a", "Nat")], call("lt", vec![var("a"), var("a")]), fls()),
        induct(
            "a",
            vec![
                case("Z", steps(vec![simp(Side::Lhs)], refl())),
                case("S", steps(vec![simp(Side::Lhs), rewrite(hyp(0), Dir::Lr, Side::Lhs)], refl())),
            ],
        ),
    )
}

/// forall a, le(a, S(a)) = True
pub fn le_succ_same() -> Theorem {
    theorem(
        "le_succ_same",
        forall_eq(vec![param("a", "Nat")], call("le", vec![var("a"), s(var("a"))]), tru()),
        induct(
            "a",
            vec![
                case("Z", steps(vec![simp(Side::Lhs)], refl())),
                case("S", steps(vec![simp(Side::Lhs), rewrite(hyp(0), Dir::Lr, Side::Lhs)], refl())),
            ],
        ),
    )
}

/// forall a, lt(a, Z) = False
pub fn lt_z() -> Theorem {
    theorem(
        "lt_z",
        forall_eq(vec![param("a", "Nat")], call("lt", vec![var("a"), z()]), fls()),
        case_on(
            var("a"),
            "Nat",
            vec![
                case("Z", steps(vec![rewrite(hyp(0), Dir::Lr, Side::Lhs), simp(Side::Lhs)], refl())),
                case("S", steps(vec![rewrite(hyp(0), Dir::Lr, Side::Lhs), simp(Side::Lhs)], refl())),
            ],
        ),
    )
}

/// forall a b, lt(a, S(b)) = le(a, b)   (a < b+1  ⟺  a ≤ b)
pub fn le_lt_succ() -> Theorem {
    theorem(
        "le_lt_succ",
        forall_eq(vec![param("a", "Nat"), param("b", "Nat")], call("lt", vec![var("a"), s(var("b"))]), call("le", vec![var("a"), var("b")])),
        induct(
            "a",
            vec![
                case("Z", steps(vec![simp(Side::Both)], refl())),
                case(
                    "S",
                    case_on(
                        var("b"),
                        "Nat",
                        vec![
                            // b = Z: lt(k, Z) = False = le(S k, Z)
                            case(
                                "Z",
                                steps(
                                    vec![rewrite(hyp(1), Dir::Lr, Side::Both), simp(Side::Both), rewrite(lemma("lt_z"), Dir::Lr, Side::Lhs)],
                                    refl(),
                                ),
                            ),
                            // b = S(kb): reduces to the IH at kb
                            case(
                                "S",
                                steps(
                                    vec![rewrite(hyp(1), Dir::Lr, Side::Both), simp(Side::Both), rewrite(hyp(0), Dir::Lr, Side::Lhs)],
                                    refl(),
                                ),
                            ),
                        ],
                    ),
                ),
            ],
        ),
    )
}

/// forall a, add(a, Z) = a
pub fn add_z_r() -> Theorem {
    theorem(
        "add_z_r",
        forall_eq(vec![param("a", "Nat")], call("add", vec![var("a"), z()]), var("a")),
        induct(
            "a",
            vec![
                case("Z", steps(vec![simp(Side::Lhs)], refl())),
                case("S", steps(vec![simp(Side::Lhs), rewrite(hyp(0), Dir::Lr, Side::Lhs)], refl())),
            ],
        ),
    )
}

/// forall a, [le(a, Z) = True] ⊢ a = Z
/// `induct` (not `case_on`) substitutes the premise, so the S case's premise
/// becomes `le(S(k), Z) = True` — contradictory, closed by ex-falso.
pub fn le_z_eq() -> Theorem {
    theorem(
        "le_z_eq",
        forall_eq_cond(vec![param("a", "Nat")], vec![eqn(call("le", vec![var("a"), z()]), tru())], var("a"), z()),
        induct("a", vec![case("Z", refl()), case("S", absurd(premise(0)))]),
    )
}

/// forall a b, [lt(a, b) = True] ⊢ nat_eq(a, b) = False.
/// The keystone conditional lemma: strict-less-than implies disequal. Search
/// cannot find this (it needs to apply its own conditional IH via `RewriteWith`).
/// Hand structure: induct on `a`; in each case **induct on `b`** (not `case_on`)
/// so the premise is substituted, exposing the boundary `lt(_, Z)`/`lt(Z, _)` as
/// a constructor clash for `absurd`; the S/S case applies the conditional IH.
pub fn lt_imp_neq() -> Theorem {
    // Subproof obligation for the IH premise: given premise[0] = lt(S ka, S kb) =
    // True, prove lt(ka, kb) = True. Rewrite the goal's True back to the premise
    // LHS, then `simp` peels the S/S — leaving lt(ka,kb)=lt(ka,kb).
    let lt_pred = || steps(vec![rewrite(premise(0), Dir::Rl, Side::Rhs), simp(Side::Rhs)], refl());
    theorem(
        "lt_imp_neq",
        forall_eq_cond(
            vec![param("a", "Nat"), param("b", "Nat")],
            vec![eqn(call("lt", vec![var("a"), var("b")]), tru())],
            call("nat_eq", vec![var("a"), var("b")]),
            fls(),
        ),
        induct(
            "a",
            vec![
                case(
                    "Z",
                    induct(
                        "b",
                        vec![
                            case("Z", absurd(premise(0))),               // lt(Z,Z)=True is false
                            case("S", steps(vec![simp(Side::Lhs)], refl())), // nat_eq(Z,S _)=False
                        ],
                    ),
                ),
                case(
                    "S",
                    induct(
                        "b",
                        vec![
                            case("Z", absurd(premise(0))),               // lt(S _,Z)=True is false
                            case(
                                "S",
                                // nat_eq(S ka,S kb) -> nat_eq(ka,kb); discharge via IH (hyp 0).
                                steps(
                                    vec![simp(Side::Lhs)],
                                    rewrite_with(hyp(0), Dir::Lr, Side::Lhs, vec![lt_pred()], refl()),
                                ),
                            ),
                        ],
                    ),
                ),
            ],
        ),
    )
}

/// forall a b, [lt(a, b) = True] ⊢ nat_eq(b, a) = False — the swapped-argument
/// form (same structure; the loop framing needs both orientations).
pub fn lt_imp_neq_sym() -> Theorem {
    let lt_pred = || steps(vec![rewrite(premise(0), Dir::Rl, Side::Rhs), simp(Side::Rhs)], refl());
    theorem(
        "lt_imp_neq_sym",
        forall_eq_cond(
            vec![param("a", "Nat"), param("b", "Nat")],
            vec![eqn(call("lt", vec![var("a"), var("b")]), tru())],
            call("nat_eq", vec![var("b"), var("a")]),
            fls(),
        ),
        induct(
            "a",
            vec![
                case(
                    "Z",
                    induct(
                        "b",
                        vec![
                            case("Z", absurd(premise(0))),
                            case("S", steps(vec![simp(Side::Lhs)], refl())), // nat_eq(S _,Z)=False
                        ],
                    ),
                ),
                case(
                    "S",
                    induct(
                        "b",
                        vec![
                            case("Z", absurd(premise(0))),
                            case(
                                "S",
                                steps(
                                    vec![simp(Side::Lhs)],
                                    rewrite_with(hyp(0), Dir::Lr, Side::Lhs, vec![lt_pred()], refl()),
                                ),
                            ),
                        ],
                    ),
                ),
            ],
        ),
    )
}

/// The recurring premise sub-proof for double-induction conditional lemmas:
/// given `premise[i]` of the form `f(S ka, S kb) = V`, prove the peeled goal
/// `f(ka, kb) = V`. Rewrites the goal's `V` back to the premise LHS, then `simp`
/// peels the `S/S`, leaving `f(ka,kb)=f(ka,kb)`.
pub fn demote(i: usize) -> Proof {
    steps(vec![rewrite(premise(i), Dir::Rl, Side::Rhs), simp(Side::Rhs)], refl())
}

/// forall a b, [le(a, b) = True] ⊢ le(a, S(b)) = True
pub fn le_succ_r() -> Theorem {
    theorem(
        "le_succ_r",
        forall_eq_cond(
            vec![param("a", "Nat"), param("b", "Nat")],
            vec![eqn(call("le", vec![var("a"), var("b")]), tru())],
            call("le", vec![var("a"), s(var("b"))]),
            tru(),
        ),
        induct(
            "a",
            vec![
                case("Z", steps(vec![simp(Side::Lhs)], refl())), // le(Z, S b) = True
                case(
                    "S",
                    induct(
                        "b",
                        vec![
                            case("Z", absurd(premise(0))), // le(S _, Z) = True is false
                            case(
                                "S",
                                steps(
                                    vec![simp(Side::Lhs)], // le(S ka, S(S kb)) -> le(ka, S kb)
                                    rewrite_with(hyp(0), Dir::Lr, Side::Lhs, vec![demote(0)], refl()),
                                ),
                            ),
                        ],
                    ),
                ),
            ],
        ),
    )
}

/// forall a b, [le(a, b) = False] ⊢ nat_eq(a, b) = False  (a > b ⟹ a ≠ b)
pub fn nle_imp_neq() -> Theorem {
    theorem(
        "nle_imp_neq",
        forall_eq_cond(
            vec![param("a", "Nat"), param("b", "Nat")],
            vec![eqn(call("le", vec![var("a"), var("b")]), fls())],
            call("nat_eq", vec![var("a"), var("b")]),
            fls(),
        ),
        induct(
            "a",
            vec![
                case("Z", absurd(premise(0))), // le(Z, b) = False is contradictory
                case(
                    "S",
                    induct(
                        "b",
                        vec![
                            case("Z", steps(vec![simp(Side::Lhs)], refl())), // nat_eq(S _, Z) = False
                            case(
                                "S",
                                steps(
                                    vec![simp(Side::Lhs)],
                                    rewrite_with(hyp(0), Dir::Lr, Side::Lhs, vec![demote(0)], refl()),
                                ),
                            ),
                        ],
                    ),
                ),
            ],
        ),
    )
}

/// forall a b, [le(a, b) = False] ⊢ le(S(a), b) = False  (a > b ⟹ a+1 > b)
pub fn nle_imp_nle_succ() -> Theorem {
    theorem(
        "nle_imp_nle_succ",
        forall_eq_cond(
            vec![param("a", "Nat"), param("b", "Nat")],
            vec![eqn(call("le", vec![var("a"), var("b")]), fls())],
            call("le", vec![s(var("a")), var("b")]),
            fls(),
        ),
        induct(
            "a",
            vec![
                case("Z", absurd(premise(0))),
                case(
                    "S",
                    induct(
                        "b",
                        vec![
                            case("Z", steps(vec![simp(Side::Lhs)], refl())), // le(S(S _), Z) = False
                            case(
                                "S",
                                steps(
                                    vec![simp(Side::Lhs)], // le(S(S ka), S kb) -> le(S ka, kb)
                                    rewrite_with(hyp(0), Dir::Lr, Side::Lhs, vec![demote(0)], refl()),
                                ),
                            ),
                        ],
                    ),
                ),
            ],
        ),
    )
}

/// forall a b c, [le(a, b) = True, le(b, c) = True] ⊢ le(a, c) = True (transitivity)
///
/// The middle term `b` appears only in the premises, not the conclusion
/// `le(a, c)`, so matching the conclusion can't infer it. We pin it with `with`
/// (∀-instantiation): in the S/S/S case the pivot is the field var `$1` that
/// `induct b` introduces, so the IH (hyp 0) is specialized at `b := $1` before
/// its two premises are discharged.
pub fn le_trans() -> Theorem {
    theorem(
        "le_trans",
        forall_eq_cond(
            vec![param("a", "Nat"), param("b", "Nat"), param("c", "Nat")],
            vec![eqn(call("le", vec![var("a"), var("b")]), tru()), eqn(call("le", vec![var("b"), var("c")]), tru())],
            call("le", vec![var("a"), var("c")]),
            tru(),
        ),
        induct(
            "a",
            vec![
                case("Z", steps(vec![simp(Side::Lhs)], refl())), // le(Z, c) = True
                case(
                    "S",
                    induct(
                        "b",
                        vec![
                            case("Z", absurd(premise(0))), // le(S a, Z) = True is false
                            case(
                                "S",
                                induct(
                                    "c",
                                    vec![
                                        case("Z", absurd(premise(1))), // le(S b, Z) = True is false
                                        case(
                                            "S",
                                            steps(
                                                vec![simp(Side::Lhs)], // le(S ka, S kc) -> le(ka, kc)
                                                rewrite_with_inst(
                                                    hyp(0),
                                                    Dir::Lr,
                                                    Side::Lhs,
                                                    vec![("b", var("$1"))], // pin the pivot to the kb field var
                                                    vec![demote(0), demote(1)],
                                                    refl(),
                                                ),
                                            ),
                                        ),
                                    ],
                                ),
                            ),
                        ],
                    ),
                ),
            ],
        ),
    )
}

// --- conditional arithmetic building blocks for the reverse assembly. All
// follow the keystone double-induction pattern (boundary cases by `absurd`/simp,
// the recursive case discharges its IH via RewriteWith + `demote`). Unconditional
// helpers (sub_le_l, lt_eq_le_succ, neq_add_succ, add_lt_cancel_r, add_succ_r) are
// found by search and live in the theory these are checked against.

/// forall a b, [le(S(a), b) = True] ⊢ le(a, b) = True
pub fn le_succ_l() -> Theorem {
    theorem(
        "le_succ_l",
        forall_eq_cond(
            vec![param("a", "Nat"), param("b", "Nat")],
            vec![eqn(call("le", vec![s(var("a")), var("b")]), tru())],
            call("le", vec![var("a"), var("b")]),
            tru(),
        ),
        induct(
            "a",
            vec![
                case("Z", steps(vec![simp(Side::Lhs)], refl())),
                case(
                    "S",
                    induct(
                        "b",
                        vec![
                            case("Z", absurd(premise(0))),
                            case(
                                "S",
                                steps(vec![simp(Side::Lhs)], rewrite_with(hyp(0), Dir::Lr, Side::Lhs, vec![demote(0)], refl())),
                            ),
                        ],
                    ),
                ),
            ],
        ),
    )
}

/// forall a b, [le(a, b) = False] ⊢ nat_eq(b, a) = False
pub fn nle_imp_neq_sym() -> Theorem {
    theorem(
        "nle_imp_neq_sym",
        forall_eq_cond(
            vec![param("a", "Nat"), param("b", "Nat")],
            vec![eqn(call("le", vec![var("a"), var("b")]), fls())],
            call("nat_eq", vec![var("b"), var("a")]),
            fls(),
        ),
        induct(
            "a",
            vec![
                case("Z", absurd(premise(0))),
                case(
                    "S",
                    induct(
                        "b",
                        vec![
                            case("Z", steps(vec![simp(Side::Lhs)], refl())),
                            case(
                                "S",
                                steps(vec![simp(Side::Lhs)], rewrite_with(hyp(0), Dir::Lr, Side::Lhs, vec![demote(0)], refl())),
                            ),
                        ],
                    ),
                ),
            ],
        ),
    )
}

/// forall a b, [lt(a, b) = True] ⊢ le(a, b) = True
pub fn lt_imp_le() -> Theorem {
    theorem(
        "lt_imp_le",
        forall_eq_cond(
            vec![param("a", "Nat"), param("b", "Nat")],
            vec![eqn(call("lt", vec![var("a"), var("b")]), tru())],
            call("le", vec![var("a"), var("b")]),
            tru(),
        ),
        induct(
            "a",
            vec![
                case("Z", steps(vec![simp(Side::Lhs)], refl())),
                case(
                    "S",
                    induct(
                        "b",
                        vec![
                            case("Z", absurd(premise(0))),
                            case(
                                "S",
                                steps(vec![simp(Side::Lhs)], rewrite_with(hyp(0), Dir::Lr, Side::Lhs, vec![demote(0)], refl())),
                            ),
                        ],
                    ),
                ),
            ],
        ),
    )
}

/// forall p n, [le(p, n) = True] ⊢ le(S(n), p) = False  (p ≤ n ⟹ ¬(n+1 ≤ p))
pub fn lt_succ_nle() -> Theorem {
    theorem(
        "lt_succ_nle",
        forall_eq_cond(
            vec![param("p", "Nat"), param("n", "Nat")],
            vec![eqn(call("le", vec![var("p"), var("n")]), tru())],
            call("le", vec![s(var("n")), var("p")]),
            fls(),
        ),
        induct(
            "p",
            vec![
                case("Z", steps(vec![simp(Side::Lhs)], refl())), // le(S n, Z) = False
                case(
                    "S",
                    induct(
                        "n",
                        vec![
                            case("Z", absurd(premise(0))), // le(S kp, Z) = True is false
                            case(
                                "S",
                                steps(vec![simp(Side::Lhs)], rewrite_with(hyp(0), Dir::Lr, Side::Lhs, vec![demote(0)], refl())),
                            ),
                        ],
                    ),
                ),
            ],
        ),
    )
}

/// forall i k, [lt(Z, k) = True] ⊢ lt(i, add(i, k)) = True  (k > 0 ⟹ i < i+k)
pub fn lt_add_pos() -> Theorem {
    theorem(
        "lt_add_pos",
        forall_eq_cond(
            vec![param("i", "Nat"), param("k", "Nat")],
            vec![eqn(call("lt", vec![z(), var("k")]), tru())],
            call("lt", vec![var("i"), call("add", vec![var("i"), var("k")])]),
            tru(),
        ),
        induct(
            "i",
            vec![
                case("Z", steps(vec![simp(Side::Lhs), rewrite(premise(0), Dir::Lr, Side::Lhs)], refl())),
                case(
                    "S",
                    steps(
                        vec![simp(Side::Lhs)],
                        rewrite_with(
                            hyp(0),
                            Dir::Lr,
                            Side::Lhs,
                            vec![steps(vec![rewrite(premise(0), Dir::Lr, Side::Lhs)], refl())],
                            refl(),
                        ),
                    ),
                ),
            ],
        ),
    )
}

/// forall p n, [le(p, n) = True] ⊢ sub(S(n), p) = S(sub(n, p))
pub fn sub_succ_l() -> Theorem {
    theorem(
        "sub_succ_l",
        forall_eq_cond(
            vec![param("p", "Nat"), param("n", "Nat")],
            vec![eqn(call("le", vec![var("p"), var("n")]), tru())],
            call("sub", vec![s(var("n")), var("p")]),
            s(call("sub", vec![var("n"), var("p")])),
        ),
        induct(
            "p",
            vec![
                case("Z", steps(vec![simp(Side::Both)], refl())),
                case(
                    "S",
                    induct(
                        "n",
                        vec![
                            case("Z", absurd(premise(0))),
                            case(
                                "S",
                                steps(vec![simp(Side::Both)], rewrite_with(hyp(0), Dir::Lr, Side::Lhs, vec![demote(0)], refl())),
                            ),
                        ],
                    ),
                ),
            ],
        ),
    )
}

/// forall p c, [le(p, c) = True] ⊢ add(p, sub(c, p)) = c
pub fn add_sub_cancel() -> Theorem {
    theorem(
        "add_sub_cancel",
        forall_eq_cond(
            vec![param("p", "Nat"), param("c", "Nat")],
            vec![eqn(call("le", vec![var("p"), var("c")]), tru())],
            call("add", vec![var("p"), call("sub", vec![var("c"), var("p")])]),
            var("c"),
        ),
        induct(
            "p",
            vec![
                case("Z", steps(vec![simp(Side::Lhs)], refl())),
                case(
                    "S",
                    induct(
                        "c",
                        vec![
                            case("Z", absurd(premise(0))),
                            case(
                                "S",
                                steps(vec![simp(Side::Lhs)], rewrite_with(hyp(0), Dir::Lr, Side::Lhs, vec![demote(0)], refl())),
                            ),
                        ],
                    ),
                ),
            ],
        ),
    )
}

/// forall i c p, [le(p, c) = True] ⊢ sub(add(i, c), p) = add(i, sub(c, p))
pub fn sub_add_assoc() -> Theorem {
    theorem(
        "sub_add_assoc",
        forall_eq_cond(
            vec![param("i", "Nat"), param("c", "Nat"), param("p", "Nat")],
            vec![eqn(call("le", vec![var("p"), var("c")]), tru())],
            call("sub", vec![call("add", vec![var("i"), var("c")]), var("p")]),
            call("add", vec![var("i"), call("sub", vec![var("c"), var("p")])]),
        ),
        induct(
            "p",
            vec![
                case("Z", steps(vec![simp(Side::Both)], refl())),
                case(
                    "S",
                    induct(
                        "c",
                        vec![
                            case("Z", absurd(premise(0))),
                            case(
                                "S",
                                steps(
                                    // add(i, S kc) is stuck under sub until we expose its S.
                                    vec![rewrite(lemma("add_succ_r"), Dir::Lr, Side::Lhs), simp(Side::Both)],
                                    rewrite_with(hyp(0), Dir::Lr, Side::Lhs, vec![demote(0)], refl()),
                                ),
                            ),
                        ],
                    ),
                ),
            ],
        ),
    )
}

/// Discharge a premise subgoal `X = V` that is exactly the goal's premise `i`.
pub fn use_prem(i: usize) -> Proof {
    steps(vec![rewrite(premise(i), Dir::Lr, Side::Lhs)], refl())
}

/// Discharge a premise subgoal `X = V` that is exactly the in-scope hypothesis `i`.
pub fn use_hyp(i: usize) -> Proof {
    steps(vec![rewrite(hyp(i), Dir::Lr, Side::Lhs)], refl())
}

/// forall n p, [le(S(n), p) = True] ⊢ le(p, n) = False  (n+1 ≤ p ⟹ ¬(p ≤ n))
pub fn le_succ_nle() -> Theorem {
    theorem(
        "le_succ_nle",
        forall_eq_cond(
            vec![param("n", "Nat"), param("p", "Nat")],
            vec![eqn(call("le", vec![s(var("n")), var("p")]), tru())],
            call("le", vec![var("p"), var("n")]),
            fls(),
        ),
        induct(
            "p",
            vec![
                case("Z", absurd(premise(0))), // le(S n, Z) = True is false
                case(
                    "S",
                    induct(
                        "n",
                        vec![
                            case("Z", steps(vec![simp(Side::Lhs)], refl())), // le(S kp, Z) = False
                            case(
                                "S",
                                steps(vec![simp(Side::Lhs)], rewrite_with(hyp(0), Dir::Lr, Side::Lhs, vec![demote(0)], refl())),
                            ),
                        ],
                    ),
                ),
            ],
        ),
    )
}

/// forall a b c, [nat_eq(a, b) = True] ⊢ nat_eq(c, a) = nat_eq(c, b)
/// Congruence of `nat_eq` in its second argument (3-level induction on c, a, b).
pub fn nat_eq_congr_r() -> Theorem {
    let ab_inner = |zz: Proof, ss: Proof| {
        induct(
            "a",
            vec![
                case("Z", induct("b", vec![case("Z", zz.clone()), case("S", absurd(premise(0)))])),
                case("S", induct("b", vec![case("Z", absurd(premise(0))), case("S", ss)])),
            ],
        )
    };
    theorem(
        "nat_eq_congr_r",
        forall_eq_cond(
            vec![param("a", "Nat"), param("b", "Nat"), param("c", "Nat")],
            vec![eqn(call("nat_eq", vec![var("a"), var("b")]), tru())],
            call("nat_eq", vec![var("c"), var("a")]),
            call("nat_eq", vec![var("c"), var("b")]),
        ),
        induct(
            "c",
            vec![
                // c = Z: both sides reduce by a/b's shape; equal since a = b.
                case("Z", ab_inner(steps(vec![simp(Side::Both)], refl()), steps(vec![simp(Side::Both)], refl()))),
                // c = S kc: peel to nat_eq(kc, a) = nat_eq(kc, b); IH at the predecessors.
                case(
                    "S",
                    ab_inner(
                        steps(vec![simp(Side::Both)], refl()),
                        // IH's `b` is a spectator (only in its RHS); pin it to the b-field var $2.
                        steps(
                            vec![simp(Side::Both)],
                            rewrite_with_inst(hyp(0), Dir::Lr, Side::Lhs, vec![("b", var("$2"))], vec![demote(0)], refl()),
                        ),
                    ),
                ),
            ],
        ),
    )
}

/// forall m a b, [nat_eq(a, b) = True] ⊢ read(m, a) = read(m, b)
/// Read congruence: equal addresses read equal values (induction over memory;
/// the cell-tag comparison uses nat_eq_congr_r, the tail uses the IH).
pub fn read_congr() -> Theorem {
    theorem(
        "read_congr",
        forall_eq_cond(
            vec![param("m", "Mem"), param("a", "Nat"), param("b", "Nat")],
            vec![eqn(call("nat_eq", vec![var("a"), var("b")]), tru())],
            call("read", vec![var("m"), var("a")]),
            call("read", vec![var("m"), var("b")]),
        ),
        induct(
            "m",
            vec![
                case("MNil", steps(vec![simp(Side::Both)], refl())),
                case(
                    "MCell",
                    steps(
                        vec![simp(Side::Both)],
                        // RHS nat_eq(ka, b) -> nat_eq(ka, a); RHS read(rest, b) -> read(rest, a).
                        rewrite_with_inst(
                            lemma("nat_eq_congr_r"),
                            Dir::Rl,
                            Side::Rhs,
                            vec![("a", var("a"))],
                            vec![use_prem(0)],
                            rewrite_with_inst(
                                hyp(0),
                                Dir::Rl,
                                Side::Rhs,
                                vec![("a", var("a"))],
                                vec![use_prem(0)],
                                refl(),
                            ),
                        ),
                    ),
                ),
            ],
        ),
    )
}

/// forall a b, [le(S(a), b) = False] ⊢ le(b, a) = True  (¬(a < b) ⟹ b ≤ a)
pub fn nle_succ_imp_le() -> Theorem {
    theorem(
        "nle_succ_imp_le",
        forall_eq_cond(
            vec![param("a", "Nat"), param("b", "Nat")],
            vec![eqn(call("le", vec![s(var("a")), var("b")]), fls())],
            call("le", vec![var("b"), var("a")]),
            tru(),
        ),
        induct(
            "a",
            vec![
                case(
                    "Z",
                    induct(
                        "b",
                        vec![
                            case("Z", steps(vec![simp(Side::Lhs)], refl())),
                            case("S", absurd(premise(0))), // le(S Z, S kb)=F ⟹ le(Z,kb)=F, false
                        ],
                    ),
                ),
                case(
                    "S",
                    induct(
                        "b",
                        vec![
                            case("Z", steps(vec![simp(Side::Lhs)], refl())), // le(Z, S ka)=True
                            case(
                                "S",
                                steps(vec![simp(Side::Lhs)], rewrite_with(hyp(0), Dir::Lr, Side::Lhs, vec![demote(0)], refl())),
                            ),
                        ],
                    ),
                ),
            ],
        ),
    )
}

/// forall a b, [le(a, b) = True] ⊢ sub(a, b) = Z  (a ≤ b ⟹ a − b = 0)
pub fn sub_z_of_le() -> Theorem {
    theorem(
        "sub_z_of_le",
        forall_eq_cond(
            vec![param("a", "Nat"), param("b", "Nat")],
            vec![eqn(call("le", vec![var("a"), var("b")]), tru())],
            call("sub", vec![var("a"), var("b")]),
            z(),
        ),
        induct(
            "b",
            vec![
                case(
                    "Z",
                    induct(
                        "a",
                        vec![case("Z", steps(vec![simp(Side::Lhs)], refl())), case("S", absurd(premise(0)))],
                    ),
                ),
                case(
                    "S",
                    induct(
                        "a",
                        vec![
                            case("Z", steps(vec![simp(Side::Lhs)], refl())),
                            case(
                                "S",
                                steps(vec![simp(Side::Lhs)], rewrite_with(hyp(0), Dir::Lr, Side::Lhs, vec![demote(0)], refl())),
                            ),
                        ],
                    ),
                ),
            ],
        ),
    )
}

/// forall p n, [le(p, n) = False] ⊢ le(S(n), p) = True  (p > n ⟹ n+1 ≤ p)
pub fn nle_imp_le_succ() -> Theorem {
    theorem(
        "nle_imp_le_succ",
        forall_eq_cond(
            vec![param("p", "Nat"), param("n", "Nat")],
            vec![eqn(call("le", vec![var("p"), var("n")]), fls())],
            call("le", vec![s(var("n")), var("p")]),
            tru(),
        ),
        induct(
            "p",
            vec![
                case("Z", absurd(premise(0))),
                case(
                    "S",
                    induct(
                        "n",
                        vec![
                            case("Z", steps(vec![simp(Side::Lhs)], refl())),
                            case(
                                "S",
                                steps(vec![simp(Side::Lhs)], rewrite_with(hyp(0), Dir::Lr, Side::Lhs, vec![demote(0)], refl())),
                            ),
                        ],
                    ),
                ),
            ],
        ),
    )
}

/// forall a b, [le(a, b) = True, le(b, a) = True] ⊢ nat_eq(a, b) = True (antisym)
pub fn le_antisym() -> Theorem {
    theorem(
        "le_antisym",
        forall_eq_cond(
            vec![param("a", "Nat"), param("b", "Nat")],
            vec![eqn(call("le", vec![var("a"), var("b")]), tru()), eqn(call("le", vec![var("b"), var("a")]), tru())],
            call("nat_eq", vec![var("a"), var("b")]),
            tru(),
        ),
        induct(
            "a",
            vec![
                case(
                    "Z",
                    induct(
                        "b",
                        vec![case("Z", steps(vec![simp(Side::Lhs)], refl())), case("S", absurd(premise(1)))],
                    ),
                ),
                case(
                    "S",
                    induct(
                        "b",
                        vec![
                            case("Z", absurd(premise(0))),
                            case(
                                "S",
                                steps(vec![simp(Side::Lhs)], rewrite_with(hyp(0), Dir::Lr, Side::Lhs, vec![demote(0), demote(1)], refl())),
                            ),
                        ],
                    ),
                ),
            ],
        ),
    )
}

/// forall i n p, [le(i, p) = True, le(S(i), p) = False] ⊢ sub(S(add(i, n)), p) = S(n)
/// The low endpoint: when p = i, the mirror address is S(n). Premises pin p = i;
/// induction on i and p stays aligned (the S(add..) survives each peel).
pub fn mirror_lo() -> Theorem {
    theorem(
        "mirror_lo",
        forall_eq_cond(
            vec![param("i", "Nat"), param("n", "Nat"), param("p", "Nat")],
            vec![
                eqn(call("le", vec![var("i"), var("p")]), tru()),
                eqn(call("le", vec![s(var("i")), var("p")]), fls()),
            ],
            call("sub", vec![s(call("add", vec![var("i"), var("n")])), var("p")]),
            s(var("n")),
        ),
        induct(
            "i",
            vec![
                case(
                    "Z",
                    induct(
                        "p",
                        vec![
                            case("Z", steps(vec![simp(Side::Both)], refl())),
                            case("S", absurd(premise(1))), // le(S Z, S kp)=F is contradictory
                        ],
                    ),
                ),
                case(
                    "S",
                    induct(
                        "p",
                        vec![
                            case("Z", absurd(premise(0))), // le(S ki, Z)=T is false
                            case(
                                "S",
                                steps(vec![simp(Side::Lhs)], rewrite_with(hyp(0), Dir::Lr, Side::Lhs, vec![demote(0), demote(1)], refl())),
                            ),
                        ],
                    ),
                ),
            ],
        ),
    )
}

#[test]
fn proves_congruence_lemmas() {
    let m = module();
    let th = check_theory(&m, &[nat_eq_congr_r()]).unwrap();
    assert_eq!(check_theorem(&m, &Theory::default(), &nat_eq_congr_r()), Ok(()), "nat_eq_congr_r");
    assert_eq!(check_theorem(&m, &th, &read_congr()), Ok(()), "read_congr");
}

#[test]
fn proves_mirror_induction_lemmas() {
    let m = module();
    let th = building_block_theory();
    for thm in [sub_z_of_le(), nle_imp_le_succ(), le_antisym(), mirror_lo()] {
        assert_eq!(check_theorem(&m, &th, &thm), Ok(()), "{}", thm.name);
    }
}

#[test]
fn proves_arith_building_blocks() {
    let m = module();
    let th = building_block_theory();
    for thm in [
        le_succ_l(),
        nle_imp_neq_sym(),
        lt_imp_le(),
        lt_succ_nle(),
        lt_add_pos(),
        sub_succ_l(),
        add_sub_cancel(),
        sub_add_assoc(),
    ] {
        assert_eq!(check_theorem(&m, &th, &thm), Ok(()), "{}", thm.name);
    }
}

#[test]
fn proves_order_toolkit() {
    // The conditional order lemmas the reverse assembly leans on, hand-proved by
    // double/triple induction (the keystone pattern). Search can't reach these.
    let m = module();
    let th = Theory::default();
    for thm in [le_succ_r(), nle_imp_neq(), nle_imp_nle_succ(), le_trans()] {
        assert_eq!(check_theorem(&m, &th, &thm), Ok(()), "{}", thm.name);
    }
}

#[test]
fn proves_lt_imp_neq() {
    // The keystone conditional arithmetic lemma (and its symmetric form), proven
    // by hand — the piece the search provably cannot reach.
    let m = module();
    assert_eq!(check_theorem(&m, &Theory::default(), &lt_imp_neq()), Ok(()), "lt_imp_neq");
    assert_eq!(check_theorem(&m, &Theory::default(), &lt_imp_neq_sym()), Ok(()), "lt_imp_neq_sym");
}

#[test]
fn proves_basic_arithmetic() {
    let m = module();
    // dependency order so later lemmas can cite earlier ones
    let lemmas = [
        and_true_r(),
        and_false_r(),
        le_refl(),
        lt_irrefl(),
        le_succ_same(),
        lt_z(),
        le_lt_succ(),
        add_z_r(),
        le_z_eq(),
    ];
    assert!(check_theory(&m, &lemmas).is_ok());
}

#[test]
fn search_rediscovers_arithmetic_proofs() {
    // The automation layer: for each arithmetic lemma, throw away the hand
    // proof, search for one, and check that the FOUND proof is kernel-valid.
    let m = module();
    let lemmas = [
        and_true_r(),
        and_false_r(),
        le_refl(),
        lt_irrefl(),
        le_succ_same(),
        lt_z(),
        le_lt_succ(),
        add_z_r(),
        le_z_eq(),
    ];
    let mut proven: Vec<Theorem> = Vec::new();
    for thm in lemmas {
        let theory = check_theory(&m, &proven).unwrap();
        let found = find_proof(&m, &theory, &thm.claim, Limits::default());
        assert!(found.is_some(), "search failed to find a proof for {}", thm.name);
        let searched = Theorem { name: thm.name.clone(), claim: thm.claim.clone(), proof: found.unwrap() };
        assert_eq!(check_theorem(&m, &theory, &searched), Ok(()), "found proof invalid for {}", thm.name);
        proven.push(searched);
    }
}

#[test]
fn builds_reverse_toolkit_theory() {
    let _ = reverse_toolkit_theory();
}

/// forall i n p, [le(p, S(n)) = True] ⊢ sub(S(add(i, n)), p) = add(i, sub(S(n), p))
/// Rewrites the mirror address into a canonical `add(i, …)` form (algebraic:
/// add_succ_r to expose the S, then sub_add_assoc to pull `i` out).
pub fn mirror_form() -> Theorem {
    theorem(
        "mirror_form",
        forall_eq_cond(
            vec![param("i", "Nat"), param("n", "Nat"), param("p", "Nat")],
            vec![eqn(call("le", vec![var("p"), s(var("n"))]), tru())],
            call("sub", vec![s(call("add", vec![var("i"), var("n")])), var("p")]),
            call("add", vec![var("i"), call("sub", vec![s(var("n")), var("p")])]),
        ),
        steps(
            vec![rewrite(lemma("add_succ_r"), Dir::Rl, Side::Lhs)], // S(add i n) -> add(i, S n)
            rewrite_with(lemma("sub_add_assoc"), Dir::Lr, Side::Lhs, vec![use_prem(0)], refl()),
        ),
    )
}

/// forall i p c, [le(S(i), p) = True, le(p, c) = True] ⊢ lt(add(i, sub(c, p)), c) = True
/// (i < p ≤ c ⟹ i + (c−p) < c). Purely algebraic: build the RHS `True` up into
/// `lt(add(i,sub(c,p)), add(p,sub(c,p)))` (∀-instantiating the cancel's addend),
/// then collapse `add(p,sub(c,p))` back to `c`.
pub fn lt_add_sub() -> Theorem {
    theorem(
        "lt_add_sub",
        forall_eq_cond(
            vec![param("i", "Nat"), param("p", "Nat"), param("c", "Nat")],
            vec![
                eqn(call("le", vec![s(var("i")), var("p")]), tru()),
                eqn(call("le", vec![var("p"), var("c")]), tru()),
            ],
            call("lt", vec![call("add", vec![var("i"), call("sub", vec![var("c"), var("p")])]), var("c")]),
            tru(),
        ),
        steps(
            vec![
                rewrite(premise(0), Dir::Rl, Side::Rhs),           // True -> le(S i, p)
                rewrite(lemma("lt_eq_le_succ"), Dir::Rl, Side::Rhs), // le(S i, p) -> lt(i, p)
                rewrite_inst(
                    lemma("add_lt_cancel_r"),
                    Dir::Rl,
                    Side::Rhs,
                    vec![("k", call("sub", vec![var("c"), var("p")]))], // lt(i,p) -> lt(add(i,d), add(p,d))
                ),
            ],
            rewrite_with(lemma("add_sub_cancel"), Dir::Lr, Side::Rhs, vec![use_prem(1)], refl()),
        ),
    )
}

/// Prove `le(p, S(n)) = True` from the goal's premise `i` = `le(p, n) = True`.
pub fn le_p_succ_from(prem: usize) -> Proof {
    rewrite_with(lemma("le_succ_r"), Dir::Lr, Side::Lhs, vec![use_prem(prem)], refl())
}

/// forall i n p, [le(p, n) = True] ⊢ nat_eq(i, sub(S(add(i, n)), p)) = False
/// Interior, low side: the mirror address exceeds `i` (it is `i + (S n − p)` with
/// `S n − p > 0`), so it differs from `i`.
pub fn mirror_neq_i() -> Theorem {
    theorem(
        "mirror_neq_i",
        forall_eq_cond(
            vec![param("i", "Nat"), param("n", "Nat"), param("p", "Nat")],
            vec![eqn(call("le", vec![var("p"), var("n")]), tru())],
            call("nat_eq", vec![var("i"), call("sub", vec![s(call("add", vec![var("i"), var("n")])), var("p")])]),
            fls(),
        ),
        rewrite_with(
            lemma("mirror_form"),
            Dir::Lr,
            Side::Lhs,
            vec![le_p_succ_from(0)],
            // goal: nat_eq(i, add(i, sub(S n, p))) = False
            rewrite_with(
                lemma("lt_imp_neq"),
                Dir::Lr,
                Side::Lhs,
                vec![
                    // lt(i, add(i, sub(S n, p))) = True, since sub(S n, p) > 0
                    rewrite_with(
                        lemma("lt_add_pos"),
                        Dir::Lr,
                        Side::Lhs,
                        vec![rewrite_with(
                            lemma("sub_succ_l"),
                            Dir::Lr,
                            Side::Lhs,
                            vec![use_prem(0)],
                            steps(vec![simp(Side::Lhs)], refl()),
                        )],
                        refl(),
                    ),
                ],
                refl(),
            ),
        ),
    )
}

/// forall i n p, [le(S(i), p) = True, le(p, n) = True] ⊢
///   nat_eq(S(n), sub(S(add(i, n)), p)) = False
/// Interior, high side: the mirror address is below `S n` (it is `i + (S n − p)`
/// with `i < p`), so it differs from `S n`.
pub fn mirror_neq_succ() -> Theorem {
    theorem(
        "mirror_neq_succ",
        forall_eq_cond(
            vec![param("i", "Nat"), param("n", "Nat"), param("p", "Nat")],
            vec![
                eqn(call("le", vec![s(var("i")), var("p")]), tru()),
                eqn(call("le", vec![var("p"), var("n")]), tru()),
            ],
            call("nat_eq", vec![s(var("n")), call("sub", vec![s(call("add", vec![var("i"), var("n")])), var("p")])]),
            fls(),
        ),
        rewrite_with(
            lemma("mirror_form"),
            Dir::Lr,
            Side::Lhs,
            vec![le_p_succ_from(1)],
            // goal: nat_eq(S n, add(i, sub(S n, p))) = False
            rewrite_with(
                lemma("lt_imp_neq_sym"),
                Dir::Lr,
                Side::Lhs,
                vec![
                    // lt(add(i, sub(S n, p)), S n) = True  (mirror < S n since i < p)
                    rewrite_with(
                        lemma("lt_add_sub"),
                        Dir::Lr,
                        Side::Lhs,
                        vec![use_prem(0), le_p_succ_from(1)],
                        refl(),
                    ),
                ],
                refl(),
            ),
        ),
    )
}

/// forall i n p, [le(p, S(n)) = True, le(p, n) = False] ⊢ sub(S(add(i, n)), p) = i
/// The high endpoint: when p = S(n), the mirror address is `i`.
pub fn mirror_hi() -> Theorem {
    theorem(
        "mirror_hi",
        forall_eq_cond(
            vec![param("i", "Nat"), param("n", "Nat"), param("p", "Nat")],
            vec![
                eqn(call("le", vec![var("p"), s(var("n"))]), tru()),
                eqn(call("le", vec![var("p"), var("n")]), fls()),
            ],
            call("sub", vec![s(call("add", vec![var("i"), var("n")])), var("p")]),
            var("i"),
        ),
        rewrite_with(
            lemma("mirror_form"),
            Dir::Lr,
            Side::Lhs,
            vec![use_prem(0)],
            // goal: add(i, sub(S n, p)) = i
            rewrite_with(
                lemma("sub_z_of_le"),
                Dir::Lr,
                Side::Lhs,
                // sub(S n, p) = Z since S n <= p (because p > n)
                vec![rewrite_with(lemma("nle_imp_le_succ"), Dir::Lr, Side::Lhs, vec![use_prem(1)], refl())],
                steps(vec![rewrite(lemma("add_z_r"), Dir::Lr, Side::Lhs)], refl()), // add(i, Z) -> i
            ),
        ),
    )
}

/// forall n p, [le(p, S(n)) = True, le(p, n) = False] ⊢ nat_eq(S(n), p) = True
/// (n < p ≤ S n ⟹ p = S n), by antisymmetry.
pub fn eq_of_bounds() -> Theorem {
    theorem(
        "eq_of_bounds",
        forall_eq_cond(
            vec![param("n", "Nat"), param("p", "Nat")],
            vec![
                eqn(call("le", vec![var("p"), s(var("n"))]), tru()),
                eqn(call("le", vec![var("p"), var("n")]), fls()),
            ],
            call("nat_eq", vec![s(var("n")), var("p")]),
            tru(),
        ),
        rewrite_with(
            lemma("le_antisym"),
            Dir::Lr,
            Side::Lhs,
            // nat_eq(S n, p): need le(S n, p) = True and le(p, S n) = True
            vec![
                rewrite_with(lemma("nle_imp_le_succ"), Dir::Lr, Side::Lhs, vec![use_prem(1)], refl()),
                use_prem(0),
            ],
            refl(),
        ),
    )
}

#[test]
fn proves_mirror_lemmas() {
    let m = module();
    let th = reverse_toolkit_theory();
    for thm in [mirror_form(), lt_add_sub(), mirror_neq_i(), mirror_neq_succ(), mirror_hi(), eq_of_bounds()] {
        assert_eq!(check_theorem(&m, &th, &thm), Ok(()), "{}", thm.name);
    }
}

#[test]
fn search_builds_arith_and_mirror_theory() {
    // All 15 arithmetic + mirror lemmas, proved entirely by search.
    let _ = searched_arith_theory(&module());
}

/// Documents the search's capability boundary by asserting what it *cannot* do.
/// `lt_imp_neq`'s proof must apply its own conditional induction hypothesis
/// (`[lt(ka,kb)=True] ⊢ nat_eq(ka,kb)=False`) via `RewriteWith`. The search only
/// ever emits plain `Rewrite`, so it can never discharge the premise — at *any*
/// budget. This is why these were hand-proved, and it pinpoints the next search
/// feature: generate `RewriteWith` with recursive premise search.
#[test]
#[ignore = "slow (~2min): exhausts the search budget to confirm it cannot generate RewriteWith"]
fn search_cannot_reach_conditional_arithmetic() {
    let m = module();
    let theory = Theory::default();
    let nat2 = || vec![param("a", "Nat"), param("b", "Nat")];
    let conds = [
        // a < b  ⟹  a ≠ b
        ("lt_imp_neq", forall_eq_cond(nat2(), vec![eqn(call("lt", vec![var("a"), var("b")]), tru())], call("nat_eq", vec![var("a"), var("b")]), fls())),
        // a < b  ⟹  b ≠ a
        ("lt_imp_neq_sym", forall_eq_cond(nat2(), vec![eqn(call("lt", vec![var("a"), var("b")]), tru())], call("nat_eq", vec![var("b"), var("a")]), fls())),
    ];
    // A modest budget keeps this fast; the impossibility is structural (no
    // RewriteWith move exists), not a matter of search effort.
    for (name, claim) in conds {
        let found = find_proof(&m, &theory, &claim, Limits { depth: 8, nodes: 200_000 });
        assert!(found.is_none(), "search unexpectedly proved {name} — it now generates conditional-IH steps; update the ROADMAP capability note");
    }
}
