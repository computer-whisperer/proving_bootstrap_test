//! M3 — reasoning about an address-indexed mutable memory.
//!
//! What works here:
//! - A `Mem` (association list of (addr, val)) with `read`/`write`, admitted.
//! - The in-place reverse *executes* on the model (`[1,2,3] → [3,2,1]`).
//! - McCarthy read-over-write framing (`read_write`) — one-step `simp`.
//! - Induction *over memory structure* (`map_id_preserves_read`).
//! - Address-disequality arithmetic (`nat_neq_succ`).
//! - `case_on` over compound expressions (`and_idem`).
//!
//! The boundary we hit (see ROADMAP "M3 finding"): the *general* address-indexed
//! in-place reverse is NOT reachable with the current foundation. Its correctness
//! needs a framing lemma of the form `lt(a, b) = True ⊢ read(store/loop…, a)
//! unchanged`, i.e. an equation with a **precondition**. Our claims/lemmas are
//! unconditional, so `induct` cannot carry the precondition into the induction
//! hypothesis. `case_on` handles disequalities that arise *within* one goal, but
//! cannot supply a hypothesis to an IH. The precise next foundation piece is
//! conditional-premise equations, plus a small arithmetic library.

use proving_bootstrap::obj_lang::ast::*;
use proving_bootstrap::obj_lang::build::*;
use proving_bootstrap::obj_lang::builtins::prelude;
use proving_bootstrap::obj_lang::check::check_module;
use proving_bootstrap::proof::ast::*;
use proving_bootstrap::proof::build::*;
use proving_bootstrap::proof::check::{check_theorem, check_theory, ProofError, Theory};
use proving_bootstrap::proof::search::{find_proof, Limits};

/// Memory + arithmetic model. Addresses and words are `Nat` for now (machine
/// ints are a deliberate later step — see ROADMAP M3).
pub fn module() -> Module {
    let mut m = prelude();
    m.types.push(TypeDef {
        name: "Mem".into(),
        ctors: vec![
            CtorDef { name: "MNil".into(), fields: vec![] },
            CtorDef { name: "MCell".into(), fields: vec!["Nat".into(), "Nat".into(), "Mem".into()] },
        ],
    });
    m.fns = vec![
        // ite(c, x, y) = match c { True => x, False => y }
        fndef(
            "ite",
            vec![param("c", "Bool"), param("x", "Nat"), param("y", "Nat")],
            "Nat",
            match_(var("c"), vec![arm("True", &[], var("x")), arm("False", &[], var("y"))]),
        ),
        // and(p, q) = match p { True => q, False => False }
        fndef(
            "and",
            vec![param("p", "Bool"), param("q", "Bool")],
            "Bool",
            match_(var("p"), vec![arm("True", &[], var("q")), arm("False", &[], fls())]),
        ),
        // nat_eq(a, b)
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
                            vec![arm("Z", &[], fls()), arm("S", &["kb"], call("nat_eq", vec![var("ka"), var("kb")]))],
                        ),
                    ),
                ],
            ),
        ),
        // add(n, m)
        fndef(
            "add",
            vec![param("n", "Nat"), param("m", "Nat")],
            "Nat",
            match_(var("n"), vec![arm("Z", &[], var("m")), arm("S", &["k"], s(call("add", vec![var("k"), var("m")])))]),
        ),
        // pred(n) = n - 1 (saturating)
        fndef("pred", vec![param("n", "Nat")], "Nat", match_(var("n"), vec![arm("Z", &[], z()), arm("S", &["k"], var("k"))])),
        // lt(a, b) : a < b
        fndef(
            "lt",
            vec![param("a", "Nat"), param("b", "Nat")],
            "Bool",
            match_(
                var("a"),
                vec![
                    arm("Z", &[], match_(var("b"), vec![arm("Z", &[], fls()), arm("S", &["_kb"], tru())])),
                    arm(
                        "S",
                        &["ka"],
                        match_(
                            var("b"),
                            vec![arm("Z", &[], fls()), arm("S", &["kb"], call("lt", vec![var("ka"), var("kb")]))],
                        ),
                    ),
                ],
            ),
        ),
        // le(a, b) : a <= b
        fndef(
            "le",
            vec![param("a", "Nat"), param("b", "Nat")],
            "Bool",
            match_(
                var("a"),
                vec![
                    arm("Z", &[], tru()),
                    arm(
                        "S",
                        &["ka"],
                        match_(
                            var("b"),
                            vec![arm("Z", &[], fls()), arm("S", &["kb"], call("le", vec![var("ka"), var("kb")]))],
                        ),
                    ),
                ],
            ),
        ),
        // sub(a, b) = a - b (saturating), recursing on b
        fndef(
            "sub",
            vec![param("a", "Nat"), param("b", "Nat")],
            "Nat",
            match_(
                var("b"),
                vec![
                    arm("Z", &[], var("a")),
                    arm(
                        "S",
                        &["kb"],
                        match_(
                            var("a"),
                            vec![arm("Z", &[], z()), arm("S", &["ka"], call("sub", vec![var("ka"), var("kb")]))],
                        ),
                    ),
                ],
            ),
        ),
        // in_range(i, j, p) = i <= p && p <= j
        fndef(
            "in_range",
            vec![param("i", "Nat"), param("j", "Nat"), param("p", "Nat")],
            "Bool",
            call("and", vec![call("le", vec![var("i"), var("p")]), call("le", vec![var("p"), var("j")])]),
        ),
        // mirror(i, j, p) = i + j - p  (the reflected index within [i, j])
        fndef(
            "mirror",
            vec![param("i", "Nat"), param("j", "Nat"), param("p", "Nat")],
            "Nat",
            call("sub", vec![call("add", vec![var("i"), var("j")]), var("p")]),
        ),
        // expected(m, i, j, p): value at p after reversing [i, j] in place
        fndef(
            "expected",
            vec![param("m", "Mem"), param("i", "Nat"), param("j", "Nat"), param("p", "Nat")],
            "Nat",
            call(
                "ite",
                vec![
                    call("in_range", vec![var("i"), var("j"), var("p")]),
                    call("read", vec![var("m"), call("mirror", vec![var("i"), var("j"), var("p")])]),
                    call("read", vec![var("m"), var("p")]),
                ],
            ),
        ),
        // read(m, b) = match m { MNil => Z, MCell(a, v, rest) => ite(nat_eq(a, b), v, read(rest, b)) }
        fndef(
            "read",
            vec![param("m", "Mem"), param("b", "Nat")],
            "Nat",
            match_(
                var("m"),
                vec![
                    arm("MNil", &[], z()),
                    arm(
                        "MCell",
                        &["a", "v", "rest"],
                        call("ite", vec![call("nat_eq", vec![var("a"), var("b")]), var("v"), call("read", vec![var("rest"), var("b")])]),
                    ),
                ],
            ),
        ),
        // write(m, a, v) = MCell(a, v, m)
        fndef(
            "write",
            vec![param("m", "Mem"), param("a", "Nat"), param("v", "Nat")],
            "Mem",
            ctor("MCell", vec![var("a"), var("v"), var("m")]),
        ),
        // map_mem_id(m): rebuild the memory structure unchanged. A memory-
        // recursive transform, used to show induction *over memory* works.
        fndef(
            "map_mem_id",
            vec![param("m", "Mem")],
            "Mem",
            match_(
                var("m"),
                vec![
                    arm("MNil", &[], ctor("MNil", vec![])),
                    arm("MCell", &["a", "v", "rest"], ctor("MCell", vec![var("a"), var("v"), call("map_mem_id", vec![var("rest")])])),
                ],
            ),
        ),
        // swap(m, i, j) = write(write(m, i, read(m, j)), j, read(m, i))
        fndef(
            "swap",
            vec![param("m", "Mem"), param("i", "Nat"), param("j", "Nat")],
            "Mem",
            call(
                "write",
                vec![
                    call("write", vec![var("m"), var("i"), call("read", vec![var("m"), var("j")])]),
                    var("j"),
                    call("read", vec![var("m"), var("i")]),
                ],
            ),
        ),
        // rev_loop(m, i, j): while i < j, swap(i, j), then (i+1, j-1).
        // Recurses structurally on j (the right pointer is also the termination
        // measure), so no separate fuel parameter is needed.
        fndef(
            "rev_loop",
            vec![param("m", "Mem"), param("i", "Nat"), param("j", "Nat")],
            "Mem",
            match_(
                var("j"),
                vec![
                    arm("Z", &[], var("m")),
                    arm(
                        "S",
                        &["jp"],
                        match_(
                            call("lt", vec![var("i"), s(var("jp"))]),
                            vec![
                                arm("False", &[], var("m")),
                                arm(
                                    "True",
                                    &[],
                                    call(
                                        "rev_loop",
                                        vec![
                                            call("swap", vec![var("m"), var("i"), s(var("jp"))]),
                                            s(var("i")),
                                            var("jp"),
                                        ],
                                    ),
                                ),
                            ],
                        ),
                    ),
                ],
            ),
        ),
        // arr_from(m, start, count) = the list [read(m,start), read(m,start+1), ...]
        fndef(
            "arr_from",
            vec![param("m", "Mem"), param("start", "Nat"), param("count", "Nat")],
            "List",
            match_(
                var("count"),
                vec![
                    arm("Z", &[], nil()),
                    arm(
                        "S",
                        &["c"],
                        cons(
                            call("read", vec![var("m"), var("start")]),
                            call("arr_from", vec![var("m"), call("add", vec![var("start"), s(z())]), var("c")]),
                        ),
                    ),
                ],
            ),
        ),
        // append + rev (the functional spec)
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
    ];
    m
}

/// forall m a v b, read(write(m, a, v), b) = ite(nat_eq(a, b), v, read(m, b))
/// The McCarthy read-over-write axiom — all framing flows through this. With
/// the association-list memory it is a one-step `simp` proof.
pub fn read_write() -> Theorem {
    theorem(
        "read_write",
        forall_eq(
            vec![param("m", "Mem"), param("a", "Nat"), param("v", "Nat"), param("b", "Nat")],
            call("read", vec![call("write", vec![var("m"), var("a"), var("v")]), var("b")]),
            call("ite", vec![call("nat_eq", vec![var("a"), var("b")]), var("v"), call("read", vec![var("m"), var("b")])]),
        ),
        steps(vec![simp(Side::Both)], refl()),
    )
}

/// forall a, nat_eq(a, a) = True
pub fn nat_eq_refl() -> Theorem {
    theorem(
        "nat_eq_refl",
        forall_eq(vec![param("a", "Nat")], call("nat_eq", vec![var("a"), var("a")]), tru()),
        induct(
            "a",
            vec![
                case("Z", steps(vec![simp(Side::Lhs)], refl())),
                case("S", steps(vec![simp(Side::Lhs), rewrite(hyp(0), Dir::Lr, Side::Lhs)], refl())),
            ],
        ),
    )
}

/// forall m a v, read(write(m, a, v), a) = v  (read-after-write, same address)
pub fn read_after_write_same() -> Theorem {
    theorem(
        "read_after_write_same",
        forall_eq(
            vec![param("m", "Mem"), param("a", "Nat"), param("v", "Nat")],
            call("read", vec![call("write", vec![var("m"), var("a"), var("v")]), var("a")]),
            var("v"),
        ),
        steps(
            vec![
                rewrite(lemma("read_write"), Dir::Lr, Side::Lhs),
                rewrite(lemma("nat_eq_refl"), Dir::Lr, Side::Lhs),
                simp(Side::Lhs),
            ],
            refl(),
        ),
    )
}

/// forall a b, and(nat_eq(a, b), nat_eq(a, b)) = nat_eq(a, b)
/// Exercises `case_on` over a compound Bool expression (not a variable).
pub fn and_idem() -> Theorem {
    theorem(
        "and_idem",
        forall_eq(
            vec![param("a", "Nat"), param("b", "Nat")],
            call("and", vec![call("nat_eq", vec![var("a"), var("b")]), call("nat_eq", vec![var("a"), var("b")])]),
            call("nat_eq", vec![var("a"), var("b")]),
        ),
        case_on(
            call("nat_eq", vec![var("a"), var("b")]),
            "Bool",
            vec![
                case("True", steps(vec![rewrite_all(hyp(0), Dir::Lr, Side::Both), simp(Side::Lhs)], refl())),
                case("False", steps(vec![rewrite_all(hyp(0), Dir::Lr, Side::Both), simp(Side::Lhs)], refl())),
            ],
        ),
    )
}

/// forall m b, read(map_mem_id(m), b) = read(m, b)
/// A general proof *by induction over memory*: the recursive transform and
/// `read` both recurse on the `Mem` structure, so they align and no address
/// arithmetic is needed. Demonstrates the induction-over-memory machinery works.
pub fn map_id_preserves_read() -> Theorem {
    theorem(
        "map_id_preserves_read",
        forall_eq(
            vec![param("m", "Mem"), param("b", "Nat")],
            call("read", vec![call("map_mem_id", vec![var("m")]), var("b")]),
            call("read", vec![var("m"), var("b")]),
        ),
        induct(
            "m",
            vec![
                case("MNil", steps(vec![simp(Side::Both)], refl())),
                case("MCell", steps(vec![simp(Side::Both), rewrite(hyp(0), Dir::Lr, Side::Lhs)], refl())),
            ],
        ),
    )
}

/// forall a, nat_eq(a, S(a)) = False — an address-disequality fact, the kind the
/// (deferred) general in-place reverse needs to frame past writes.
pub fn nat_neq_succ() -> Theorem {
    theorem(
        "nat_neq_succ",
        forall_eq(vec![param("a", "Nat")], call("nat_eq", vec![var("a"), s(var("a"))]), fls()),
        induct(
            "a",
            vec![
                case("Z", steps(vec![simp(Side::Lhs)], refl())),
                case("S", steps(vec![simp(Side::Lhs), rewrite(hyp(0), Dir::Lr, Side::Lhs)], refl())),
            ],
        ),
    )
}

/// forall m a v b, [nat_eq(a, b) = False] ⊢ read(write(m, a, v), b) = read(m, b)
/// Read-after-write at a *different* address — a genuinely conditional framing
/// lemma. Proven using its own premise (via `EqRef::Premise`).
pub fn read_write_frame() -> Theorem {
    theorem(
        "read_write_frame",
        forall_eq_cond(
            vec![param("m", "Mem"), param("a", "Nat"), param("v", "Nat"), param("b", "Nat")],
            vec![eqn(call("nat_eq", vec![var("a"), var("b")]), fls())],
            call("read", vec![call("write", vec![var("m"), var("a"), var("v")]), var("b")]),
            call("read", vec![var("m"), var("b")]),
        ),
        steps(
            vec![
                simp(Side::Lhs),                          // -> ite(nat_eq(a,b), v, read(m,b))
                rewrite(premise(0), Dir::Lr, Side::Lhs),  // premise: nat_eq(a,b) = False
                simp(Side::Lhs),                          // ite(False, v, read(m,b)) -> read(m,b)
            ],
            refl(),
        ),
    )
}

/// forall xs, [Z = Z] ⊢ append(xs, Nil) = xs
/// A trivially-conditioned version of `append_nil`, to exercise that `induct`
/// produces a *conditional* induction hypothesis and that `RewriteWith`
/// discharges it (here by reflexivity).
pub fn append_nil_cond() -> Theorem {
    theorem(
        "append_nil_cond",
        forall_eq_cond(
            vec![param("xs", "List")],
            vec![eqn(z(), z())],
            call("append", vec![var("xs"), nil()]),
            var("xs"),
        ),
        induct(
            "xs",
            vec![
                case("Nil", steps(vec![simp(Side::Lhs)], refl())),
                case(
                    "Cons",
                    // simp -> Cons(h, append(t, Nil)); then use the conditional IH,
                    // discharging its [Z = Z] premise by refl.
                    steps(
                        vec![simp(Side::Lhs)],
                        rewrite_with(hyp(0), Dir::Lr, Side::Lhs, vec![refl()], refl()),
                    ),
                ),
            ],
        ),
    )
}

/// forall m, read(write(write(m, 0, 7), 1, 9), 0) = 7
/// USES `read_write_frame` (a conditional lemma) via `RewriteWith`, discharging
/// `nat_eq(1, 0) = False` with a sub-proof, then `read_after_write_same`.
pub fn frame_use() -> Theorem {
    theorem(
        "frame_use",
        forall_eq(
            vec![param("m", "Mem")],
            call(
                "read",
                vec![
                    call("write", vec![call("write", vec![var("m"), z(), nat(7)]), s(z()), nat(9)]),
                    z(),
                ],
            ),
            nat(7),
        ),
        rewrite_with(
            lemma("read_write_frame"),
            Dir::Lr,
            Side::Lhs,
            vec![steps(vec![simp(Side::Lhs)], refl())], // prove nat_eq(S(Z), Z) = False
            steps(vec![rewrite(lemma("read_after_write_same"), Dir::Lr, Side::Lhs)], refl()),
        ),
    )
}

// --- swap framing: how `swap(m, i, j)` affects each read. These are the memory
// lemmas the loop invariant rests on, and they exercise conditional framing.

/// read(swap(m, i, j), j) = read(m, i)
pub fn swap_at_j() -> Theorem {
    theorem(
        "swap_at_j",
        forall_eq(
            vec![param("m", "Mem"), param("i", "Nat"), param("j", "Nat")],
            call("read", vec![call("swap", vec![var("m"), var("i"), var("j")]), var("j")]),
            call("read", vec![var("m"), var("i")]),
        ),
        steps(
            vec![simp(Side::Lhs), rewrite(lemma("nat_eq_refl"), Dir::Lr, Side::Lhs), simp(Side::Lhs)],
            refl(),
        ),
    )
}

/// [nat_eq(j, i) = False] ⊢ read(swap(m, i, j), i) = read(m, j)
pub fn swap_at_i() -> Theorem {
    theorem(
        "swap_at_i",
        forall_eq_cond(
            vec![param("m", "Mem"), param("i", "Nat"), param("j", "Nat")],
            vec![eqn(call("nat_eq", vec![var("j"), var("i")]), fls())],
            call("read", vec![call("swap", vec![var("m"), var("i"), var("j")]), var("i")]),
            call("read", vec![var("m"), var("j")]),
        ),
        steps(
            vec![
                simp(Side::Lhs),
                rewrite(premise(0), Dir::Lr, Side::Lhs),
                simp(Side::Lhs),
                rewrite(lemma("nat_eq_refl"), Dir::Lr, Side::Lhs),
                simp(Side::Lhs),
            ],
            refl(),
        ),
    )
}

/// [nat_eq(j, p) = False, nat_eq(i, p) = False] ⊢ read(swap(m, i, j), p) = read(m, p)
pub fn swap_elsewhere() -> Theorem {
    theorem(
        "swap_elsewhere",
        forall_eq_cond(
            vec![param("m", "Mem"), param("i", "Nat"), param("j", "Nat"), param("p", "Nat")],
            vec![
                eqn(call("nat_eq", vec![var("j"), var("p")]), fls()),
                eqn(call("nat_eq", vec![var("i"), var("p")]), fls()),
            ],
            call("read", vec![call("swap", vec![var("m"), var("i"), var("j")]), var("p")]),
            call("read", vec![var("m"), var("p")]),
        ),
        steps(
            vec![
                simp(Side::Lhs),
                rewrite(premise(0), Dir::Lr, Side::Lhs),
                simp(Side::Lhs),
                rewrite(premise(1), Dir::Lr, Side::Lhs),
                simp(Side::Lhs),
            ],
            refl(),
        ),
    )
}

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
fn demote(i: usize) -> Proof {
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
fn use_prem(i: usize) -> Proof {
    steps(vec![rewrite(premise(i), Dir::Lr, Side::Lhs)], refl())
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

/// All conditional building blocks, checked against a searched theory that holds
/// the unconditional helpers they cite (add_succ_r, etc.).
fn building_block_theory() -> Theory {
    searched_arith_theory(&module())
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
#[ignore = "probe: which unconditional sub/add arithmetic lemmas can the search find?"]
fn probe_search_arith() {
    let m = module();
    let ab = || vec![param("a", "Nat"), param("b", "Nat")];
    let abk = || vec![param("a", "Nat"), param("b", "Nat"), param("k", "Nat")];
    let claims: Vec<(&str, ForallEq)> = vec![
        ("sub_le_l", forall_eq(ab(), call("le", vec![call("sub", vec![var("a"), var("b")]), var("a")]), tru())),
        ("lt_eq_le_succ", forall_eq(ab(), call("lt", vec![var("a"), var("b")]), call("le", vec![s(var("a")), var("b")]))),
        (
            "neq_add_succ",
            forall_eq(ab(), call("nat_eq", vec![var("a"), call("add", vec![var("a"), s(var("b"))])]), fls()),
        ),
        (
            "add_lt_cancel_r",
            forall_eq(
                abk(),
                call("lt", vec![call("add", vec![var("a"), var("k")]), call("add", vec![var("b"), var("k")])]),
                call("lt", vec![var("a"), var("b")]),
            ),
        ),
    ];
    // Build a theory of the already-proven arithmetic so search can cite it.
    let theory = searched_arith_theory(&m);
    for (name, claim) in claims {
        let found = find_proof(&m, &theory, &claim, Limits { depth: 8, nodes: 1_000_000 });
        eprintln!("{name}: {}", if found.is_some() { "FOUND" } else { "not found" });
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

/// All arithmetic + mirror lemmas the reverse needs, as (name, claim). Proofs
/// are found by search — that's the automation layer doing the lemma volume.
fn arith_claims() -> Vec<(String, ForallEq)> {
    let mut v: Vec<(String, ForallEq)> = [
        and_true_r(),
        and_false_r(),
        le_refl(),
        lt_irrefl(),
        le_succ_same(),
        lt_z(),
        le_lt_succ(),
        add_z_r(),
        nat_eq_refl(),
    ]
    .iter()
    .map(|t| (t.name.clone(), t.claim.clone()))
    .collect();

    let nat3 = || vec![param("i", "Nat"), param("j", "Nat"), param("p", "Nat")];
    let ab = || vec![param("a", "Nat"), param("b", "Nat")];
    v.push(("add_succ_r".into(), forall_eq(ab(), call("add", vec![var("a"), s(var("b"))]), s(call("add", vec![var("a"), var("b")])))));
    v.push(("sub_add_l".into(), forall_eq(ab(), call("sub", vec![call("add", vec![var("a"), var("b")]), var("a")]), var("b"))));
    v.push(("sub_add_r".into(), forall_eq(ab(), call("sub", vec![call("add", vec![var("a"), var("b")]), var("b")]), var("a"))));
    // mirror(i,j,i) = j ; mirror(i,j,j) = i ; mirror(i,S j,p) = mirror(S i,j,p)
    v.push(("mirror_at_i".into(), forall_eq(vec![param("i", "Nat"), param("j", "Nat")], call("mirror", vec![var("i"), var("j"), var("i")]), var("j"))));
    v.push(("mirror_at_j".into(), forall_eq(vec![param("i", "Nat"), param("j", "Nat")], call("mirror", vec![var("i"), var("j"), var("j")]), var("i"))));
    v.push((
        "mirror_step".into(),
        forall_eq(nat3(), call("mirror", vec![var("i"), s(var("j")), var("p")]), call("mirror", vec![s(var("i")), var("j"), var("p")])),
    ));
    // Unconditional sub/add helpers the reverse assembly cites (search finds all).
    let abk = || vec![param("a", "Nat"), param("b", "Nat"), param("k", "Nat")];
    v.push(("sub_le_l".into(), forall_eq(ab(), call("le", vec![call("sub", vec![var("a"), var("b")]), var("a")]), tru())));
    v.push(("lt_eq_le_succ".into(), forall_eq(ab(), call("lt", vec![var("a"), var("b")]), call("le", vec![s(var("a")), var("b")]))));
    v.push(("neq_add_succ".into(), forall_eq(ab(), call("nat_eq", vec![var("a"), call("add", vec![var("a"), s(var("b"))])]), fls())));
    v.push((
        "add_lt_cancel_r".into(),
        forall_eq(
            abk(),
            call("lt", vec![call("add", vec![var("a"), var("k")]), call("add", vec![var("b"), var("k")])]),
            call("lt", vec![var("a"), var("b")]),
        ),
    ));
    v
}

/// The full conditional toolkit, as a checked theory: searched unconditional
/// lemmas first, then the hand-proved conditional ones in dependency order.
/// Memoized — the search over the growing theory is the slow part.
fn reverse_toolkit_theory() -> Theory {
    use std::sync::OnceLock;
    static CACHE: OnceLock<Theory> = OnceLock::new();
    CACHE.get_or_init(build_reverse_toolkit_theory).clone()
}

fn build_reverse_toolkit_theory() -> Theory {
    let m = module();
    let mut proven: Vec<Theorem> = Vec::new();
    for (name, claim) in arith_claims() {
        let th = check_theory(&m, &proven).unwrap();
        let proof = find_proof(&m, &th, &claim, Limits::default())
            .unwrap_or_else(|| panic!("search failed for {name}"));
        proven.push(Theorem { name, claim, proof });
    }
    for thm in [
        lt_imp_neq(),
        lt_imp_neq_sym(),
        le_succ_r(),
        nle_imp_neq(),
        nle_imp_nle_succ(),
        le_trans(),
        le_succ_l(),
        nle_imp_neq_sym(),
        lt_imp_le(),
        lt_succ_nle(),
        lt_add_pos(),
        sub_succ_l(),
        add_sub_cancel(),
        sub_add_assoc(),
        sub_z_of_le(),
        nle_imp_le_succ(),
        le_antisym(),
        mirror_lo(),
        mirror_form(),
        lt_add_sub(),
        mirror_neq_i(),
        mirror_neq_succ(),
        mirror_hi(),
        eq_of_bounds(),
    ] {
        proven.push(thm);
    }
    check_theory(&m, &proven).unwrap()
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
fn le_p_succ_from(prem: usize) -> Proof {
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

/// Build a theory by searching a proof for each claim in order.
fn searched_arith_theory(m: &Module) -> Theory {
    let mut proven: Vec<Theorem> = Vec::new();
    for (name, claim) in arith_claims() {
        let theory = check_theory(m, &proven).unwrap();
        let proof = find_proof(m, &theory, &claim, Limits::default())
            .unwrap_or_else(|| panic!("search failed to find a proof for {name}"));
        proven.push(Theorem { name, claim, proof });
    }
    check_theory(m, &proven).unwrap()
}

#[test]
fn search_builds_arith_and_mirror_theory() {
    // All 15 arithmetic + mirror lemmas, proved entirely by search.
    let _ = searched_arith_theory(&module());
}

#[test]
#[ignore = "documents a search LIMIT: needs conditional-IH application (RewriteWith), which search does not generate"]
fn search_finds_conditional_arithmetic() {
    // lt_imp_neq's proof must apply its own conditional induction hypothesis
    // ([lt(ka,kb)=True] => nat_eq(ka,kb)=False) via RewriteWith. The search only
    // emits plain Rewrite, so it cannot discharge the premise and fails here.
    // This pinpoints the next search feature: generate RewriteWith with
    // recursive premise search.
    let m = module();
    // Minimal theory: these conditional facts need no prior lemmas (induct +
    // case + IH + ex-falso), and a big theory only adds noise rewrite candidates.
    let theory = Theory::default();
    let nat2 = || vec![param("a", "Nat"), param("b", "Nat")];
    let conds = [
        // a < b  ⟹  a ≠ b
        ("lt_imp_neq", forall_eq_cond(nat2(), vec![eqn(call("lt", vec![var("a"), var("b")]), tru())], call("nat_eq", vec![var("a"), var("b")]), fls())),
        // a < b  ⟹  b ≠ a
        ("lt_imp_neq_sym", forall_eq_cond(nat2(), vec![eqn(call("lt", vec![var("a"), var("b")]), tru())], call("nat_eq", vec![var("b"), var("a")]), fls())),
    ];
    for (name, claim) in conds {
        let found = find_proof(&m, &theory, &claim, Limits { depth: 8, nodes: 2_000_000 });
        assert!(found.is_some(), "search failed for {name}");
        let thm = Theorem { name: name.into(), claim: claim.clone(), proof: found.unwrap() };
        assert_eq!(check_theorem(&m, &theory, &thm), Ok(()), "invalid for {name}");
    }
}

/// The per-position loop invariant (the centerpiece). Claim only; proof TBD
/// (hand or search): read(rev_loop(m,i,j), p) = expected(m,i,j,p).
fn spec_claim() -> ForallEq {
    forall_eq(
        vec![param("m", "Mem"), param("i", "Nat"), param("j", "Nat"), param("p", "Nat")],
        call("read", vec![call("rev_loop", vec![var("m"), var("i"), var("j")]), var("p")]),
        call("expected", vec![var("m"), var("i"), var("j"), var("p")]),
    )
}

#[test]
fn search_finds_swap_framing() {
    // The swap framing lemmas are conditional; their proofs use premises +
    // nat_eq_refl + simp. Search should find them.
    let m = module();
    let theory = check_theory(&m, &[read_write(), nat_eq_refl()]).unwrap();
    for thm in [swap_at_j(), swap_at_i(), swap_elsewhere()] {
        let found = find_proof(&m, &theory, &thm.claim, Limits::default());
        assert!(found.is_some(), "search failed for {}", thm.name);
        let searched = Theorem { name: thm.name.clone(), claim: thm.claim.clone(), proof: found.unwrap() };
        assert_eq!(check_theorem(&m, &theory, &searched), Ok(()), "invalid for {}", thm.name);
    }
}

#[test]
#[ignore = "exploration harness: prints S-case goal shapes while authoring the spec proof"]
fn explore_spec_scase() {
    use proving_bootstrap::proof::check::{do_case_on, do_induct, run_steps, Sequent};

    let m = module();
    let theory = Theory::default();
    let claim = spec_claim();
    let seq0 = Sequent { vars: claim.vars, hyps: vec![], premises: vec![], lhs: claim.lhs, rhs: claim.rhs };

    let subs = do_induct(&m, &seq0, "j").unwrap();
    for (ctor, sub) in &subs {
        eprintln!("\n===== induct(j) case {ctor} =====\n{sub}");
        if ctor == "S" {
            // The loop guard governs the S case. jp is the fresh field var; find it.
            let jp = sub.vars[0].name.clone();
            let guard = call("lt", vec![var("i"), s(var(&jp))]);
            let branches = do_case_on(&m, sub, &guard, "Bool").unwrap();
            for (bctor, bsub) in &branches {
                eprintln!("\n----- case lt(i,S {jp})={bctor} -----");
                if bctor == "True" {
                    // Preamble: expose the guard, resolve it, apply the IH, align mirrors.
                    let th = searched_arith_theory(&m);
                    let pre = [
                        ("unfold rev_loop", unfold("rev_loop", Side::Lhs)),
                        ("simp Lhs (fire match S)", simp(Side::Lhs)),
                        ("rewrite guard True", rewrite(hyp(1), Dir::Lr, Side::Lhs)),
                        ("simp Lhs (fire match True)", simp(Side::Lhs)),
                        ("rewrite IH", rewrite(hyp(0), Dir::Lr, Side::Lhs)),
                        ("simp Both", simp(Side::Both)),
                        ("add_succ_r Rhs", rewrite(lemma("add_succ_r"), Dir::Lr, Side::Rhs)),
                    ];
                    let mut cur = bsub.clone();
                    for (label, step) in pre {
                        match run_steps(&m, &th, &cur, std::slice::from_ref(&step)) {
                            Ok(s2) => {
                                eprintln!("  [{label}] ->\n{s2}");
                                cur = s2;
                            }
                            Err(e) => {
                                eprintln!("  [{label}] ERROR {e:?}");
                                break;
                            }
                        }
                    }
                } else if let Ok(s2) = run_steps(&m, &theory, bsub, &[simp(Side::Both)]) {
                    eprintln!("  after simp(Both):\n{s2}");
                }
            }
        }
    }
}

#[test]
#[ignore = "exploratory: hybrid — induct on j by hand, search each case (rich theory)"]
fn search_attempts_spec() {
    use proving_bootstrap::proof::check::{do_induct, Sequent};
    use proving_bootstrap::proof::search::find_from_sequent;

    let m = module();
    let theory = searched_arith_theory(&m);
    let claim = spec_claim();
    let seq0 = Sequent { vars: claim.vars, hyps: vec![], premises: vec![], lhs: claim.lhs, rhs: claim.rhs };
    let subs = do_induct(&m, &seq0, "j").unwrap();
    let limits = Limits { depth: 16, nodes: 2_000_000 };
    for (ctor, sub) in &subs {
        let found = find_from_sequent(&m, &theory, sub, limits);
        eprintln!("induct(j) case {ctor}: {}", if found.is_some() { "FOUND" } else { "not found" });
    }
}

#[test]
fn module_is_admitted() {
    assert_eq!(check_module(&module()), Ok(()));
}

/// forall m, arr_from(rev_loop(m, 0, n-1), 0, n) = rev(arr_from(m, 0, n))
/// for a FIXED size n, but arbitrary memory contents. Concrete indices make
/// every nat_eq/lt reduce and the list structure concrete, so the whole
/// pipeline (loop → swap → framing → functional rev) computes under `simp`,
/// leaving only the symbolic values read(m,k) — which match on both sides.
fn reverse_fixed_size(n: u64) -> Theorem {
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
fn proves_swap_framing() {
    let theory = check_theory(&module(), &[read_write(), nat_eq_refl()]).unwrap();
    assert_eq!(check_theorem(&module(), &theory, &swap_at_j()), Ok(()), "swap_at_j");
    assert_eq!(check_theorem(&module(), &theory, &swap_at_i()), Ok(()), "swap_at_i");
    assert_eq!(check_theorem(&module(), &theory, &swap_elsewhere()), Ok(()), "swap_elsewhere");
}

#[test]
fn proves_conditional_framing_lemma() {
    assert_eq!(check_theorem(&module(), &Theory::default(), &read_write_frame()), Ok(()));
}

#[test]
fn inductive_conditional_lemma_with_conditional_ih() {
    assert_eq!(check_theorem(&module(), &Theory::default(), &append_nil_cond()), Ok(()));
}

#[test]
fn uses_conditional_lemma_via_rewrite_with() {
    let theory = check_theory(&module(), &[read_write(), nat_eq_refl(), read_after_write_same(), read_write_frame()]).unwrap();
    assert_eq!(check_theorem(&module(), &theory, &frame_use()), Ok(()));
}

#[test]
fn plain_rewrite_rejects_conditional_lemma() {
    // Trying to use the conditional read_write_frame as if unconditional (plain
    // Rewrite) would prove the FALSE unconditional read(write(m,a,v),b)=read(m,b).
    // The kernel must reject it.
    let theory = check_theory(&module(), &[read_write_frame()]).unwrap();
    let unsound = theorem(
        "unsound",
        forall_eq(
            vec![param("m", "Mem"), param("a", "Nat"), param("v", "Nat"), param("b", "Nat")],
            call("read", vec![call("write", vec![var("m"), var("a"), var("v")]), var("b")]),
            call("read", vec![var("m"), var("b")]),
        ),
        steps(vec![rewrite(lemma("read_write_frame"), Dir::Lr, Side::Lhs)], refl()),
    );
    assert_eq!(check_theorem(&module(), &theory, &unsound), Err(ProofError::RewriteNeedsPremises));
}

#[test]
fn ex_falso_from_constructor_clash() {
    // [Z = S(a)] is contradictory, so any goal holds.
    let bogus_premise = theorem(
        "exfalso1",
        forall_eq_cond(vec![param("a", "Nat")], vec![eqn(z(), s(var("a")))], z(), s(z())),
        absurd(premise(0)),
    );
    assert_eq!(check_theorem(&module(), &Theory::default(), &bogus_premise), Ok(()));
}

#[test]
fn ex_falso_after_simplifying_premise() {
    // [lt(Z, Z) = True] is contradictory once lt(Z,Z) reduces to False.
    let thm = theorem(
        "exfalso2",
        forall_eq_cond(vec![], vec![eqn(call("lt", vec![z(), z()]), tru())], z(), s(z())),
        absurd(premise(0)),
    );
    assert_eq!(check_theorem(&module(), &Theory::default(), &thm), Ok(()));
}

#[test]
fn rewrite_with_checks_premise_count() {
    let theory = check_theory(&module(), &[read_write(), nat_eq_refl(), read_after_write_same(), read_write_frame()]).unwrap();
    let bad = theorem(
        "bad",
        frame_use().claim,
        // read_write_frame has 1 premise; supply 0.
        rewrite_with(lemma("read_write_frame"), Dir::Lr, Side::Lhs, vec![], refl()),
    );
    assert_eq!(
        check_theorem(&module(), &theory, &bad),
        Err(ProofError::PremiseCountMismatch { expected: 1, got: 0 })
    );
}

#[test]
fn induction_over_memory_works() {
    assert_eq!(check_theorem(&module(), &Theory::default(), &map_id_preserves_read()), Ok(()), "map_id_preserves_read");
}

#[test]
fn address_disequality_is_provable() {
    assert_eq!(check_theorem(&module(), &Theory::default(), &nat_neq_succ()), Ok(()), "nat_neq_succ");
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

#[test]
fn proves_memory_framing_lemmas() {
    let m = module();
    // read_write needs nothing; chain the rest in dependency order.
    assert_eq!(check_theorem(&m, &Theory::default(), &read_write()), Ok(()), "read_write");
    assert_eq!(check_theorem(&m, &Theory::default(), &nat_eq_refl()), Ok(()), "nat_eq_refl");
    let theory = check_theory(&m, &[read_write(), nat_eq_refl()]).unwrap();
    assert_eq!(check_theorem(&m, &theory, &read_after_write_same()), Ok(()), "read_after_write_same");
}

#[test]
fn case_on_over_expression() {
    assert_eq!(check_theorem(&module(), &Theory::default(), &and_idem()), Ok(()));
}
