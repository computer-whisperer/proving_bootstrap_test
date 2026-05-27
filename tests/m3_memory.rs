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
    v
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
