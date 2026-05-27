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
use proving_bootstrap::proof::check::{check_theorem, check_theory, Theory};

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
        // rev_loop(m, i, j, fuel): while i < j, swap(i,j), i+1, j-1
        fndef(
            "rev_loop",
            vec![param("m", "Mem"), param("i", "Nat"), param("j", "Nat"), param("fuel", "Nat")],
            "Mem",
            match_(
                var("fuel"),
                vec![
                    arm("Z", &[], var("m")),
                    arm(
                        "S",
                        &["f"],
                        match_(
                            call("lt", vec![var("i"), var("j")]),
                            vec![
                                arm("False", &[], var("m")),
                                arm(
                                    "True",
                                    &[],
                                    call(
                                        "rev_loop",
                                        vec![
                                            call("swap", vec![var("m"), var("i"), var("j")]),
                                            call("add", vec![var("i"), s(z())]),
                                            call("pred", vec![var("j")]),
                                            var("f"),
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

#[test]
fn module_is_admitted() {
    assert_eq!(check_module(&module()), Ok(()));
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
            call("arr_from", vec![call("rev_loop", vec![mem0, z(), nat(2), nat(3)]), z(), nat(3)]),
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
