//! The object-language model under test: arithmetic (`add`/`sub`/`lt`/`le`/
//! `nat_eq`), an association-list memory (`Mem`/`read`/`write`), the in-place
//! reverse (`swap`/`rev_loop`), the functional spec (`append`/`rev`), and the
//! list-extraction helpers (`arr_from`/`arr_rev`/`read_refl_arr`). All admitted —
//! just the definitions everything else reasons about.

use super::*;

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
                            call("arr_from", vec![var("m"), s(var("start")), var("c")]),
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
        // arr_rev(m, count) = [read(m, count-1), read(m, count-2), …, read(m, 0)]
        // (the descending read list — what an in-place reverse produces).
        fndef(
            "arr_rev",
            vec![param("m", "Mem"), param("count", "Nat")],
            "List",
            match_(
                var("count"),
                vec![
                    arm("Z", &[], nil()),
                    arm("S", &["c"], cons(call("read", vec![var("m"), var("c")]), call("arr_rev", vec![var("m"), var("c")]))),
                ],
            ),
        ),
        // read_refl_arr(m, hi, s, count) = [read(m, hi-s), read(m, hi-(s+1)), …]
        // — reads at reflected addresses; recursion mirrors arr_from (increment s).
        fndef(
            "read_refl_arr",
            vec![param("m", "Mem"), param("hi", "Nat"), param("s", "Nat"), param("count", "Nat")],
            "List",
            match_(
                var("count"),
                vec![
                    arm("Z", &[], nil()),
                    arm(
                        "S",
                        &["c"],
                        cons(
                            call("read", vec![var("m"), call("sub", vec![var("hi"), var("s")])]),
                            call("read_refl_arr", vec![var("m"), var("hi"), s(var("s")), var("c")]),
                        ),
                    ),
                ],
            ),
        ),
    ];
    m
}

#[test]
fn module_is_admitted() {
    assert_eq!(check_module(&module()), Ok(()));
}
