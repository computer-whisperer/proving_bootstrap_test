//! Memory framing — how `read` sees through `write` and `swap` — plus the
//! kernel-feature demonstrations (conditional premises, `RewriteWith`, ex-falso,
//! `case_on`). McCarthy read-over-write (`read_write`) is the axiom all framing
//! flows through; the three `swap_*` lemmas are what the loop invariant rests on.

use super::*;

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
