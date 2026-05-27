//! The per-position loop invariant — the centerpiece:
//!   read(rev_loop(m, i, j), p) = expected(m, i, j, p)
//! after reversing [i, j] in place, position p holds the mirror value when in
//! range and is untouched otherwise. Induction on j; the S-case splits on the
//! loop guard, and the True branch fans into 5 position regions.

use super::*;

/// The S-case loop variable `n` (the `induct(j)` field var $0).
pub fn nn() -> Expr {
    var("$0")
}

// --- The S-case True branch's 5 region leaves. Goal after the preamble:
//   LHS = ite(and(le(S i,p), le(p,$0)), INNER, OUTER)
//   RHS = ite(and(le(i,p), le(p,S$0)), read(m,M), read(m,p))   M = sub(S(add i $0), p)
// Hyps: 0=IH, 1=lt(i,S$0)=True, 2=le(p,$0)=B, 3=le(S i,p)/le(p,S$0)=B', 4=le(i,p)=B''.

/// i < p ≤ n: both sides read(m, M).
pub fn region_interior() -> Proof {
    steps(
        vec![rewrite_all(hyp(3), Dir::Lr, Side::Lhs), rewrite_all(hyp(2), Dir::Lr, Side::Lhs)],
        rewrite_with(
            lemma("le_succ_l"),
            Dir::Lr,
            Side::Rhs,
            vec![use_hyp(3)],
            rewrite_with(
                lemma("le_succ_r"),
                Dir::Lr,
                Side::Rhs,
                vec![use_hyp(2)],
                steps(
                    vec![simp(Side::Both)],
                    rewrite_with(
                        lemma("mirror_neq_succ"),
                        Dir::Lr,
                        Side::Lhs,
                        vec![use_hyp(3), use_hyp(2)],
                        rewrite_with(
                            lemma("mirror_neq_i"),
                            Dir::Lr,
                            Side::Lhs,
                            vec![use_hyp(2)],
                            steps(vec![simp(Side::Lhs)], refl()),
                        ),
                    ),
                ),
            ),
        ),
    )
}

/// p = i: LHS picks read(m, S n) (nat_eq(i,p)=T); RHS picks read(m, M)=read(m, S n).
pub fn region_p_eq_i() -> Proof {
    steps(
        vec![rewrite_all(hyp(3), Dir::Lr, Side::Lhs), rewrite_all(hyp(2), Dir::Lr, Side::Lhs), rewrite_all(hyp(4), Dir::Lr, Side::Rhs)],
        rewrite_with(
            lemma("le_succ_r"),
            Dir::Lr,
            Side::Rhs,
            vec![use_hyp(2)],
            rewrite_with(
                lemma("mirror_lo"),
                Dir::Lr,
                Side::Rhs,
                vec![use_hyp(4), use_hyp(3)],
                steps(
                    vec![simp(Side::Both)],
                    rewrite_with(
                        lemma("nle_imp_neq"),
                        Dir::Lr,
                        Side::Lhs,
                        vec![rewrite_with(lemma("lt_succ_nle"), Dir::Lr, Side::Lhs, vec![use_hyp(2)], refl())],
                        rewrite_with(
                            lemma("le_antisym"),
                            Dir::Lr,
                            Side::Lhs,
                            vec![use_hyp(4), rewrite_with(lemma("nle_succ_imp_le"), Dir::Lr, Side::Lhs, vec![use_hyp(3)], refl())],
                            steps(vec![simp(Side::Lhs)], refl()),
                        ),
                    ),
                ),
            ),
        ),
    )
}

/// p < i: both sides read(m, p).
pub fn region_p_lt_i() -> Proof {
    steps(
        vec![rewrite_all(hyp(3), Dir::Lr, Side::Lhs), rewrite_all(hyp(4), Dir::Lr, Side::Rhs)],
        steps(
            vec![simp(Side::Both)],
            rewrite_with(
                lemma("nle_imp_neq"),
                Dir::Lr,
                Side::Lhs,
                vec![rewrite_with(lemma("lt_succ_nle"), Dir::Lr, Side::Lhs, vec![use_hyp(2)], refl())],
                rewrite_with(
                    lemma("nle_imp_neq"),
                    Dir::Lr,
                    Side::Lhs,
                    vec![use_hyp(4)],
                    steps(vec![simp(Side::Lhs)], refl()),
                ),
            ),
        ),
    )
}

/// le(i, $0) = True, from hyp(1): lt(i, S $0) = True (via le_lt_succ).
pub fn le_i_n_proof() -> Proof {
    steps(vec![rewrite(lemma("le_lt_succ"), Dir::Rl, Side::Lhs), rewrite(hyp(1), Dir::Lr, Side::Lhs)], refl())
}

/// le(S i, p) = True in the p > S n region, via le_trans pivot S $0.
pub fn le_s_i_p_proof() -> Proof {
    rewrite_with_inst(
        lemma("le_trans"),
        Dir::Lr,
        Side::Lhs,
        vec![("b", s(nn()))],
        vec![
            steps(vec![simp(Side::Lhs), rewrite(lemma("le_lt_succ"), Dir::Rl, Side::Lhs), rewrite(hyp(1), Dir::Lr, Side::Lhs)], refl()),
            rewrite_with(lemma("nle_imp_le_succ"), Dir::Lr, Side::Lhs, vec![use_hyp(2)], refl()),
        ],
        refl(),
    )
}

/// p = S n: LHS picks read(m, i) (nat_eq(S n,p)=T); RHS picks read(m, M)=read(m, i).
pub fn region_p_eq_succ_n() -> Proof {
    steps(
        vec![
            rewrite_all(hyp(2), Dir::Lr, Side::Lhs),
            rewrite(lemma("and_false_r"), Dir::Lr, Side::Lhs),
            rewrite_all(hyp(3), Dir::Lr, Side::Rhs),
        ],
        rewrite_with_inst(
            lemma("le_trans"),
            Dir::Lr,
            Side::Rhs,
            vec![("b", nn())],
            vec![
                le_i_n_proof(),
                rewrite_with(lemma("le_succ_l"), Dir::Lr, Side::Lhs, vec![rewrite_with(lemma("nle_imp_le_succ"), Dir::Lr, Side::Lhs, vec![use_hyp(2)], refl())], refl()),
            ],
            rewrite_with(
                lemma("mirror_hi"),
                Dir::Lr,
                Side::Rhs,
                vec![use_hyp(3), use_hyp(2)],
                steps(
                    vec![simp(Side::Both)],
                    rewrite_with(lemma("eq_of_bounds"), Dir::Lr, Side::Lhs, vec![use_hyp(3), use_hyp(2)], steps(vec![simp(Side::Lhs)], refl())),
                ),
            ),
        ),
    )
}

/// p > S n: both sides read(m, p).
pub fn region_p_gt_succ_n() -> Proof {
    steps(
        vec![
            rewrite_all(hyp(2), Dir::Lr, Side::Lhs),
            rewrite(lemma("and_false_r"), Dir::Lr, Side::Lhs),
            rewrite_all(hyp(3), Dir::Lr, Side::Rhs),
            rewrite(lemma("and_false_r"), Dir::Lr, Side::Rhs),
            simp(Side::Both), // collapse dead ite(False, …) so nat_eq rewrites hit OUTER
        ],
        rewrite_with(
            lemma("nle_imp_neq_sym"),
            Dir::Lr,
            Side::Lhs,
            vec![use_hyp(3)],
            rewrite_with(
                lemma("lt_imp_neq"),
                Dir::Lr,
                Side::Lhs,
                vec![steps(vec![rewrite(lemma("lt_eq_le_succ"), Dir::Lr, Side::Lhs)], le_s_i_p_proof())],
                steps(vec![simp(Side::Lhs)], refl()),
            ),
        ),
    )
}

/// Preamble for the S-case True branch: expose the loop body, resolve the guard,
/// apply the IH, align the mirror address to the canonical sub(S(add i $0), p).
pub fn spec_true_preamble() -> Vec<Step> {
    vec![
        unfold("rev_loop", Side::Lhs),
        simp(Side::Lhs),
        rewrite(hyp(1), Dir::Lr, Side::Lhs),
        simp(Side::Lhs),
        rewrite(hyp(0), Dir::Lr, Side::Lhs),
        simp(Side::Both),
        rewrite(lemma("add_succ_r"), Dir::Lr, Side::Rhs),
    ]
}

/// The full S-case True branch: preamble + the 5-region case tree.
pub fn spec_true_branch() -> Proof {
    let le = |a: Expr, b: Expr| call("le", vec![a, b]);
    steps(
        spec_true_preamble(),
        case_on(
            le(var("p"), nn()),
            "Bool",
            vec![
                case(
                    "True",
                    case_on(
                        le(s(var("i")), var("p")),
                        "Bool",
                        vec![
                            case("True", region_interior()),
                            case(
                                "False",
                                case_on(le(var("i"), var("p")), "Bool", vec![case("True", region_p_eq_i()), case("False", region_p_lt_i())]),
                            ),
                        ],
                    ),
                ),
                case(
                    "False",
                    case_on(le(var("p"), s(nn())), "Bool", vec![case("True", region_p_eq_succ_n()), case("False", region_p_gt_succ_n())]),
                ),
            ],
        ),
    )
}

/// The S-case **False** branch (loop done immediately, i ≥ S n): rev_loop returns
/// `m`, so LHS = read(m, p). `expected` reads at `mirror` only inside the range,
/// which here forces the single fixed point i = p = S n, where mirror = p.
/// Hyps: 0 = IH, 1 = lt(i, S $0) = False.
pub fn spec_false_branch() -> Proof {
    let n = || var("$0");
    let le = |a: Expr, b: Expr| call("le", vec![a, b]);

    // le(i, $0) = False, from hyp(1): lt(i, S $0) = False (via le_lt_succ).
    let le_i_n_false = || steps(vec![rewrite(lemma("le_lt_succ"), Dir::Rl, Side::Lhs), rewrite(hyp(1), Dir::Lr, Side::Lhs)], refl());
    // le(S $0, i) = True (i ≥ S $0).
    let le_s0_i = || rewrite_with(lemma("nle_imp_le_succ"), Dir::Lr, Side::Lhs, vec![le_i_n_false()], refl());

    // Fixed point i = p = S $0: read(m, p) = read(m, M), with M = i and i = p.
    let fixed_point = {
        // le(p, $0) = False, needed by mirror_hi.
        let le_p_n_false = rewrite_with(
            lemma("le_succ_nle"),
            Dir::Lr,
            Side::Lhs,
            vec![rewrite_with_inst(lemma("le_trans"), Dir::Lr, Side::Lhs, vec![("b", var("i"))], vec![le_s0_i(), use_hyp(3)], refl())],
            refl(),
        );
        // nat_eq(i, p) = True (so read(m, i) = read(m, p)).
        let nat_eq_i_p = rewrite_with(
            lemma("le_antisym"),
            Dir::Lr,
            Side::Lhs,
            vec![
                use_hyp(3),
                rewrite_with_inst(lemma("le_trans"), Dir::Lr, Side::Lhs, vec![("b", s(n()))], vec![use_hyp(2), le_s0_i()], refl()),
            ],
            refl(),
        );
        steps(
            vec![rewrite_all(hyp(3), Dir::Lr, Side::Rhs), rewrite_all(hyp(2), Dir::Lr, Side::Rhs), simp(Side::Rhs)],
            rewrite_with(
                lemma("mirror_hi"),
                Dir::Lr,
                Side::Rhs,
                vec![use_hyp(2), le_p_n_false],
                rewrite_with_inst(lemma("read_congr"), Dir::Lr, Side::Rhs, vec![("b", var("p"))], vec![nat_eq_i_p], refl()),
            ),
        )
    };

    steps(
        vec![
            unfold("rev_loop", Side::Lhs),
            simp(Side::Lhs),
            rewrite(hyp(1), Dir::Lr, Side::Lhs),
            simp(Side::Both),
            rewrite(lemma("add_succ_r"), Dir::Lr, Side::Rhs),
        ],
        case_on(
            le(var("p"), s(n())),
            "Bool",
            vec![
                case(
                    "False",
                    steps(vec![rewrite_all(hyp(2), Dir::Lr, Side::Rhs), rewrite(lemma("and_false_r"), Dir::Lr, Side::Rhs), simp(Side::Rhs)], refl()),
                ),
                case(
                    "True",
                    case_on(
                        le(var("i"), var("p")),
                        "Bool",
                        vec![
                            case("False", steps(vec![rewrite_all(hyp(3), Dir::Lr, Side::Rhs), simp(Side::Rhs)], refl())),
                            case("True", fixed_point),
                        ],
                    ),
                ),
            ],
        ),
    )
}

#[test]
#[ignore = "checks the spec S-case False branch in isolation against its sub-sequent"]
fn proves_spec_false_branch() {
    use proving_bootstrap::proof::check::{check_sequent, do_case_on, do_induct, Sequent};
    let m = module();
    let theory = reverse_toolkit_theory();
    let claim = spec_claim();
    let seq0 = Sequent { vars: claim.vars, hyps: vec![], premises: vec![], lhs: claim.lhs, rhs: claim.rhs };
    let s_sub = do_induct(&m, &seq0, "j").unwrap().into_iter().find(|(c, _)| c == "S").unwrap().1;
    let guard = call("lt", vec![var("i"), s(var("$0"))]);
    let false_sub = do_case_on(&m, &s_sub, &guard, "Bool").unwrap().into_iter().find(|(c, _)| c == "False").unwrap().1;
    assert_eq!(check_sequent(&m, &theory, &false_sub, &spec_false_branch()), Ok(()));
}

#[test]
#[ignore = "checks the spec S-case True branch in isolation against its sub-sequent"]
fn proves_spec_true_branch() {
    use proving_bootstrap::proof::check::{check_sequent, do_case_on, do_induct, Sequent};
    let m = module();
    let theory = reverse_toolkit_theory();
    let claim = spec_claim();
    let seq0 = Sequent { vars: claim.vars, hyps: vec![], premises: vec![], lhs: claim.lhs, rhs: claim.rhs };
    let s_sub = do_induct(&m, &seq0, "j").unwrap().into_iter().find(|(c, _)| c == "S").unwrap().1;
    let guard = call("lt", vec![var("i"), s(var("$0"))]);
    let true_sub = do_case_on(&m, &s_sub, &guard, "Bool").unwrap().into_iter().find(|(c, _)| c == "True").unwrap().1;
    assert_eq!(check_sequent(&m, &theory, &true_sub, &spec_true_branch()), Ok(()));
}

/// The full per-position invariant proof: induct on j; the Z (loop-empty) case is
/// found by search; the S case splits on the loop guard into the True (body runs,
/// 5-region) and False (loop done, fixed point) branches.
pub fn spec_proof(m: &Module, theory: &Theory) -> Proof {
    use proving_bootstrap::proof::check::{do_induct, Sequent};
    use proving_bootstrap::proof::search::find_from_sequent;
    let claim = spec_claim();
    let seq0 = Sequent { vars: claim.vars, hyps: vec![], premises: vec![], lhs: claim.lhs, rhs: claim.rhs };
    let z_sub = do_induct(m, &seq0, "j").unwrap().into_iter().find(|(c, _)| c == "Z").unwrap().1;
    let z_proof = find_from_sequent(m, theory, &z_sub, Limits { depth: 10, nodes: 3_000_000 })
        .expect("search the spec Z case");
    induct(
        "j",
        vec![
            case("Z", z_proof),
            case(
                "S",
                case_on(
                    call("lt", vec![var("i"), s(var("$0"))]),
                    "Bool",
                    vec![case("True", spec_true_branch()), case("False", spec_false_branch())],
                ),
            ),
        ],
    )
}

#[test]
#[ignore = "the full universal-n per-position invariant (slow: builds the toolkit + searches Z)"]
fn proves_per_position_spec() {
    let m = module();
    let theory = reverse_toolkit_theory();
    let thm = Theorem { name: "rev_loop_spec".into(), claim: spec_claim(), proof: spec_proof(&m, &theory) };
    assert_eq!(check_theorem(&m, &theory, &thm), Ok(()), "per-position spec");
}

/// The per-position loop invariant (the centerpiece). Claim only; proof TBD
/// (hand or search): read(rev_loop(m,i,j), p) = expected(m,i,j,p).
pub fn spec_claim() -> ForallEq {
    forall_eq(
        vec![param("m", "Mem"), param("i", "Nat"), param("j", "Nat"), param("p", "Nat")],
        call("read", vec![call("rev_loop", vec![var("m"), var("i"), var("j")]), var("p")]),
        call("expected", vec![var("m"), var("i"), var("j"), var("p")]),
    )
}
