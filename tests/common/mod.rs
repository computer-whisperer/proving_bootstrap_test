//! Shared M3 fixtures, re-exported flat so every themed submodule can `use
//! super::*` and reference any builder without a path. Read the submodules in
//! this order:
//!
//!   model.rs    — the object-language definitions under test
//!   framing.rs  — read/write + swap framing; kernel-feature demos
//!   arith.rs    — order/sub/add toolkit, congruence, the mirror lemmas
//!   spec.rs     — the per-position loop invariant (the centerpiece)
//!   reverse.rs  — arr_from = rev (the capstone)
//!
//! This module itself holds only the *theory assembly* — the builders that
//! stitch searched + hand-proved lemmas into checkable `Theory`s. See
//! `docs/M3-WALKTHROUGH.md` for the narrative.

pub mod arith;
pub mod framing;
pub mod model;
pub mod reverse;
pub mod spec;
pub mod wasm;

pub use proving_bootstrap::obj_lang::ast::*;
pub use proving_bootstrap::obj_lang::build::*;
pub use proving_bootstrap::obj_lang::builtins::prelude;
pub use proving_bootstrap::obj_lang::check::check_module;
pub use proving_bootstrap::proof::ast::*;
pub use proving_bootstrap::proof::build::*;
pub use proving_bootstrap::proof::check::{check_theorem, check_theory, ProofError, Theory};
pub use proving_bootstrap::proof::search::{find_proof, Limits};

pub use arith::*;
pub use framing::*;
pub use model::*;
pub use reverse::*;
pub use spec::*;
// `wasm::*` is intentionally not re-exported yet — nothing cross-module consumes
// the VM builders until the correctness proof lands. `pub mod wasm` above is
// enough to compile and run its tests.

// ===== theory assembly =====
// The glue that turns the lemma builders above into checkable `Theory`s:
// unconditional leaves are found by `search`, then the hand-proved conditionals
// are appended in dependency order. Memoized where the search is the slow part.

/// All conditional building blocks, checked against a searched theory that holds
/// the unconditional helpers they cite (add_succ_r, etc.).
pub fn building_block_theory() -> Theory {
    searched_arith_theory(&module())
}

/// All arithmetic + mirror lemmas the reverse needs, as (name, claim). Proofs
/// are found by search — that's the automation layer doing the lemma volume.
pub fn arith_claims() -> Vec<(String, ForallEq)> {
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
pub fn reverse_toolkit_theory() -> Theory {
    use std::sync::OnceLock;
    static CACHE: OnceLock<Theory> = OnceLock::new();
    CACHE.get_or_init(build_reverse_toolkit_theory).clone()
}

pub fn build_reverse_toolkit_theory() -> Theory {
    let m = module();
    check_theory(&m, &reverse_toolkit_theorems()).unwrap()
}

/// The full toolkit as an ordered theorem list (searched unconditional lemmas,
/// then hand-proved conditionals in dependency order).
pub fn reverse_toolkit_theorems() -> Vec<Theorem> {
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
        nle_succ_imp_le(),
        le_succ_nle(),
        le_antisym(),
        nat_eq_congr_r(),
        read_congr(),
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
    proven
}

/// Build a theory by searching a proof for each claim in order.
pub fn searched_arith_theory(m: &Module) -> Theory {
    let mut proven: Vec<Theorem> = Vec::new();
    for (name, claim) in arith_claims() {
        let theory = check_theory(m, &proven).unwrap();
        let proof = find_proof(m, &theory, &claim, Limits::default())
            .unwrap_or_else(|| panic!("search failed to find a proof for {name}"));
        proven.push(Theorem { name, claim, proof });
    }
    check_theory(m, &proven).unwrap()
}

/// A fast theory for the pure list/arith lemmas (no rev_loop spec needed).
pub fn list_theory() -> Theory {
    let m = module();
    let mut proven: Vec<Theorem> = Vec::new();
    let ab = || vec![param("a", "Nat"), param("b", "Nat")];
    let xs3 = || vec![param("xs", "List"), param("ys", "List"), param("zs", "List")];
    let searched: Vec<(&str, ForallEq)> = vec![
        ("add_z_r", add_z_r().claim),
        ("add_succ_r", forall_eq(ab(), call("add", vec![var("a"), s(var("b"))]), s(call("add", vec![var("a"), var("b")])))),
        ("le_add_r", forall_eq(ab(), call("le", vec![var("a"), call("add", vec![var("a"), var("b")])]), tru())),
        ("le_refl", le_refl().claim),
        ("append_nil", forall_eq(vec![param("xs", "List")], call("append", vec![var("xs"), nil()]), var("xs"))),
        (
            "append_assoc",
            forall_eq(
                xs3(),
                call("append", vec![call("append", vec![var("xs"), var("ys")]), var("zs")]),
                call("append", vec![var("xs"), call("append", vec![var("ys"), var("zs")])]),
            ),
        ),
    ];
    for (name, claim) in searched {
        let th = check_theory(&m, &proven).unwrap();
        let proof = find_proof(&m, &th, &claim, Limits::default()).unwrap_or_else(|| panic!("search failed {name}"));
        proven.push(Theorem { name: name.into(), claim, proof });
    }
    for thm in [sub_succ_r(), arr_from_cons(), arr_from_snoc(), rev_append(), rev_arr_from(), read_refl_arr_eq()] {
        proven.push(thm);
    }
    check_theory(&m, &proven).unwrap()
}

/// The complete theory for the capstone: toolkit + rev_loop_spec + the list lemmas.
pub fn full_theory() -> Theory {
    use std::sync::OnceLock;
    static CACHE: OnceLock<Theory> = OnceLock::new();
    CACHE.get_or_init(build_full_theory).clone()
}

pub fn build_full_theory() -> Theory {
    let m = module();
    let mut proven = reverse_toolkit_theorems();
    let ab = || vec![param("a", "Nat"), param("b", "Nat")];
    let xs3 = || vec![param("xs", "List"), param("ys", "List"), param("zs", "List")];
    let searched: Vec<(&str, ForallEq)> = vec![
        ("le_add_r", forall_eq(ab(), call("le", vec![var("a"), call("add", vec![var("a"), var("b")])]), tru())),
        ("append_nil", forall_eq(vec![param("xs", "List")], call("append", vec![var("xs"), nil()]), var("xs"))),
        (
            "append_assoc",
            forall_eq(
                xs3(),
                call("append", vec![call("append", vec![var("xs"), var("ys")]), var("zs")]),
                call("append", vec![var("xs"), call("append", vec![var("ys"), var("zs")])]),
            ),
        ),
    ];
    for (name, claim) in searched {
        let th = check_theory(&m, &proven).unwrap();
        let proof = find_proof(&m, &th, &claim, Limits::default()).unwrap_or_else(|| panic!("search failed {name}"));
        proven.push(Theorem { name: name.into(), claim, proof });
    }
    proven.push(le_succ_both());
    proven.push(add_succ_l());
    // rev_loop_spec, proven against the toolkit-so-far (its Z case is searched).
    let so_far = check_theory(&m, &proven).unwrap();
    proven.push(Theorem { name: "rev_loop_spec".into(), claim: spec_claim(), proof: spec_proof(&m, &so_far) });
    for thm in [sub_succ_r(), arr_from_cons(), arr_from_snoc(), rev_append(), rev_arr_from(), read_refl_arr_eq(), read_rev_full(), arr_from_rev_eq_refl()] {
        proven.push(thm);
    }
    check_theory(&m, &proven).unwrap()
}
