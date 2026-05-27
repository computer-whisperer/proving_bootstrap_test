# M3 Walkthrough — in-place reverse = `rev`

A map of the shapes in the M3 proof, so you can read `tests/common/` knowing
what each piece is for. This is the pilot's "smallest honest form of the real
dragon": mutation, framing, a loop invariant, and index arithmetic, all carried
through the trusted kernel. `ROADMAP.md` has the status and the dated findings;
this is the *why it is shaped this way*.

## The claim, in one line

```text
forall m n,  arr_from(rev_loop(m, 0, n−1), 0, n)  =  rev(arr_from(m, 0, n))
```

Read it as: take any memory `m`; run the imperative two-pointer reverse over
addresses `0 .. n−1` (`rev_loop`); read the buffer back out as a list
(`arr_from`). That equals the *functional* reverse of the buffer you started
with. `reverse_eq_rev` in `common/reverse.rs`.

The model under test is in `common/model.rs` — all admitted, no proofs:

- **memory** — `Mem` is an association list `MCell(addr, val, rest)`; `read`
  walks it returning the first matching cell (`ite(nat_eq(a,b), v, read(rest,b))`),
  `write` just conses a new cell on front. McCarthy semantics fall out for free.
- **the loop** — `rev_loop(m, i, j)` recurses *structurally on `j`*: if `i < j`,
  `swap` the ends and recurse on `(i+1, j−1)`; otherwise stop. No fuel parameter —
  the right pointer is also the termination measure, so totality stays syntactic.
- **`swap(m,i,j)`** = `write(write(m, i, read(m,j)), j, read(m,i))`.
- **the spec** — ordinary `append`/`rev`, plus list-extraction helpers
  `arr_from` (ascending reads), `arr_rev` (descending reads), and `read_refl_arr`
  (reads at reflected addresses) that the lift uses as stepping stones.

## Why a per-position invariant is unavoidable

The three things recurse on *different* arguments: `rev_loop` on the right
pointer `j`, `arr_from` on a count, `read`/`Mem` on memory structure. There is no
single induction that aligns them. So we cannot prove the top claim directly; we
prove a stronger, *positional* statement about the loop and then read it off.

The bridge is `expected(m, i, j, p)` (in `model.rs`): what *should* be at address
`p` after reversing the window `[i, j]` in place —

```text
expected(m,i,j,p) = if i ≤ p ≤ j  then read(m, i+j−p)   -- the mirror address
                                  else read(m, p)        -- untouched
```

`mirror(i,j,p) = (i+j) − p` is the reflection of `p` within `[i,j]`;
`in_range(i,j,p) = i ≤ p ∧ p ≤ j`.

## The centerpiece: the per-position invariant

```text
forall m i j p,  read(rev_loop(m, i, j), p)  =  expected(m, i, j, p)
```

`spec_claim` / `spec_proof` in `common/spec.rs`. The proof is `induct(j)`:

- **Z** (`j = 0`, loop does nothing) — found by the **search**
  (`find_from_sequent`). A genuine leaf; no reason to hand-write it.
- **S** (`j = S jp`) — `case_on` the loop guard `lt(i, S jp)`:
  - **False** — `i` already past the window, `rev_loop` returns `m` unchanged.
    The only in-range position is the degenerate fixed point `i = p = S jp`, where
    the mirror *is* `p`, so both sides read `read(m, p)`. `spec_false_branch`.
  - **True** — the body runs once. The `spec_true_preamble` unfolds one loop
    iteration, fires the swap, and applies the **induction hypothesis** to the
    recursive `rev_loop(swap(...), i+1, jp)` call, leaving a goal about
    `read(swap(m, i, S jp), mirror)` vs. `expected`. Then it fans into 5 regions.

### The 5 regions of the True branch

After one swap of the ends `i` and `S jp = j`, where position `p` sits decides
which value it sees. Picture the window:

```text
        i        i+1 ........ j-1        j = S jp
        |          (interior)            |
   p<i  •───swapped with j───┐    ┌──────• ───swapped with i
        └──────────┐         │    │
   ... each p in [i,j] reads its mirror (i+j)−p; outside, p is untouched ...
```

| region            | what happens                                              | builder |
|-------------------|-----------------------------------------------------------|---------|
| `p < i`           | below the window — swap doesn't touch it; both read `m[p]`| `region_p_lt_i` |
| `p = i`           | took `j`'s old value; mirror of `i` is `j` ✓              | `region_p_eq_i` |
| `i < p < j` (interior) | the recursive call (via IH) handled it; both read the mirror `m[M]` | `region_interior` |
| `p = j` (`= S jp`)| took `i`'s old value; mirror of `j` is `i` ✓             | `region_p_eq_succ_n` |
| `p > j`           | above the window — untouched; both read `m[p]`            | `region_p_gt_succ_n` |

Each region is discharged by the **swap framing** lemmas (`common/framing.rs`):
`swap_at_i`, `swap_at_j`, `swap_elsewhere` — which say exactly how `read(swap(...))`
resolves at, and away from, the two swapped addresses. *Framing is free here:*
`simp` unfolds `read(swap(m,i,j), p)` directly into nested `nat_eq`-guarded `ite`s,
so there is no separation logic and no explicit "permission" reasoning — the
association-list memory pays for itself. What the regions *do* need is the
**arithmetic** that the address comparisons come out the way the region assumes
(e.g. in the interior, the mirror is itself in range and distinct from the ends):
that is the order/`sub`/`add`/mirror toolkit in `common/arith.rs`.

## The arithmetic toolkit, and the one kernel change

`common/arith.rs` is ~40 lemmas: `le`/`lt` monotonicity, `sub`/`add` identities,
`nat_eq`/`read` congruence, and the "mirror" lemmas that pin down `i+j−p`. The
**unconditional** leaves (`le_add_r`, `add_succ_r`, …) are found by the search.
The **conditional** ones (`premise ⊢ conclusion`) are hand-proved by a uniform
move: induct the variable that turns a stuck premise into a refutable constructor
clash, then close that boundary with `Absurd` (ex-falso) and apply the conditional
IH with `RewriteWith`. The search *cannot* generate that step — it has no move
that produces a `RewriteWith` — which is the capability limit the kernel/search
split is meant to expose (see `search_finds_conditional_arithmetic`).

**∀-instantiation (the kernel change).** `Rewrite`/`RewriteWith` carry an optional
`with: Vec<(String, Expr)>` that pre-substitutes named ∀-variables before matching
(∀-elimination — sound, not a new axiom). It is needed whenever a lemma has a
**spectator** variable: one that appears only in its premises, never its
conclusion, so unifying against the conclusion can't infer it. The canonical case
is transitivity — `le_trans : le(a,b) ∧ le(b,c) ⊢ le(a,c)` — where the pivot `b`
is invisible in the conclusion `le(a,c)`; we pin it with `with`. It also rescues
`var = var` lemmas, which are otherwise unusable as rewrites (a bare variable
pattern matches everything).

> Lesson worth keeping: state structural endpoint facts with a *compound*
> conclusion, or reach them via congruence + ∀-instantiation — never as a bare
> `var = var`. And peel recursive calls with one-step "defining unfold as a
> rewrite" lemmas (`arr_from_cons`, `add_succ_l`, `le_succ_both`, `sub_succ_r`),
> because `simp` over-reduces and loses the shape the next step needs to match.

## Lifting the invariant to `arr_from = rev`

With the per-position invariant proven, `common/reverse.rs` connects it to the
functional `rev`. Both sides are driven to a common middle form, `arr_rev` (the
descending read list an in-place reverse produces):

```text
                 read_rev_full          arr_from_rev_eq_refl       read_refl_arr_eq
   read(rev_loop)  ───────────▶  reflected reads  ───────────▶  read_refl_arr  ───▶  arr_rev
                                                                                        ▲
   rev(arr_from(m,0,n))  ─────────────────────────────────────────────────────────────┘
                                              rev_arr_from
```

- `read_rev_full` specializes the invariant to a *full* reversal `[0, hi]`: every
  in-range position `p` reads the mirror `sub(hi, p)`.
- `arr_from_rev_eq_refl` pushes that through `arr_from`, so extracting positions
  `s .. s+count−1` of the reversed buffer is reading reflected addresses —
  i.e. equals `read_refl_arr`. (Precondition: the last position stays `≤ hi`.)
- `read_refl_arr_eq` collapses the reflected-read list to `arr_rev`.
- `rev_arr_from` independently proves `rev(arr_from(m,0,n)) = arr_rev(m,n)`
  (using `arr_from_snoc` + `rev_append`).

The capstone `reverse_eq_rev` is then just two `RewriteWith`s meeting at
`arr_rev`, discharging the small index side-conditions (`le(0+n, S(pred n))`,
`sub(pred n, 0) = pred n`) inline.

## Where to read, in order

1. `common/model.rs` — the definitions. Get `read`/`write`/`swap`/`rev_loop`,
   `expected`/`mirror`/`in_range`, and `arr_from`/`arr_rev`/`read_refl_arr` in
   your head first.
2. `common/framing.rs` — `read_write` (the axiom) and the three `swap_*` lemmas.
3. `common/arith.rs` — skim; it is volume. Note `lt_imp_neq` (the keystone
   double-induction), `le_trans` (the ∀-instantiation motive), and the `mirror_*`
   lemmas.
4. `common/spec.rs` — the centerpiece. `spec_claim`, then the five `region_*`
   builders, then `spec_proof`.
5. `common/reverse.rs` — the lift, ending at `reverse_eq_rev`.

`common/mod.rs` holds only the *theory assembly* (which lemmas are searched vs.
hand-proved, and the memoized `Theory` builders) and re-exports every builder
flat so each submodule can `use super::*`.

## Honest caveats

- The four heavy end-to-end proofs (`proves_per_position_spec`,
  `proves_spec_{true,false}_branch`, `proves_reverse_eq_rev_universal`) are
  `#[ignore]`d: they rebuild a search-constructed `Theory` on each run (~45s).
  They pass; they are just not in the default `cargo test`. Making them always-on
  means caching the searched leaf proofs (serialize the found `Proof`s) instead of
  re-searching — see ROADMAP "Later".
- Indices and words are `Nat`. Machine ints (i32, modular) are a deliberate
  separate step; fighting bitvector arithmetic *and* framing at once would have
  taught us nothing about framing, which was the determining question here.
