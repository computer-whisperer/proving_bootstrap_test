# Roadmap & Status

Staged plan toward the north-star demo. See `OVERVIEW.md` for the why.

## North-Star Demo

One end-to-end artifact that is the entire vision in miniature:

> A naive **spec** function + an optimized **implementation** + a
> machine-checked proof that they are extensionally equal:
> `forall x, impl(x) = spec(x)`.

Concrete candidate: **naive list reverse vs. accumulator reverse.**

```text
spec:  rev(Nil)        = Nil
       rev(Cons(h, t)) = append(rev(t), Cons(h, Nil))

impl:  fast(xs)        = go(xs, Nil)
       go(Nil, acc)    = acc
       go(Cons(h,t),acc) = go(t, Cons(h, acc))

goal:  forall xs, fast(xs) = rev(xs)
```

This is chosen because it forces the pedagogically interesting wrinkle:
**the proof does not go through by induction on `xs` directly.** You must
generalize — prove the stronger lemma `forall xs acc, go(xs, acc) =
append(rev(xs), acc)` first, then specialize. Hitting that wall is exactly the
"how do basic program structures become provable" lesson this pilot exists to
teach.

(`sum` recursive vs. fold-with-accumulator is the simpler backup if reverse is
too much for the first cut.)

## Milestones

### M0 — Object language + interpreter  ✅ done (2026-05-26)
- [x] AST (serde + JSON): inductive type decls, top-level fn defs, expressions
      (constructor application, fn application, variable, `match`/case). `ast.rs`
- [x] Built-in inductive types: `Bool`, `Nat`, `List`. `builtins.rs`
- [x] Structural-recursion checker + mutual-recursion ban + scope/arity
      well-formedness. `check.rs`
- [x] Reducer/normalizer (the shared reduction engine — see Trust in OVERVIEW),
      handles closed terms now, designed to extend to open terms in M1.
      `reduce.rs`
- [x] Demonstrate: evaluate closed terms; a concrete unit test (`test(xs) =
      list_eq(fast(xs), rev(xs))`) passes by eval. `tests/m0_object_language.rs`
- Deferred to when needed: type checker + `match` exhaustiveness (no typing in
  M0); open-term normalization (M1).

### M1 — Proof checker kernel  ✅ done (2026-05-26)
- [x] Claim representation: `ForallEq` = `forall vars, lhs = rhs` (the
      `t(x) = true` unit test is the case `rhs = True`). `proof/ast.rs`
- [x] Proof representation (serde + JSON): a `Proof` *tree* — `Refl | Then(step,
      rest) | Induct(var, cases)`. Induct is the only brancher. `proof/ast.rs`
- [x] Inference kit, realized as two reduction primitives + rewrite + induct,
      all driven explicitly by the script (strategy (a)):
      - `Unfold(func)` — one δ-layer; `Reduce` — ι to normal form. Both in the
        shared engine (`obj_lang::reduce`), both always terminate. `unfold`/
        `reduce` replace the single "eval" — see design note below.
      - `Rewrite(eq, dir, side)` — first-order match + capture-avoiding replace,
        citing an induction hypothesis (`Hyp(i)`) or a proven lemma (`Lemma`).
      - `Induct(var)` — kernel derives per-constructor subgoals and the IH(s)
        from the type's constructors.
- [x] `Theory` accumulates proven lemmas in order for later citation (the M2
      hook; M1 proofs use only the IH).
- [x] Demonstrate: `forall n, add(n, Z) = n` and `forall xs, append(xs, Nil) =
      xs` proven by induction. 3 negative tests reject bad proofs (non-reflexive
      close, missing induction case, dangling hypothesis ref).
      `tests/m1_proof_kernel.rs`

**M1 design note — why `unfold` + `reduce` instead of one `eval`.** The full
normalizer (`obj_lang::reduce::normalize`) is right for *closed* terms but on
*open* terms it would unfold a recursive call like `go(t, acc)` (with `t` free)
into a residual `match`, destroying the `go(t, acc)` shape the proof needs to
rewrite with the IH. So the kernel never full-normalizes open goals: `Unfold`
exposes recursion exactly one layer when asked, `Reduce` fires only
constructor-matches, and the script decides when to do each. Both are trivially
terminating, which keeps the kernel's termination story obvious. `case` (split
without an IH) was dropped from the kit — not needed for the demos and derivable;
re-add if a proof wants it.

### M2 — North star  ✅ done (2026-05-26)
- [x] Prove `forall xs, fast(xs) = rev(xs)` end-to-end through the kernel, as a
      4-theorem chain checked in dependency order:
      `append_nil`, `append_assoc`, `go_spec` (the generalized lemma), `fast_rev`.
      `tests/m2_reverse_equivalence.rs`
- [x] The generalization wall is real and was hit: `fast = rev` does **not** go
      through by induction on `xs` directly; you must first prove the stronger
      `forall xs acc, go(xs, acc) = append(rev(xs), acc)` (IH instantiated at
      `acc := Cons(h, acc)`), using `append_assoc` to reassociate. Exactly the
      lesson the pilot existed to teach.
- [x] Negative test: citing the lemmas against an empty `Theory` is rejected
      (`NoLemma`). Whole chain round-trips through JSON and re-checks.

**What M2 forced — the `simp` primitive.** The reverse proof needs a recursive
call like `append(b, c)` (with `b` a free variable) to *stay* in call form so it
can be rewritten, while `append(Cons(h,t), y)` must compute. `unfold` (all
occurrences) and `reduce_iota` are too blunt for this. So M2 added `simp`:
guarded δ+ι that unfolds a call only when its guard `match` fires on a
constructor, keeping genuinely stuck calls as `f(args)`. It is now the proof
workhorse; `unfold`/`reduce` remain for fine control. A termination bug surfaced
and was fixed: `simp` must **not** reduce under a stuck `match`'s arms (doing so
δ-unfolds recursive calls in the arm bodies forever).

### M3 — Bridge to hardware-realistic code (the chosen next direction)

Goal (set with the user): prove an **in-place array reverse over an
address-indexed mutable memory** equal to the functional `rev`. This is the
smallest honest form of the real dragon — mutation, framing, a loop invariant,
index arithmetic — and if it works, a narrow wasm interpreter becomes plausible.

Deliberate scoping: **`Nat` indices/words first; machine ints (i32, modular) are
a separate later step.** Fighting bitvector arithmetic *and* framing at once
would teach us nothing about the framing question, which is the determining one.
Memory is an address-indexed association list with `read`/`write` (the user
OK'd this stand-in); McCarthy read-over-write gives framing without separation
logic (sufficient for a single buffer).

QoL built first to make memory proofs bearable:
- [x] Goal-state visibility: `Display` for `Expr`/`Sequent` + `run_steps` to
      inspect intermediate goals while authoring. `obj_lang/ast.rs`, `proof/check.rs`
- [x] `case_on(expr, ty)` proof node — case-split on a compound expression (e.g.
      `nat_eq(a,b)`), each branch assuming `expr = C(…)`. `proof/{ast,check}.rs`
- [x] `rewrite_all` — rewrite every occurrence in one pass (memory terms repeat).

Foundation layer ✅ done (2026-05-26): `tests/m3_memory.rs`
- [x] Memory model (`Mem`, `read`, `write`, `ite`) + arithmetic (`lt`, `pred`,
      `add`, `nat_eq`) admitted.
- [x] Concrete in-place reverse **executes** on the model (`[1,2,3] → [3,2,1]`).
- [x] McCarthy `read_write` framing lemma (one-step `simp`), `nat_eq_refl`,
      `read_after_write_same`, and a `case_on` exercise (`and_idem`).
- [x] Induction *over memory structure* (`map_id_preserves_read`).
- [x] Address-disequality arithmetic (`nat_neq_succ`).

**M3 finding (2026-05-26): the general in-place reverse needs conditional
equations.** The pieces that don't need address arithmetic all prove cleanly
(above). The general `forall m n, arr(rev_loop(m, …), n) = rev(arr(m, n))` does
**not** go through, and the reason is precise and architectural, not a matter of
effort:

- The loop (`rev_loop`, recurses on fuel), the array extraction (`arr_from`,
  recurses on count), and the memory (recurses on structure) all recurse on
  *different* things, so correctness needs a positional/range invariant.
- That invariant is inherently **conditional**: a framing lemma like
  `lt(a, b) = True ⊢ read(store/loop…, a) = read(m, a)` (reads below the touched
  region are unchanged). Our `ForallEq` claims are *unconditional* equations.
- Therefore `induct` cannot carry the precondition into the induction
  hypothesis. `case_on` discharges disequalities that arise *within* a single
  goal, but cannot supply a hypothesis to an IH generated from a premise-less
  goal. This is the wall.

**Recommended next foundation piece:** conditional-premise equations —
`ForallEq` gains `premises: Vec<Equation>`; premises enter the sequent as usable
hyps; `induct` substitutes them into the IH; `rewrite` with a conditional lemma
discharges its premises (against current hyps or as subgoals). This is a natural
extension of the hypothesis machinery the kernel already has internally (the IH
*is* an assumed equation). With that plus a small arithmetic library
(`lt`-monotonicity, `lt ⟹ ≠`), the two-pointer reverse becomes tractable. It is
a real kernel change, so it is a decision to make deliberately, not ram in.

### Later / decide-after
- [ ] Machine ints (i32 bitvector type + modular-arithmetic lemma library).
- [ ] An instruction-set VM layer (decode/dispatch) for higher ISA fidelity.
- [ ] Property-based counterexample search over executable tests.
- [ ] Pluggable untrusted proof search behind the kernel (the LLM slot); a
      `simplify` step (simp + lemma set) is the first automation to add there.

## Crate Layout (decided)

Single crate, modules — least ceremony for a throwaway. The reducer lives in
`obj_lang` and is imported by `proof`, so the trust boundary ("kernel uses the
same reduction as the interpreter") is a module boundary.

```text
src/
  obj_lang/   AST, built-in types, structural-recursion check, reducer (semantics)
  proof/      goal + proof AST, the trusted checker (kernel)        [M1]
  bin/check.rs  load JSON object + proof files, run check, report yes/no  [M1]
examples/     the reverse demo (built via helpers, round-tripped through JSON)
```

## Authoring (decided)

JSON + Rust builder helpers; no parser. Demo terms are tiny; add a parser later
only if hand-building becomes the bottleneck.

## Open Questions / To Resolve Later

- **How much of the inference kit is "primitive" vs. derived.** Smaller kernel is
  better for trust; more primitives is faster to reach M2. Calibrate at M1.
- **Negative results matter too.** The checker must clearly *reject* invalid
  proofs and unprovable goals, not just accept valid ones — needs deliberate
  test cases, not only happy-path demos.
- **Open-term normalization for the kernel.** M0 ships a closed-term evaluator;
  M1 needs the same engine to normalize *open* terms (with free variables) for
  reasoning under `forall`. Reduction logic is factored so M1 extends it rather
  than forking it.

## Status

- 2026-05-26: Concept aligned (object/meta split, first-order + total + pure,
  kernel/search split, refinement framing). Docs written.
- 2026-05-26: **M0 complete** — object language, built-in types, totality
  checks, reduction engine. 6 tests pass, clippy clean.
- 2026-05-26: **M1 complete** — proof kernel (`unfold`/`reduce`/`rewrite`/
  `induct`), `Theory` lemma accumulation, two induction proofs + 3 negative
  tests.
- 2026-05-26: **M2 complete — north star reached.** `forall xs, fast(xs) =
  rev(xs)` proven end-to-end (4-theorem chain with the generalized `go_spec`
  lemma). Added the guarded `simp` reduction primitive. 18 tests total, clippy
  clean. The pilot has demonstrated its thesis: a naive spec, an optimized
  implementation, and a machine-checked proof they agree — algorithmic
  refinement in miniature.
- 2026-05-26: **M3 foundation done; general in-place reverse blocked on a
  precise wall.** Added QoL (`Display`/`run_steps`, `case_on`, `rewrite_all`)
  and an address-indexed memory. Proven: in-place reverse *executes*, McCarthy
  framing, induction-over-memory, address-disequality arithmetic (24 tests,
  clippy clean). Established by attempting it that the *general* in-place reverse
  needs **conditional-premise equations** — a real but well-scoped kernel
  extension. That is the decision point now.
