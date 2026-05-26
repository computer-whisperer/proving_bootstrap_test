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

### M2 — North star
- [ ] Prove `forall xs, fast(xs) = rev(xs)`, including the generalized lemma.
- [ ] This is the "done enough to judge the idea" point.

### M3 — Stretch / decide-after-M2 (likely out of pilot)
- [ ] Property-based counterexample search over executable tests (free, since
      tests are runnable `Bool` functions): run before proving, surface a failing
      input fast.
- [ ] Pluggable untrusted proof search behind the kernel (the slot an LLM fills).

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
  tests. 13 tests total, clippy clean. Next: M2 (the north-star reverse
  equivalence), which exercises lemma citation + hypothesis generalization.
