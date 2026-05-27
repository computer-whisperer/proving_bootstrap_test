# Provable Software — Pilot Overview

This is a throwaway pilot. The goal is not a shippable artifact; it is to learn,
by building, how basic program structures (recursion over inductive data) become
*provable*, and to find out whether the architecture sketched below feels right.
Expect to delete most of this in a few days. Optimize for clarity of the idea,
not durability of the code.

This doc is maintainer/agent-facing. It captures the *why* and the *shape*.
`ROADMAP.md` captures the staged plan and current status.

## Current Thesis

Two small languages and one trusted program:

```text
object language   — functions live here. The Device-Under-Test (DUT) functions,
                    AND the "unit tests", which are themselves functions that
                    should evaluate to `true` for every input.

proof language    — proofs live here. A proof is a series of operations that,
                    when run by the checker, establishes a claim ABOUT an
                    object-language function.

checker (kernel)  — the trusted program. Given a goal and a proof, it answers
                    yes/no: does this proof actually establish this goal under
                    the object language's semantics?
```

A "unit test" is a total function `t : Inputs -> Bool`. Saying the test *passes*
is the claim:

```text
forall x : Inputs,  t(x) = true
```

Concrete tests (`t` applied to a fixed input) are discharged for free: the
checker just evaluates them. The interesting work is the universal quantifier —
that needs a real proof, by case analysis and induction over the inductive
structure of the inputs.

This is a **two-level reflective system**: the object language is a *deep
embedding* — its programs are data the proof language inspects, unfolds, and
rewrites. The closest existing relatives are **ACL2** (a programming language
plus a separate prover that reasons about its definitions) and the **LCF
lineage** (a proof is a sequence of primitive inference steps; only valid
results can be constructed).

### Why this is not the dependent-types path

There is a well-known alternative — Curry-Howard systems (Coq/Lean/Agda) — where
proofs *are* programs and checking a proof *is* type-checking, with one language.
We are deliberately **not** doing that. We keep two languages because:

- The object language stays an ordinary, familiar total functional interpreter.
- The proof checker stays a recursive validator over a goal — no dependent type
  theory to implement.
- It matches the long-term vision (below), where the object language is a
  portable, introspectable data structure and proofs are separate artifacts.

The cost we accept: two languages and two semantics that must be kept in lockstep
(see "Trust" below).

## The Long-Term Vision (horizon, not pilot scope)

Recorded here because it explains the feature biases, not because we build it now.

High-level software design expressed as *formal requirements* (the unit tests
that must be proven true). Humans and LLMs then write library/application code
**and proofs** that satisfy those requirements. The bet that makes this timely:

> Code is cheap; coherent, expressive, *proven* requirements are the scarce
> resource. An LLM is good at *proposing* an implementation or a proof; a
> checker is exactly what is needed to make that untrusted output *trustworthy*.
> The generate-and-check asymmetry is the whole product.

This reframes a 40-year-old idea — **refinement** (Dijkstra/Back/Morgan's
refinement calculus): there is a single relation `spec ⊑ impl` ("impl refines
spec"), it is transitive, and you chain `spec ⊑ … ⊑ code`, proving each step.
Under this lens:

- requirements → code, and code → machine code, are **the same operation** at
  different levels. Verified compilers (CompCert, CakeML) already prove the
  lower half as exactly this kind of composed refinement.
- Languages like Rust/C tangle "this is the algorithm" with "this is how to
  fulfill it efficiently." Compilers are hard precisely because there is no 1:1
  mapping between those two. The alternative bet here: make the lowering an
  **explicit, proven artifact** instead of leaving a "sufficiently smart
  compiler" to guess it.
- A pure algorithm becomes *portable*: copy its high-level expression (as tests)
  into a new project, then create and prove a lowering for that target.

The refinement-derivation programs of the 80s–2000s (Specware/Kestrel) stalled
because a *human* writing every refinement was brutally laborious. LLMs invert
that economics. That is the "why now."

## Architecture

```text
        +------------------------+
        |   object language      |   total, pure, first-order
        |   - AST (serde/json)   |   inductive data + structural recursion
        |   - reducer/evaluator  |---------+
        +------------------------+         | SHARED reduction engine
                                           | (single source of truth)
        +------------------------+         |
        |   proof checker        |<--------+
        |   (TRUSTED KERNEL)     |
        |   goal + proof -> y/n  |
        +------------------------+
                  ^
                  | proposes proofs (untrusted, swappable)
        +------------------------+
        |   search / tactics     |   later: an LLM slots in here
        |   (UNTRUSTED)          |
        +------------------------+
```

### Trust

The trusted base is: the checker's inference rules **plus** the object
language's operational semantics (because proofs reason about how functions
reduce). The soundness promise is:

> If the checker says yes, then `forall x, t(x) = true` genuinely holds when the
> interpreter runs `t`.

**The sharpest risk: the prover's model of reduction must equal the
interpreter's actual reduction.** If they ever diverge, you can "prove" things
that are operationally false. Therefore a hard rule: the checker's `eval`/
`unfold` steps call the *same* reduction engine the interpreter uses. One source
of truth for the object language's semantics — shared code, not a
re-implementation.

### The minimal logic

Logical structure (`and`/`or`/`not`/`implies`) lives **inside the object
language** as ordinary computable `Bool` functions. The *meta* logic therefore
needs only:

- **equality** between object-language terms (`=`),
- **universally-quantified equations** (the goal's quantified variables), and
- **conditional premises** — `premises ⊢ lhs = rhs` (added in M3, when framing a
  mutable memory forced "this holds *when* `a ≠ b`"; premises enter the sequent as
  usable hypotheses and `induct` carries them into the induction hypothesis).

proven by a small fixed kit of inference steps (as realized in `proof/`):

- `simp` — guarded δ+ι reduction via the shared engine: unfold a call only where
  its guard `match` fires on a constructor, keeping stuck calls as `f(args)`.
  The workhorse.
- `unfold` / `reduce` — one δ-layer / ι-only, for the rare cases `simp` is too
  coarse or too eager.
- `rewrite` by a known equation (an induction hypothesis, a proven lemma, or one
  of the goal's own premises), via first-order matching + capture-avoiding
  replacement. Carries an optional `with` to instantiate ∀-variables before
  matching (∀-elimination — needed for lemmas with a "spectator" variable, like
  the pivot in transitivity).
- `induct` on a variable: the kernel generates the base/step subgoals from the
  type's constructors and supplies the induction hypothesis as a rewritable
  equation.
- `case_on(expr, ty)` — split on a compound `Bool`/inductive expression (no
  hypothesis), each branch assuming `expr = C(…)`. (The original `case` sketch was
  dropped; `case_on` is its compound-scrutinee replacement, added for memory proofs.)
- `rewrite_with` — rewrite by a *conditional* lemma, discharging each instantiated
  premise with a sub-proof. A plain `rewrite` rejects conditional lemmas, so a
  precondition can never be silently skipped.
- `absurd` — ex-falso: a cited ground assumption that `simp`s to a constructor
  clash (e.g. `lt(Z,Z) = True`) closes any goal. Lets contradictory boundary
  premises discharge a case.

This kit proves `forall n, add(n, Z) = n`, `forall xs, append(xs, []) = xs`, the
north-star equivalence (`fast = rev`), and the full M3 result — an in-place array
reverse over a mutable memory equal to functional `rev` (see `M3-WALKTHROUGH.md`).

## Design Decisions (pilot)

1. **Object language is first-order.** Functions are top-level named definitions
   only; no lambdas as runtime values. This kills the hardest part of a
   reflective system — representing binders / avoiding variable capture when the
   meta level manipulates object terms. Variables appear only as parameters.
2. **Object language is total.** Recursion is restricted to **structural
   recursion** (recursive calls on a structurally-smaller argument). Totality is
   then syntactic — no separate termination prover needed. (ACL2 proves
   termination at definition time; we take the simpler structural-only rule.)
3. **Object language is pure.** No effects, no IO. Equational reasoning works.
4. **Kernel / search split is the product thesis, not just hygiene.** The
   checker is tiny and trusted; proof *search* is separate, untrusted, and
   swappable (an LLM eventually lives there).
5. **ASTs persist as serde + JSON** for both languages. The object-language AST
   is the crown jewel — clean, serializable, easily manipulated — because the
   long-term value (portability, LLM manipulation, refinement) all runs through
   it. Worth over-investing in even for a throwaway.
6. **`impl ⊑ spec` is first-class.** The provable claim is `forall x, impl(x) =
   spec(x)`; a plain unit test is the degenerate case where `spec` ≡ "returns
   true".
7. **Proofs are serializable artifacts** (proof-carrying), since portable
   *proofs* matter as much as portable specs.

## Known Hard Parts (dragons — flagged, mostly out of pilot scope)

- **Data refinement is the dragon.** Proving `naive(x) = optimized(x)` where both
  use the *same* types (the O(n²)→O(n) kind) is tractable and is the pilot's
  target. Proving a lowering that *changes the data representation* (abstract set
  → sorted array → packed buffer) is where refinement gets genuinely hard. Pilot
  does algorithmic refinement only.
- **Efficiency is not a Bool property.** `forall x, t(x) = true` proves a lowering
  *correct*, never *fast*. The framework gatekeeps correctness; choosing an
  efficient lowering is left to the engineer/LLM. A cost/resource-bound layer is
  future work.
- **Spec adequacy.** "Proven" means "satisfies the stated tests", not "correct"
  in the intuitive sense — a weak `t` admits garbage that still passes. The
  accretion model (pile up discriminating tests, prove each) is the incremental
  answer, but spec quality stays a human responsibility. This matters doubly for
  LLM-written code.
- **The spec boundary.** Portability works only if a spec is statable without
  dragging in the whole world. *What a unit-test function may mention* (its
  dependency surface) is the design axis the long-term vision lives or dies on.
  Too early to solve; flagged so we do not paint ourselves into a corner.

## Glossary

- **Object language / meta language** — the language being reasoned about vs. the
  language doing the reasoning.
- **Deep embedding** — representing object-language programs as data the meta
  level can inspect, rather than as opaque host functions.
- **Normalization / reduction** — evaluating a term to its simplest form. For a
  total language, a closed term always normalizes to a value.
- **Inductive type** — a data type defined by constructors (e.g. `Nat = Z |
  S(Nat)`, `List = Nil | Cons(head, tail)`).
- **Structural recursion** — recursion where each recursive call is on a
  structurally-smaller piece of an argument; guarantees termination.
- **Induction principle** — for an inductive type, the schema "prove the base
  case(s) and the step case(s) (assuming the hypothesis) to conclude `P` for all
  values."
- **Induction hypothesis (IH)** — in a step case, the assumed-true instance of
  the goal for the smaller value, usable as a rewrite.
- **Refinement (`⊑`)** — a transitive relation: `impl` refines `spec` if it
  satisfies everything `spec` requires. Chains from requirements to machine code.
- **Kernel** — the small trusted core whose correctness everything rests on.
- **Reflection** — using the object language's own evaluation inside a proof to
  discharge goals by computation.
