# Provable Software — Docs

Pilot exploring **provable software**: a small object language for writing
functions, an interpreter, a small proof language, and a trusted checker that
proves "unit tests" (functions that should be `true` for every input) always
hold. Throwaway by design — the goal is to learn the shape of the idea.

- `OVERVIEW.md` — thesis, two-level architecture, trust model, design decisions,
  the long-term refinement/LLM vision, and the known hard parts. Start here.
- `ROADMAP.md` — north-star demo, staged milestones (M0–M3), proposed crate
  layout, open questions, and current status.
- `M3-WALKTHROUGH.md` — a map of the shapes in the completed M3 proof (in-place
  array reverse = functional `rev`): the per-position loop invariant, the 5-region
  case split, the swap framing, the ∀-instantiation kernel change, and the lift to
  `rev`. Read alongside `tests/common/`.
