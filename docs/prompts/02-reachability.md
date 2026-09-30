Draft by AI, not yet fired.

# Step 2: reachability, minimal

Start in plan mode.

## Goal

Step 2 of decision D7 in `docs/decisions.md`. Put one construction under a real
Mathlib notion, end to end: `G.Reachable a b` for a concrete
`G : SimpleGraph (Fin n)`. The user states the claim in Mathlib's words and
types `certify`; the claim is proved by a walk, or refuted by a set of vertices
that contains `a`, not `b`, and is closed under `G.Adj`. Correctness and shape
only; the checkers may be slow.

## Scope

In:

- `Understory/Graph/`: a computable form of a concrete graph, with a proof that
  it matches `G.Adj` (decide how graphs are given, and record why);
- a `Construction (G.Reachable a b)`, its checkers, and their soundness from
  Mathlib lemmas only (D10 for the shape; check every lemma name in the pinned
  Mathlib);
- canonical counter-evidence where it comes at no cost (D5, D11): decide
  whether the closed set is the connected component, and say why;
- `PoV/`: a first file of concrete graphs in Mathlib's terms, proved and
  refuted through `certify`, and the same examples with Mathlib's `decide`
  for comparison (the baseline is in `docs/benchmarks.md`);
- axiom footprints pinned and reported. `Classical.choice` from Mathlib's own
  proofs is expected; say where it comes from.

Out: faster checkers and data structures; `Connected`, distance,
bipartiteness; changes to the core beyond what this construction needs (any
such change is reported, with what relies on it).

## Horizon (tentative, not in scope)

Use this only to avoid choices that would block these later steps (order: D7).

- **Step 3, measure then swap:** a scaling table needs graph families built by
  a function of `n`; a faster checker must slide in under the same claim
  without touching tests (D9: a local instance).
- **Step 4, distance and bipartiteness:** distance is a value (a `Proposer` and
  a construction for `G.dist u v = d`); large evidence must be shown by name,
  not printed in full.
- **Beyond:** the proof of value's scaling table and a README readable without
  history.

## Stop point

Present the plan and wait for approval before writing code. After approval:
build the plan, then stop and report what works, what does not, and what was
measured, separating proven, checked by the build, trusted and empirical.
Draft the next assignment as `docs/prompts/03-...`.

## Done when

- The build is green: `scripts/check-imports.sh && lake build`.
- Every test in `Test/Core/` keeps its verdict and message (D6).
- A reachable pair is proved and an unreachable pair refuted by `certify` in
  `PoV/`, with the refutation message stated in Mathlib's vocabulary and
  pinned with `#guard_msgs`.
- The main theorem of each new stage, and its axiom footprint, is pinned in
  the build.
- `README.md`, `docs/decisions.md` and `docs/benchmarks.md` are consistent
  with the code.
