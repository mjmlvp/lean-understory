Draft by AI, not yet fired.

# Step 1: generalise the core

Start in plan mode.

## Goal

Step 1 of decision D7 in `docs/decisions.md`. Today `certify` handles one kind
of claim: a least witness, which has exactly one correct answer. Make the core
handle yes/no claims with evidence on both sides, where the evidence need not
be unique. A construction supplies a search, checkers and their soundness
proofs; `certify` does the rest. The least-witness case becomes one
construction among others.

## Scope

In:

- constructions for claims, and how they are registered (decide, and record
  why in `docs/decisions.md`);
- branch agreement: two verdicts on one claim never contradict, proven once for
  all constructions;
- `certify` generalised, with as little logic as possible left in the tactic;
- the least-witness case as a construction, proven from its existing main
  theorems;
- a toy yes/no claim, not about graphs, proved and refuted through a
  construction.

Out: graphs and anything that imports Mathlib; performance work.

`ai-scratchpad/core-pattern.md` holds a design proposal for this step. It is
input, not a decision: check what you take from it.

## Horizon (tentative, not in scope)

Use this only to avoid choices that would block these later steps (order: D7).

- **Step 2, reachability:** a construction under a Mathlib notion, needing a
  computable form of the graph; evidence is a walk or a closed set of
  vertices; soundness proven from Mathlib lemmas only.
- **Step 3, faster checkers:** a checker must be replaceable without touching
  claims or tests.
- **Step 4, distance and bipartiteness:** distance is a value, not a yes/no, so
  a value has to be proposed and then checked; large evidence (thousands of
  vertices) must be shown by name, not printed in full.
- **Beyond:** the proof of value's scaling table and a README readable without
  history.

## Stop point

Present the plan and wait for approval before writing code. After approval:
build the plan, then stop and report what works, what does not, and what
changed in messages, separating proven, checked by the build, trusted and
empirical. Draft the next assignment as `docs/prompts/02-...`.

## Done when

- The build is green: `scripts/check-imports.sh && lake build`.
- Every ported test in `Test/Core/` keeps its verdict (D6); changed message
  wording is reported.
- The main theorem of each stage, and its axiom footprint, is pinned in the
  build.
- `README.md`, `docs/decisions.md` and the scratchpad notes are consistent with
  the code.
