# Design decisions

Decisions recorded here are settled; later sessions do not reopen them without
a new reason. Newest last.

## D1 — Toolchain and Mathlib pin (2026-09-30)

Mathlib is pinned to release tag `v4.34.1`, whose `lean-toolchain` is
`leanprover/lean4:v4.34.1`. That is also the toolchain of the proof of concept,
so the port of the core needed no toolchain changes. Mathlib `master` was on
`v4.35.0-rc3` at the time; a release tag is preferred over a moving branch.

## D2 — Renames in the port of the core (2026-09-30)

The core was ported from `reference/lean-understory-kindling/Kindling/` into
`Understory/Core/`, namespace `Understory`. Two names collide with root-level
Mathlib declarations and would become ambiguous in any file that imports
Mathlib and opens `Understory`:

| proof of concept | Understory | Mathlib name it collides with |
|---|---|---|
| `Kindling.IsLeast p n` | `Understory.IsLeastWitness p n` | `IsLeast s a` (order theory) |
| `Kindling.Monotone p` | `Understory.UpwardClosed p` | `Monotone f` (order theory) |

The module `Kindling/Mono.lean` became `Understory/Core/Bisect.lean`, after
what it implements. No other changes to the mathematics or the tactic.

## D3 — Tests of the core live in `Test/` (2026-09-30)

The ported demos of the proof of concept (least non-divisor in both variants,
`⌈√m⌉` with bisection, the axiom audit) are tests of the core, not part of the
graph-theory proof of value. They live in a separate Lake library `Test`, built
by default. `Test` may import anything; nothing imports `Test`.

The swap script of the proof of concept (`check-swap.sh`, two builds with a
different interface module) was not ported; both variants are kept as two
separate test modules instead (`Test/Core/NonDiv.lean`,
`Test/Core/Undecided.lean`).

## D4 — Import rules are checked by a script (2026-09-30)

`scripts/check-imports.sh` checks the import lines of every module against the
dependency rules of `CLAUDE.md`. A module is *internal* when its module path
contains `Internal`; `PoV` may not import those. A build is
`scripts/check-imports.sh && lake build`.

## D5 — Evidence may vary; verdicts may not (2026-09-30)

A claim about a graph can have several correct pieces of evidence (two walks,
two odd cycles). Any valid, kernel-checked piece of evidence is acceptable in a
message. Where a canonical form comes at no cost (the connected component
instead of some closed set; the exact distance labelling), use it. What must
never depend on the implementation is the verdict: proved or refuted. See also
`docs/corrections.md`, C1.

## D6 — Acceptance test for generalising the core (2026-09-30)

When `certify` becomes general, the least-witness case of the proof of concept
becomes one construction among others. Every ported test in `Test/Core/` must
keep its verdict. A change in message wording is allowed, but must be reported.

## D7 — Order of work after phase 0 (2026-09-30)

1. **Core, generalised.** Constructions for yes/no claims with evidence on both
   sides; branch agreement proven once for all; `certify` general; the
   least-witness case as one construction. No graphs yet.
2. **Reachability, minimal.** One graph notion end to end on real Mathlib, with
   simple (slow) checkers. Correctness and shape only.
3. **Measure, then swap.** A scaling table; a faster checker under the same
   construction, with no verdict changing.
4. **Distance, then bipartiteness.**

Why this order: the proof of concept covered only claims with exactly one
correct answer. Generalising the core first makes each graph notion an addition
instead of its own machinery; keeping step 2 simple separates correctness from
speed.

## D8 — Assignments are drafted at each stop point (2026-09-30)

At each stop point the AI drafts the next assignment as
`docs/prompts/NN-name.md`, with the first line `Draft by AI, not yet fired.`
The user reviews it and fires it by giving it to a session as its assignment.
That session first replaces the draft line with the "Fired on" line, as the
kickoff prompt has it. Prompts stay thin (goal, scope, stop point, what counts
as done); everything else lives in the repository, and a fresh session must be
able to carry out a prompt from the repository alone. Prompts never tell a
session to read `CLAUDE.md`: it comes with every session.

Each prompt also has a short **horizon** section: one line per later step,
saying what that step needs from this one. It is marked tentative and not in
scope, and serves only to avoid choices that would block later steps. The order
of steps stays in D7, so the two cannot drift apart. Once a prompt is fired,
its horizon is a snapshot of what was expected at the time.
