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

## D9 — Constructions are registered as instances of a class (2026-09-30)

A construction for a claim `P` is an instance of the class
`Understory.Construction P` (`Understory/Core/Construction.lean`), not a
declaration tagged with an attribute `@[construction]`. Why:

- instance search is already a registry indexed by the shape of the goal, and
  it picked implementations in the proof of concept too;
- priorities give the fallback order (the `Decidable` fallback has low
  priority);
- `attribute [local instance high]` swaps a construction for one section,
  which is what a faster checker needs (D7, step 3);
- instance arguments compose layers (a graph construction can require a
  computable form of the graph).

The umbrella term stays "construction"; the class carries the name.

## D10 — The shape of a construction, and what `certify` does with it (2026-09-30)

- A construction for `P` supplies evidence types for `P` and against it, a
  `Bool` checker for each with its soundness proof, what counter-evidence
  states in the user's vocabulary (`Says`), an untrusted `search`, and
  optionally what stays proven if no check can run (`Known`) and a hint.
- The hint is advice, never checked: an instance that would let the kernel
  run the check. It is printed only in an undecided message.
- The search runs only in compiled code; its result is turned into a term
  (`ToExpr`) and only the checker runs in the kernel.
- A *value* (a term such as `least p`) is proposed by an instance of
  `Proposer t` and checked through `Construction (t = v)`. The claim with the
  value substituted is then decided by its own construction. `Verdict.ofValue`
  assembles the two at object level.
- Any decidable claim has a low-priority construction (`Construction.ofDecidable`),
  so the tactic itself has no `Decidable` fallback.
- `certify` contains no construction-specific code. The kernel reads the
  branch of the verdict (`Verdict.of_branch_proved v rfl`,
  `Verdict.not_of_branch_refuted v rfl`), so reading the branch is no longer
  trusted meta code.
- Evidence is printed inline for now. Naming large evidence (D7, step 4) can
  be added in the tactic's printing without changing constructions.

## D11 — Message independence for least witnesses is kept (2026-09-30)

When a claim has only one correct piece of evidence, the message is the same
for every implementation whose check the kernel can run. This is what
`docs/pitch.md` and `docs/corrections.md` (C1) state for least witnesses, and
it is now proven for the parts `certify` actually uses (see C2):

- `Verdict.ofValue_indep`: a checked value leaves one verdict, however it was
  found (every value, not only least witnesses);
- `Construction.Decides.unique`, from `UniqueEvidence` and `UniqueCounter`: a
  construction whose checker accepts only one piece of evidence on each side
  delivers one verdict. The `Decidable` fallback and the least-witness
  construction have both properties;
- `least_message_indep`: for a claim `Q (least p)`, two implementations whose
  checks passed give the same verdict.

This holds only among implementations the kernel can compute with. Adding one
where there was none turns "Undecided" into an answer; that is intended, and
branch agreement (`Verdict.branch_agree`) allows it: it rules out only proved
against refuted. Where evidence is not unique (D5), only the verdict is
independent, not the message. `UniqueEvidence` and `UniqueCounter` are the
properties to prove for canonical forms (the connected component, the exact
distance labelling).
