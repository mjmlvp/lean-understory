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
