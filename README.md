# Understory

A Lean 4 library underneath Mathlib. A classical Mathlib definition stays as it
is and acts as an *interface*. Underneath it goes a *construction*: a
constructive implementation together with a *flattening proof* that ties it to
the classical concept. From that same proof, Lean can compute, and a false claim
yields a kernel-checked counterexample in the user's own vocabulary instead of an
opaque error.

## Status

**Phase 0 done: set-up and survey. The library itself holds only the ported
core so far; no graph theory yet.**

| | |
|---|---|
| Proven | the proof of concept's core, ported (`Understory/Core/`): verdicts never claim anything false; least witnesses are unique, so swapping their implementation provably changes nothing. Axiom footprints pinned in `Test/Core/Audit.lean`. |
| Checked by the build | all ported tests and messages (`Test/Core/`, via `#guard_msgs`); the import rules (`scripts/check-imports.sh`) |
| Trusted | the Lean kernel; the compiled code behind `certify` proposes candidates, which the kernel checks; printing of messages |
| Empirical | the survey of what Mathlib can decide about graphs, and a prototype of our own checkers ([`docs/benchmarks.md`](docs/benchmarks.md)) |

What the survey found: Mathlib's `decide` settles reachability and
connectivity only for tiny graphs (about 12–20 vertices), and cannot settle
distance or 2-colourability at all. A prototype checker of our own handled
thousands of vertices, not yet linked to Mathlib's definitions.

**Next:** generalise the core from claims with exactly one correct answer to
yes/no claims with evidence on both sides, then graph theory one notion at a
time. The order and its reasons are decision D7 in
[`docs/decisions.md`](docs/decisions.md); the current assignment is the latest
file in [`docs/prompts/`](docs/prompts/).

## Building

With [elan](https://github.com/leanprover/elan) installed:

    lake exe cache get                         # Mathlib's prebuilt files
    scripts/check-imports.sh && lake build     # the build is the test

Lean 4.34.1, Mathlib `v4.34.1` (pinned in `lakefile.toml`).

## Reading guide

- [`CLAUDE.md`](CLAUDE.md): the design principle and the working rules. The
  project is developed with Claude Code; this file is its contract.
- [`docs/pitch.md`](docs/pitch.md): the vision. It is a hypothesis; results
  decide what holds.
- [`docs/decisions.md`](docs/decisions.md): settled decisions;
  [`docs/corrections.md`](docs/corrections.md): claims later narrowed or
  refuted; [`docs/benchmarks.md`](docs/benchmarks.md): measurements.
- [`docs/prompts/`](docs/prompts/): the assignments, in order.
- [`reference/lean-understory-kindling/`](reference/lean-understory-kindling/README.md):
  the proof of concept, frozen. It builds on its own (`lake build` in that
  folder).
- `ai-scratchpad/`: working notes by the AI, fallible and not endorsed; not
  needed to understand the project.

## Layout

| path | contents |
|---|---|
| `Understory/Core/` | verdicts, least witnesses, bisection, the tactic `certify`; imports Lean core only |
| `Understory/Graph/` | (not yet created) constructions under Mathlib's graph notions |
| `PoV/` | (not yet created; `PoV.lean` is an empty placeholder) the proof of value: concrete graphs in Mathlib's terms |
| `Test/` | tests of the library, pinned with `#guard_msgs` |
| `scripts/` | `check-imports.sh` |

## License

[Apache License 2.0](LICENSE).
