# Understory

A Lean 4 library underneath Mathlib. A classical Mathlib definition stays as it
is and acts as an *interface*. Underneath it goes a *construction*: a
constructive implementation together with a *flattening proof* that ties it to
the classical concept. From that same proof, Lean can compute, and a false claim
yields a kernel-checked counterexample in the user's own vocabulary instead of an
opaque error.

## Status

**Step 1 done: the core is general. Still no graph theory.**

`certify` is now a socket. A *construction* for a yes/no claim brings a search
for evidence (fast, not trusted) and checkers for evidence on both sides
(proven sound). `certify` runs the search, lets the kernel check what it
found, and shows only what the kernel confirmed. The least-witness case of the
proof of concept is one construction; a toy claim (`Test/Core/Lands.lean`,
"can steps of `a` forward and `b` back end exactly `c` ahead?") is another,
with several valid pieces of evidence on each side. The construction interface
is a first version: step 2 is its first real use and may change it.

| | |
|---|---|
| Proven | a verdict never claims anything false; two verdicts on one claim never contradict each other (`Verdict.branch_agree`), so no swap of construction or search flips proved into refuted; where evidence has only one correct form, the message is the same for every implementation whose check the kernel can run (`least_message_indep`; decision D11). Swapping in an implementation that can compute, where none could, may turn "Undecided" into an answer; that is intended. Least witnesses are unique, so swapping their implementation changes no value (`least_congr`). Statements and axiom footprints pinned in `Test/Core/Audit.lean`. |
| Checked by the build | all tests and messages (`Test/Core/`, via `#guard_msgs`); the import rules (`scripts/check-imports.sh`) |
| Trusted | the Lean kernel; the compiled code that proposes values and evidence, which the kernel then checks; turning compiled results into terms; printing of messages |
| Empirical | the survey of what Mathlib can decide about graphs, and a prototype of our own checkers ([`docs/benchmarks.md`](docs/benchmarks.md)) |

What the survey found: Mathlib's `decide` settles reachability and
connectivity only for tiny graphs (about 12–20 vertices), and cannot settle
distance or 2-colourability at all. A prototype checker of our own handled
thousands of vertices, not yet linked to Mathlib's definitions.

**Next:** graph theory one notion at a time, starting with reachability on
real Mathlib. The order and its reasons are decision D7 in
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
| `Understory/Core/` | verdicts, constructions for claims, least witnesses and bisection, least witnesses as a construction, the tactic `certify`; imports Lean core only |
| `Understory/Graph/` | (not yet created) constructions under Mathlib's graph notions |
| `PoV/` | (not yet created; `PoV.lean` is an empty placeholder) the proof of value: concrete graphs in Mathlib's terms |
| `Test/` | tests of the library, pinned with `#guard_msgs`: the ported proof of concept, the toy claim, the axiom audit |
| `scripts/` | `check-imports.sh` |

## License

[Apache License 2.0](LICENSE).
