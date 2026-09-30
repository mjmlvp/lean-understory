# Understory

A Lean 4 library underneath Mathlib. A classical Mathlib definition stays as it
is and acts as an *interface*. Underneath it goes a *construction*: a
constructive implementation together with a *flattening proof* that ties it to
the classical concept. From that same proof, Lean can compute, and a false claim
yields a kernel-checked counterexample in the user's own vocabulary instead of an
opaque error.

## Status

**Not started.** This repository holds the plan and the proof of concept it
grows from; the library itself does not exist yet. Nothing below is a result
about Understory.

| | |
|---|---|
| Proven | nothing yet about Understory |
| Checked by the build | nothing yet about Understory |
| Exists | the proof of concept in [`reference/lean-understory-kindling/`](reference/lean-understory-kindling/): one narrow fragment, core Lean 4.34.1, no Mathlib |

The first milestone is a proof of value on finite graph theory: prove or refute
claims about concrete graphs, stated with Mathlib's `SimpleGraph`, with a
kernel-checked certificate on both sides and Mathlib left untouched.

## Reading guide

- [`docs/pitch.md`](docs/pitch.md): the vision. It is a hypothesis; results
  decide what holds.
- [`reference/lean-understory-kindling/README.md`](reference/lean-understory-kindling/README.md):
  the proof of concept, frozen. It has its own toolchain and builds on its own
  (`lake build`, or `./scripts/check-swap.sh` for both variants).
- [`docs/prompts/`](docs/prompts/): the assignments this project was given, in
  order.
- [`CLAUDE.md`](CLAUDE.md): the design principle and the working rules. The
  project is developed with Claude Code; this file is its contract.

## License

[Apache License 2.0](LICENSE).
