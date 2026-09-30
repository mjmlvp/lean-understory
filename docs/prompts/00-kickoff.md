Fired on 2026-09-30; historical. Lasting rules are in CLAUDE.md.

# Kickoff: build Understory, with a graph-theory proof of value

This is a one-time assignment. The lasting rules are in `CLAUDE.md`; read it
first, then `docs/pitch.md`, then `reference/lean-understory-kindling/README.md`. In that folder, read
`Kindling/Least.lean`, `Kindling/Certify.lean` and the two variants in
`variants/`. The proof of concept is pinned to Lean 4.34.1 without Mathlib;
treat it as read-only.

## The goal

Build Understory as a library under Mathlib, with the proof of value as its
consumer in the same tree. The proof of value shows, on concrete finite graphs,
that claims stated in Mathlib's own vocabulary (`SimpleGraph` and related
notions) can be proved or refuted with a kernel-checked certificate on both
sides, without modifying Mathlib. Candidate notions, in rising difficulty:

| Claim | Proof certificate | Refutation certificate |
|---|---|---|
| reachability | a path | a closed set of vertices containing A and not B |
| distance = d | a path of length d | a labelling that rules out shorter paths (e.g. 1-Lipschitz along edges, 0 at A) |
| bipartite / 2-colourable | a 2-colouring | an odd cycle |

Choose the scope yourself after the survey below. Three notions done
watertight beat six done halfway.

## An open design question: whose code computes?

1. **Existing code under Mathlib**: Mathlib's own decidability instances, or data
   structures and algorithms from Lean's `Std` or Batteries.
2. **Our own code under Mathlib**: small kernel-friendly searchers and checkers,
   with our own bridge theorems to Mathlib notions.

My expectation, which you may refute: a mix works best. Search runs in fast,
untrusted code (existing `Std` code is fine there, since correctness comes from
the check); the kernel runs only a small checker of our own on lists; bridge
theorems connect that checker to Mathlib's definitions. Justify your choice with
measurements.

## Success

The proof of value must do something Mathlib cannot do now, or do it measurably
faster or more informatively, on graphs of meaningful size, with Mathlib
untouched. Include a scaling table up to the point where it breaks, and a README
that is understandable without any conversation history.

## Phase 0: survey, then stop

1. Set up the environment: Mathlib via `lake exe cache get`, toolchain as
   Mathlib pins it. Port the core of the proof of concept into
   `Understory/Core/`, in English, and get it green on that toolchain.
2. Survey Mathlib itself: how the chosen notions are defined and which are
   noncomputable; which decidability instances exist and whether the kernel can
   run them; how far `decide` gets on small concrete graphs, with timings.
3. Present: which notions you choose, which route for the computing code, what
   the bridge theorems look like, how you define success, and how the library is
   laid out.

**Then wait for my response before building further.**

## After phase 0

Small steps, each with a green build: first one notion end to end
(reachability is the obvious start), then extend. After each notion, report
briefly what works, what does not, and what was measured.
