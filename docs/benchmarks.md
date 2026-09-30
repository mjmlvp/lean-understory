# Benchmarks

All numbers here are **empirical**: measured on one machine (Windows 11, 22
cores), Lean 4.34.1, Mathlib v4.34.1. They are not checked by the build.

## Phase 0 baseline: what Mathlib does now (2026-09-30)

Scratch experiments, not yet reproducible from the repository (benchmark
scripts come with phase 1). "Kernel" is the profiler's cumulative
type-checking time; runs were 4–8 in parallel, so expect some noise. Mathlib
import loading (10–35 s) is excluded. `P_n` is the path on `n` vertices,
given as `SimpleGraph.fromRel` over an edge list on `Fin n`.

`decide +kernel` on Mathlib's own instances (`SimpleGraph.instDecidableReachable…`
in `Combinatorics/SimpleGraph/Connectivity/Finite.lean`, which enumerates all
walks of each length below `card V`):

| claim | n=3 | 5 | 8 | 10 | 12 | 16 | 20 | 24 |
|---|---|---|---|---|---|---|---|---|
| `P_n.Reachable 0 (n-1)` | 38 ms | 162 ms | 0.87 s | 6.3 s | 33.8 s | > 150 s | | |
| `¬Reachable 0 (n-1)`, P_n minus middle edge | 19 ms | 42 ms | 0.71 s | | 27.3 s | > 150 s | | |
| `P_n.Connected` | 99 ms | 446 ms | 9.7 s | 47.9 s | > 150 s | | | |
| `(cycleGraph n).Reachable 0 (n/2)` | 21 ms | 30 ms | 143 ms | | 1.07 s | 3.4 s | 19.2 s | > 150 s |
| `(cycleGraph n).Connected` | | | 1.9 s | | 15.9 s | | | |

No decision procedure at all (`decide` fails to synthesize an instance, or gets
stuck at `Classical.propDecidable` under `open Classical`):

- `G.dist u v = d`, `G.edist`: noncomputable (an infimum over walks);
  `rfl`, `simp` and `decide` all fail.
- `G.Colorable 2`, `G.IsBipartite` and their negations: no instance; `aesop`
  makes no progress. The `Fintype (G.Coloring α)` instance is noncomputable.

Certificates written by hand in Mathlib's vocabulary do work:

| hand-written proof | n=5 | 20 | 40 | 60 | 80 | 200 |
|---|---|---|---|---|---|---|
| `P_n.Reachable` by an explicit `Walk.cons … (by decide)` chain (elab + kernel) | | 0.13 s + 0.04 s | | | 1.4 s + 0.9 s | 8.5 s + 4.3 s |
| `P_n.Colorable 2` by `Coloring.mk (v % 2) (by decide +kernel)` | 24 ms | 1.56 s | 11.2 s | 37.5 s | > 150 s | |

Refuting `Colorable 2` for a triangle via `two_colorable_iff_forall_loop_even`
and an explicit odd loop takes milliseconds.

## Phase 0 prototype: list-based certificate checkers (2026-09-30)

Scratch prototype without Mathlib and without bridge theorems: graphs as edge
lists `List (ℕ × ℕ)`, computed in the kernel (`k × k` grids). One file checks a
path certificate for reachability in one grid, and a closed-set certificate for
non-reachability between two disjoint grids. Wall time for the whole file,
including about 0.3 s start-up.

| vertices (edges) | naive: set as a list | set as a binary trie |
|---|---|---|
| 200 (≈ 400) | 11.3 s | 3.0 s |
| 800 (≈ 1 600) | 4 min 27 s | 12.8 s |
| 3 200 (≈ 6 400) | not run | 67 s |
| 12 800 (≈ 25 600) | not run | 5 min 4 s |

Reading: the data structure of the checker decides the scaling; the trie
version is roughly linear-times-log but with a large constant per kernel step.
Even so it handles about 250 times as many vertices as Mathlib's `decide` in
the same time. Bridge theorems to `SimpleGraph` are not included, and their
cost is not yet known.
