# Kindling — the proof of concept behind Understory

Lean 4.34.1, core only (no Mathlib). No `sorry`, no custom axioms.

This is the frozen proof of concept from which Understory grows. It is kept as a
reference; new work happens in the Understory library itself.

## What this is about

The thesis: once it is proven how a classical concept relates to a constructive
construction (the *flattening proof*), the classical statement becomes an
interface. The constructive core computes, and error messages follow from that
same proof rather than from a heuristic.

This proof of concept tests that in one fragment: the *least* witness of a
decidable predicate on `Nat`. Examples are the least non-divisor `lnd m` and
`⌈√m⌉`. It does not prove the general thesis; it shows that the mechanism works
in this fragment, and where it stops.

## Terminology

`certify` is the tactic the classical user calls. What the constructivist
supplies, an implementation with its flattening proof, is called a
*construction* in follow-up work. In this proof of concept a `Search` instance
plays that role (built from `Bounded`, `Solvable` or `Monotone`). The code does
not use the new name yet.

## Installing and running

With [elan](https://github.com/leanprover/elan) installed, `lake` picks the
toolchain from `lean-toolchain` by itself.

    lake build                 # constructive variant (current state of Demo/)
    ./scripts/check-swap.sh    # both variants, same downstream files

`Demo/Spec.lean` and `Demo/Tests.lean` are working copies; the sources are in
`variants/classical/` and `variants/constructive/`. The script copies them in and
builds twice.

## Reading order

1. `Kindling/Least.lean` — the heart: interface, implementations, `least_congr`.
2. `variants/classical/Spec.lean` next to `variants/constructive/Spec.lean` — the
   entire difference the constructivist makes (`diff` them).
3. `Demo/Downstream.lean` — downstream code that compiles unchanged in both variants.
4. `variants/*/Tests.lean` — what happens in each variant, with the exact messages.
5. `Demo/MathlibStyle.lean` and the tests on it — what does and does not work
   without touching an existing definition.
6. `Kindling/Mono.lean` and `Scale/` — a faster implementation under the same interface.
7. `Kindling/Certify.lean` — the seam between tactic and kernel.
8. `Kindling/Flat.lean`, `Kindling/Verdict.lean`, `Demo/Audit.lean` — the logical
   boundaries and the axiom audit.

## What you will see

**Classical only** (existence proved by contradiction): `#eval lnd 12` gives 5
without `noncomputable`, because the proof only serves termination and is
erased. The kernel cannot evaluate it (`decide +kernel` fails). `certify`
reports "Undecided" and states what *is* proven. `lnd` depends on
`Classical.choice`.

**With a constructive implementation** (one block in the interface module: a
bound with its proof): the kernel computes. A false claim yields a
kernel-checked refutation in the user's terms, for example `lnd 12 = 5, ¬5 ≤ 4`.
`Classical.choice` disappears.

**The Mathlib test** (`lnd'`, pinned to the classical search, left untouched):
`decide` still fails, but `certify` refutes and proves claims about it, and
`rw [lnd'_eq_lnd]; decide +kernel` works. Without changing the definition you
therefore get certified proofs and counterexamples, but no direct kernel
computation on that definition itself.

## Design choices

* **Subsingleton interfaces.** `Search p` holds a number together with the proof
  that it is the least; so there is at most one. That makes "downstream does not
  break" a theorem (`least_congr`, `judge_indep`) rather than an appeal to
  parametricity, which Lean does not have internally. For non-canonical
  witnesses ("a" witness instead of "the least") this does not hold: that is the
  boundary.
* **`least` is irreducible, not `opaque`.** Downstream proofs cannot look
  through it, but the kernel can still compute (hence `decide +kernel`).
* **Kernel versus runtime.** Classical existence proofs compute in compiled code,
  not in the kernel. For proofs only the kernel counts; that is why the
  constructive implementations use structural recursion.
* **Errors are certificates.** `Verdict P` has three branches, each carrying a
  proof. "Undecided" carries a named, proven statement that is not a refutation.
* **Classical assumptions stay local** (`Kindling/Flat.lean`): a refutation that
  uses excluded middle for one named proposition is already constructive; for
  global excluded middle this fails.
* **`certify` decides nothing itself.** Compiled code proposes a value; the
  kernel checks it, and the verdict, before any message appears.

## Corrections and limits

* `lnd` keeps `propext`, which comes from core Lean (`Nat.decidable_dvd`), not
  from the framework. For `⌈√m⌉`, `#print axioms` is empty.
* An implementation must be upstream of the first use; otherwise only the
  behaviour at later use sites changes (values remain provably equal).
* One narrow fragment, small examples, no real test against Mathlib.

## Positioning

Closest predecessors: `Decidable`/`reflect` (Bool level, refutation without a
counterexample), CoqEAL's "Refinements for free!" (external parametricity),
Isabelle's code generator and Lean's `@[csimp]` (compiled code). Possibly new
here: subsingleton interfaces as an internal substitute for parametricity,
including for error messages; swaps that affect kernel computation and hence
proofs; the locality rule for classical assumptions.

## Layout

| Module | Imports | Contents |
|---|---|---|
| `Kindling/Flat` | Init | ¬¬-reflector, stability, boundary theorem, local transfer, Markov |
| `Kindling/Verdict` | Init | `Verdict P`: proved / refuted with certificate / undecided with a proven `W` |
| `Kindling/Least` | Verdict | `Solvable` (classical), `Bounded` (constructive), `Search` (subsingleton), `least`, `least_congr`, `judge_indep` |
| `Kindling/Mono` | Least | bisection for monotone predicates: another implementation of `Search p` |
| `Kindling/Certify` | Lean, Least | the seam: the tactic `certify`, for one or more witnesses per goal |
| `Demo/Spec` | Least | the classical user's module (two variants in `variants/`) |
| `Demo/Downstream`, `MathlibStyle`, `TwoImpls` | Spec | unchanged across both variants |
| `Scale/Sqrt`, `SqrtMono`, `Tests` | Least, Mono | `⌈√m⌉` by linear search and by bisection; `csqrtM_eq` proves they are the same function |

## Scaling (measured, not checked by the build)

`decide +kernel` on `csqrt m = ⌈√m⌉`, wall-clock time including start-up (~0.25 s):

| m | bounded search | bisection |
|---|---|---|
| 10⁸ | 1.2 s | 0.26 s |
| 10¹⁰ | 9.8 s | 0.26 s |
| 10¹² | > 120 s (aborted) | 0.26 s |

The fixed definition `csqrt` benefits through the theorem (`rw [← csqrtM_eq]`),
and `certify` picks the fastest implementation itself, even under `csqrt`.

## Proven, checked by the build, trusted, empirical

**Proven** (axiom-free, `Demo/Audit.lean`): `stable_everywhere_iff_em`,
`refute_of_local_em`, `markov`, `Verdict.says_true`, `Search.subsingleton`,
`least_congr`, `judge_indep`, correctness of all three search procedures
(bounded, classical, bisection).

**Checked by the build**: downstream compiles unchanged in both variants; all
messages and axiom footprints via `#guard_msgs`.

**Trusted**: the kernel; the compiler (for `#eval` and for the candidate that
`certify` proposes, which the kernel then checks); reading off the verdict's
branch, and printing.

**Empirical**: friction, performance, scale beyond this fragment.
