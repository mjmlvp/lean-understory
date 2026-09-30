# Understory: classical mathematics as interface, a constructive core as engine

## In one paragraph

Classical mathematics in Lean is abstract and often cannot be computed with;
executable code is often full of implementation detail. Understory connects the
two without either side giving way. A classical definition stays as it is and
becomes an *interface*. A *construction* goes underneath: a constructive
implementation together with a proof that the two belong together, the
*flattening proof*. From that same proof follow two things: Lean can compute,
and a false claim yields not an opaque error but a kernel-checked
counterexample, in the user's own terms.

## Two words

- **`certify`** is what the classical user calls: the tactic that proves or
  refutes a claim, with a kernel-checked certificate.
- **A *construction*** is what the constructivist supplies: an implementation
  under a classical concept, together with its flattening proof. Constructions
  are registered, for instance with an attribute `@[construction]` or as
  instances of a class `Construction`.

The division of labour reads naturally: the constructivist supplies a
construction, the classical user lets `certify` compute against it. Deliberately
not chosen: `by construction` as a tactic. In English that phrase means "follows
directly from the definition", and it is too close to Lean's existing tactic
`constructor`.

## What already exists

A proof of concept in core Lean 4.34.1, without Mathlib, without `sorry` and
without custom axioms (`reference/lean-understory-kindling/`). In one narrow fragment, the
least witness of a decidable property of natural numbers, it shows:

- **Swapping without breakage, as a theorem.** The interface is chosen so that
  there is at most one correct answer (a *subsingleton*). "Downstream does not
  break" is therefore proven (`least_congr`), not hoped for. A script builds the
  same downstream files, byte for byte identical, with and without a
  constructive implementation.
- **Computation in the kernel.** With only a classical existence proof the
  kernel can compute nothing. With one added block (a bound with its proof) it
  can.
- **Errors as certificates.** On a false claim, `certify` reports for instance
  `lnd 12 = 5, ¬5 ≤ 4`, and only after the kernel has checked it. When the
  kernel cannot compute, it says "undecided" and states what *is* proven, rather
  than guessing.
- **Faster implementations under the same interface.** For `⌈√m⌉`, bisection
  replaces linear search. Kernel computation at m = 10¹²: over 120 s (aborted)
  versus 0.26 s including start-up. That it is the same function is again a
  theorem.
- **An untouched definition.** For a pinned, Mathlib-style definition the
  constructivist may not change, certified counterexamples and proofs work
  through a bridge theorem. What does *not* work is `decide` directly on that
  definition: that requires changing the definition itself.

The framework is about 500 lines; the unverifiable seam (the tactic) is about
150 lines, and everything it shows is checked by the kernel first.

## What it offers, by audience

**For the classical mathematician.** You write and read classically; your
definitions stay as they are. For concrete, decidable claims in covered areas
(for instance "this graph is connected") you type `certify`. If the claim holds,
it is proven. If not, you get a counterexample in your own vocabulary, checked by
the kernel. This does not apply to abstract theorems or to arbitrary stuck
proofs: it works where someone has put a construction under the concept.

**For the constructivist.** You can put an algorithm under existing classical
work without building a parallel library and without breaking your colleagues'
work. That it does not break is proven. Your work immediately shows up as
computing power and better messages for everyone who uses the interface.

**For the software engineer.** Faster algorithms can slide under an interface
without adjusting proofs downstream, and the kernel checks the result. For now
this concerns computation *inside* Lean proofs, on small to medium inputs.
Extraction to production code is a future direction, not a promise of this step.

**For Mathlib maintainers.** An opt-in package on top of Mathlib, with no changes
to Mathlib. Whoever imports it gets certified counterexamples and proofs for
existing definitions through bridge theorems. Mathlib need not take a position
in the debate about constructivism. Direct `decide` computation on a Mathlib
definition does require changing that definition; that remains Mathlib's choice.

**For the Lean core team.** So far no change to Lean has been needed: everything
is library plus tactic. If the pattern catches on, there are natural next steps;
see below.

## The proof of value: finite graph theory

The next step tests the idea on real Mathlib mathematics, without modifying
Mathlib. The aim: for concrete finite graphs, prove or refute claims in
Mathlib's own vocabulary, with a certificate on both sides.

| Claim | Proof certificate | Refutation certificate |
|---|---|---|
| A and B are connected | a path | a closed set of vertices containing A and not B |
| the distance is d | a path of length d | a distance labelling that rules out shorter paths |
| the graph is bipartite | a 2-colouring | an odd cycle |

Search may run fast and untrusted; the kernel only checks the certificate.
Success means: this works on graphs of meaningful size, is measurably faster or
more informative than what Mathlib can do now, and leaves Mathlib untouched. If
it fails somewhere, that is a result too: the framework must itself say where a
concept cannot become a computing interface.

## Hopes for the future

These are directions, not promises. They are plausible if the proof of value
succeeds, and each needs its own work and its own testing.

- **One library, two communities.** Classical and constructive work in the same
  place, without a fork, with constructive depth growing step by step beneath
  existing theory.
- **A registry of constructions.** Today Lean's instance mechanism picks the
  implementation. An explicit registry of constructions and bridge theorems
  would let the ecosystem grow in a decentralised way.
- **A `decide` that knows bridges.** A variant of `decide` that first applies
  registered bridge theorems and then lets the kernel compute. This can probably
  be done as a library tactic already; native adoption in Lean would make it the
  default. The kernel itself would not need to change.
- **Error messages as structured data.** Because verdicts are objects, an editor
  could show them interactively: the counterexample, the cut, the odd cycle.
- **From certified computation to certified software.** Where the constructive
  core is efficient, extraction to executable code is a natural extension. That
  is the farthest horizon, and not yet explored here.

## What is new, and what is not

Not new: the double-negation translations, proof by reflection, `Decidable` and
MathComp's `reflect`, refinement of implementations (CoqEAL, Isabelle's code
generator, Lean's `@[csimp]`). Possibly new is the combination: subsingleton
interfaces as an internal substitute for parametricity; swaps that affect kernel
computation and hence proofs, not only compiled code; and verdicts (proved or
refuted) that provably depend only on the interface. The evidence shown in an
error message depends only on the interface where that evidence has exactly one
correct form, as with the least witnesses of the proof of concept. Where several
correct forms exist, such as two different routes or two different odd cycles in
one graph, a swap may change which one is shown; each is still checked by the
kernel. A focused literature review still has to confirm what is new.
