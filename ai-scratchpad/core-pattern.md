# Design note: the core pattern beyond least witnesses

```
Date: 2026-09-30 (revised the same day)
Status: draft. Input for planning step 1 (docs/prompts/01-core-socket.md);
  the plan made there supersedes this note where they differ.
Based on: the proof of concept (reference/lean-understory-kindling), the phase 0
  survey of Mathlib v4.34.1 (docs/benchmarks.md), conversation with the user
  (decisions D5-D7 in docs/decisions.md).
Checked: in Mathlib v4.34.1 sources, Reachable := Nonempty (G.Walk u v)
  (Connectivity/Connected.lean:52), Colorable n := Nonempty (G.Coloring (Fin n))
  (Coloring/Vertex.lean:163), Walk derives DecidableEq (Walk/Basic.lean:54-57).
Unchecked: the lemma names in section 6 (from the survey, not re-verified);
  the HoTT remarks in section 1 (from background knowledge, not verified here).
  Everything else is a proposal: not proven, not built, not measured.
```

## Why this note

The proof of concept settled the pattern for one case: a *value* with exactly
one correct answer (`least p`). Finite graph theory asks something the proof of
concept never had to answer. The claims are *propositions*, and their evidence
is not unique: many walks prove reachability, many odd cycles refute
bipartiteness. The proof of concept names this as its boundary ("for
non-canonical witnesses this does not hold").

Questions this note answers, as proposals:

1. What stays fixed when implementations are swapped, now that evidence is not
   unique? (section 1)
2. How are the proofs staged? (section 2)
3. What is a construction, concretely, and how is it registered? (section 3)
4. How does `certify` become general, and what stays unproven? (sections 4, 5)

## 1. Evidence and its truncation

Mathlib already separates evidence from claims:

- **Evidence lives in `Type`**, as data with many distinct elements: `G.Walk u
  v`, `G.Coloring (Fin 2)`, and our own cut sets and labellings. `Walk` even has
  decidable equality, so two pieces of evidence can be told apart.
- **The claim is its truncation**: `Reachable := Nonempty (Walk u v)`,
  `Colorable n := Nonempty (Coloring (Fin n))`. `Nonempty` forgets which
  evidence there was.

Consequences:

- **The subsingleton principle applies to truncated things only**: claims,
  the branch of a verdict (proved / refuted), and values (`least p`,
  `G.dist u v`). These have one correct answer, so swapping implementations
  under them is a theorem.
- **Downstream proofs cannot see evidence.** Proofs of a `Prop` are
  definitionally irrelevant in Lean. This comes from the logic, not from
  discipline.
- **Verdicts can see it.** `Verdict P` lives in `Type`, and `refuted C c s`
  carries the certificate statement `C`. So `Verdict P` is not a subsingleton,
  and `judge_indep` from the proof of concept does not carry over.
- **What replaces it: branch agreement.** A function `Verdict.branch : Verdict P
  → Branch` (proved / refuted / unknown) and a theorem: two verdicts on the same
  claim never have branches proved and refuted. Proven once, for all
  constructions.
- **Messages** state *a* certificate the kernel has checked, not *the*
  certificate (docs/corrections.md, C1).
- **Certificates stay data**, never squashed into `Prop`, so they remain
  visible and comparable.

**Canonical evidence where it comes at no cost** (D5). Examples: for
non-reachability, the connected component of `a` instead of some closed set;
for distance lower bounds, the exact distance labelling. Walks and odd cycles
have no cheap canonical form; any valid, checked one will do.

**Values** stay as in the proof of concept. For an untouched Mathlib term `t`,
the specification of an implementation is "equals `t`": `{v // t = v}` is a
subsingleton, and we need not look inside `t`.

**HoTT** was considered and ruled out. Its reading (evidence as structure,
claims as truncations) is what we adopt, but its machinery cannot be used:
univalence is inconsistent with Lean's proof-irrelevant `Prop` and with
Mathlib's global choice. Take care with the word "path": in graph theory a walk
without repeated vertices; in HoTT an equality. Use "walk" in our docs where
possible.

## 2. Staged main theorems

Each stage has one main theorem, its specification. The stage above uses only
that theorem, never the internals below (the design principle of CLAUDE.md).

1. **Verdicts.** `Verdict.says_true` (exists): a verdict never claims anything
   false. New: branch agreement.
2. **Constructions.** A construction's specification is its soundness: its
   checker accepts evidence ⇒ the claim; accepts counter-evidence ⇒ the stated
   certificate claim ⇒ the negation. Main theorem of the stage: the judge
   built from any construction yields a verdict whose branch is correct. Proven
   from the specification alone, so it holds for every future construction.
3. **The least-witness case as a construction.** Prove that it meets the
   construction specification using only `least_spec` and `least_congr`. This
   moves the old stage's main theorems across the boundary instead of
   reproving anything.
4. **Whole stack.** For least-witness claims: sound answers, and no swap flips
   a verdict. By composition, not by a new proof.

In step 2 the same pattern crosses the Mathlib boundary: the graph
construction's soundness is proven from Mathlib lemmas only.

## 3. What a construction is

| kind | sits under | supplies | flattening proof |
|---|---|---|---|
| **claim construction** | a proposition `P` (e.g. `G.Reachable a b`) | evidence types for `P` and `¬P`, Bool checkers for both, what counter-evidence *says* in the user's vocabulary | checker accepts ⇒ `P`; checker accepts ⇒ stated claim ⇒ `¬P` |
| **value proposer** | a term `t` (e.g. `G.dist u v`) | an untrusted guess for its value | none: the guess is checked through a claim construction for `t = v` |
| **presentation** | an object (e.g. `G : SimpleGraph (Fin n)`) | a computable representation (sorted, duplicate-free neighbour lists) | the representation matches `G.Adj` |

A presentation with sorted, duplicate-free lists is unique, so faster ways of
computing it are provably the same presentation.

**Registration: typeclasses** (proposal; to be decided and recorded in step 1).
`Construction (P : Prop)` for claim constructions, separate classes for
proposers and presentations. Instance search is a registry indexed by goal
shape; it picked implementations in the proof of concept already; layers
compose (`Construction (G.Reachable a b)` needs `[Presentation G]`).

**Generic instances** for connectives: `¬P` swaps the two sides of `P`;
`P ∧ Q`, `P ∨ Q`. Quantifiers over `Fin n` generically, but notions like
`Connected` get dedicated constructions (one component certificate, not `n²`).

**No global `Decidable` instances** under Mathlib concepts: that avoids
instance diamonds with anything Mathlib adds later. `certify` is the entry
point.

**Naming** (to be decided in step 1): "construction" as the umbrella term, or
only the claim class `Construction`. CLAUDE.md asks for "a class
`Construction`", which fits the claim class.

## 4. `certify`, generalised

On goal `G₀`:

1. **Evaluate values.** For each subterm `t` with a registered proposer: get an
   untrusted guess `v`, obtain `Construction (t = v)`, find evidence, kernel
   check, rewrite `t` to `v`. If the construction instead refutes `t = v`, the
   proposer is wrong: report a proposer error, never a verdict on the goal.
2. **Decide the rest.** With `Construction G` for the rewritten goal:
   untrusted search proposes evidence, the kernel checks, the result is proved
   or refuted.
3. **Fall back.** Otherwise, if `Decidable G` reduces in the kernel, decide it
   (the proof of concept's `ofRewrite`).
4. **Otherwise `Undecided`**, stating what is proven (the checked rewrites).

A refutation message states the certificate's claim in Mathlib vocabulary.
Large certificates are named as checked constants rather than printed inline
("the vertex set `_cut_1` (3 200 vertices) contains 0, not 7, and is closed
under `G.Adj`"), so the user can `#print` them.

**Acceptance test** (D6): the least-witness case becomes an ordinary
construction, and every ported test in `Test/Core/` keeps its verdict. Changed
message wording is allowed but reported.

## 5. The seam: what stays unproven

`certify` is meta-level code and is not proven. A full proof of it is not
planned; no practical route for verifying tactics end to end in Lean is known
to us (unchecked). It is not needed for soundness: everything `certify` shows is
kernel-checked first, so a bug can cause a failure or a poor message, never a
false theorem.

What remains trusted: that the printed message reflects what was checked (keep
it to Lean's own pretty-printing of the checked statement), and reading off the
verdict's branch. Completeness (does it find evidence when there is some) is a
quality matter for tests and measurements.

Direction: move logic out of `certify` into the proven stages, until the seam
only searches, hands evidence to a construction's checker, and prints.

## 6. Contact with real Mathlib

- **Lemmas only.** Bridges use Mathlib lemmas (`reachable_iff_reflTransGen`,
  `dist_le`, `two_colorable_iff_forall_loop_even`, …), never unfolding.
- **Axiom footprint.** Bridge theorems will probably depend on
  `Classical.choice` through Mathlib's own lemma proofs. That does not block
  computation (the checkers are Bool functions), but differs from the proof of
  concept's axiom-free results. Pin with `#print axioms`, report it.
- **Vertex type:** `Fin n` first.
- **Unknown until measured:** kernel cost of `Fin` arithmetic and of Mathlib's
  `DecidableRel` instances inside a presentation; elaboration cost of large
  certificate literals; whether our files need the module system.

## 7. Order of work

See D7 in `docs/decisions.md`.
