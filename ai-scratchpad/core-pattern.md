# Design note: the core pattern beyond least witnesses

```
Date: 2026-09-30
Status: draft; questions 1 and 4 await user decision
Based on: the proof of concept (reference/lean-understory-kindling), the phase 0
  survey of Mathlib v4.34.1 (docs/benchmarks.md), conversation with the user
Checked: in Mathlib v4.34.1 sources, Reachable := Nonempty (G.Walk u v)
  (Connectivity/Connected.lean:52), Colorable n := Nonempty (G.Coloring (Fin n))
  (Coloring/Vertex.lean:163), Walk derives DecidableEq (Walk/Basic.lean:54-57).
  The lemma names in section 4 come from the survey and are unchecked here.
  Everything else is a proposal: not proven, not built, not measured.
```

**Pending revisions, from conversation with the user (2026-09-30):**

- Recast section 1 in the vocabulary of truncation, since Mathlib already has
  that structure. Evidence lives in `Type` (`Walk`, `Coloring`, cut sets) and
  the claim is its truncation (`Nonempty`). The subsingleton principle applies
  only to truncated things (claims, verdict branches, values). State branch
  agreement as a function `Verdict P → branch` plus a theorem. HoTT itself is
  ruled out: univalence is inconsistent with Lean's proof-irrelevant `Prop`
  and with Mathlib's global choice.
- The pitch's claim about error messages has been narrowed accordingly
  (`docs/corrections.md`, C1).
- Questions 2 and 3 below are technical: the AI decides them and records why in
  `docs/decisions.md`. Questions 1 and 4 are for the user, and are to be asked
  in plain terms (what users see), not in the terms of this note.

## Why this note

The proof of concept settled the pattern for one case: a *value* with exactly
one correct answer (`least p`). Finite graph theory asks something the proof of
concept never had to answer. The claims are *propositions*, and their evidence
is not unique: many paths prove reachability, many odd cycles refute
bipartiteness. The proof of concept names this as its boundary ("for
non-canonical witnesses this does not hold").

This note settles three questions before any graph code is written:

1. What stays fixed when implementations are swapped, now that certificates are
   not unique?
2. What is a *construction*, concretely, and how is it registered?
3. How does `certify` become general instead of hard-wired to `least`?

It ends with the order of work and the open questions.

## 1. Decision versus evidence

Split every check into two parts.

- **The decision**: whether the claim holds. There is only one correct answer,
  so this part is canonical. This is where the subsingleton principle applies.
- **The evidence**: the certificate that backs the decision up. It is generally
  not unique, and different implementations may produce different evidence.

What this means for each layer:

- **Downstream proofs cannot see the evidence at all.** Proofs of a `Prop` are
  definitionally irrelevant in Lean. Whichever path went into a proof of
  `G.Reachable a b`, no downstream theorem can depend on it. This comes for
  free from the logic, not from our discipline.
- **Verdicts can see it.** `Verdict P` lives in `Type`, and `refuted C c s`
  carries the certificate statement `C`. So `Verdict P` is *not* a subsingleton,
  and the proof of concept's `judge_indep` does not carry over.
- **What replaces it: branch agreement** (to be proven). Two verdicts on the
  same claim never disagree on a decisive branch. If one is `proved` and the
  other `refuted`, that is a contradiction. Two implementations can differ only
  in their evidence, or in one saying `unknown` where the other decides.
- **Messages** are then guaranteed only to state *a* certificate the kernel has
  checked, not *the* certificate. That is the honest boundary, and the README
  must say so.

**Canonical evidence where it is cheap.** Some certificates can be made unique
by strengthening their specification, and then messages are
implementation-independent again:

- For non-reachability: the connected component of `a`, instead of *some*
  closed set containing `a`.
- For distance lower bounds: the exact distance labelling, instead of *some*
  1-Lipschitz labelling.

Paths and odd cycles have no cheap canonical form (a "least" path in some order
is expensive to check). So canonical evidence is an option per certificate, not
a rule.

**Values** (`least p`, `G.dist u v`) stay as in the proof of concept. The
specification of an implementation is "equals the interface term", which has
at most one answer by construction: `{v // t = v}` is a subsingleton. For an
untouched Mathlib definition this is the natural specification, since we may
not look inside it.

## 2. What a construction is

A construction is what the constructivist supplies: computable data or
procedures under a classical concept, plus the flattening proof. Three kinds
appear in the graph work:

| kind | sits under | supplies | flattening proof |
|---|---|---|---|
| **claim construction** | a proposition `P` (e.g. `G.Reachable a b`) | certificate types for `P` and `¬P`, Bool checkers for both, and what each refutation certificate *says* in the user's vocabulary | checker accepts ⇒ `P`; checker accepts ⇒ the stated claim ⇒ `¬P` |
| **value proposer** | a term `t` (e.g. `G.dist u v`) | an untrusted guess for its value | none (the guess is checked through a claim construction for `t = v`) |
| **presentation** | an object (e.g. `G : SimpleGraph (Fin n)`) | a computable representation (sorted neighbour lists) | the representation matches `G.Adj` |

**The presentation can be made canonical.** Require duplicate-free sorted
neighbour lists, and the presentation of a graph on `Fin n` is unique. Faster
ways to compute it are then provably the same presentation.

**Registration: typeclasses.** The recommendation is a class
`Construction (P : Prop)` for claim constructions, and separate classes for
proposers and presentations. Why:

- Instance search *is* a registry, indexed by the shape of the goal. It already
  picked the implementation in the proof of concept.
- A goal like `G.Reachable a b` is found by synthesizing
  `Construction (G.Reachable a b)`. That instance in turn needs
  `[Presentation G]`, so the layers compose without extra machinery.
- An attribute-based registry would need its own discrimination tree for the
  same job.

**Generic instances** handle the logical connectives: `¬P` by swapping the two
sides of `P`, and `P ∧ Q`, `P ∨ Q`. Quantifiers over `Fin n` get generic
instances too, but efficient ones for notions like `Connected` are dedicated
constructions (one component certificate, not `n²` separate ones).

**No global `Decidable` instances.** We do not register `Decidable`
instances under Mathlib concepts. That avoids instance diamonds with anything
Mathlib adds later. `certify` is the entry point; a `Decidable` instance can be
derived from a complete construction on request.

**Open naming question.** Is "construction" the umbrella term, with the three
kinds above, or is only the claim class called `Construction`? `CLAUDE.md`
asks for "a class `Construction`", which fits the claim class best.

## 3. `certify`, generalised

`certify` stays a conduit that decides nothing itself. On goal `G₀`:

1. **Evaluate values.** For each subterm `t` with a registered proposer: get an
   untrusted guess `v`, obtain `Construction (t = v)`, find a proof certificate
   (untrusted), let the kernel check it, rewrite `t` to `v`. If the construction
   instead *refutes* `t = v`, the proposer is wrong: report that as a proposer
   error, never as a verdict on the goal.
2. **Decide the rest.** If `Construction G` exists for the rewritten goal `G`:
   untrusted search proposes a certificate, the kernel checks it, and the result
   is `proved` or `refuted`.
3. **Fall back.** Otherwise, if `Decidable G` reduces in the kernel, decide it
   (the proof of concept's `ofRewrite`).
4. **Otherwise say `Undecided`,** and state what is proven (the checked
   rewrites).

A refutation message states the certificate's claim in Mathlib vocabulary. For
large certificates it names a checked constant instead of printing everything
inline, for example "the vertex set `_cut_1` (3 200 vertices) contains 0, not
7, and is closed under `G.Adj`". The user can `#print` that constant. The
message still says nothing the kernel has not checked.

**Acceptance test for the generalisation:** `least` becomes an ordinary
instance (`Construction (least p = n)`, checked by kernel evaluation of
`Search.val`). All ported tests in `Test/Core/` must pass with *unchanged
messages*. That shows the generalisation lost nothing.

## 4. Contact with real Mathlib

- **Lemmas only.** Bridges use Mathlib lemmas (`reachable_iff_reflTransGen`,
  `dist_le`, `two_colorable_iff_forall_loop_even`, …), never unfolding.
- **Axiom footprint.** Bridge theorems will probably depend on
  `Classical.choice` through Mathlib's own lemma proofs. That does not block
  computation, since the checkers are Bool functions. It does differ from the
  proof of concept's axiom-free results, and must be reported as such: pinned
  with `#print axioms`, and recorded in `docs/corrections.md` if anything
  earlier suggests otherwise.
- **Vertex type:** `Fin n` first. Other finite types later, through an explicit
  equivalence, if at all.
- **Unknown until measured:** the kernel cost of `Fin` arithmetic and of
  Mathlib's own `DecidableRel` instances inside a presentation; the elaboration
  cost of large certificate literals; whether our files need the module system.

## 5. Order of work

Each step ends with a green build, a commit, and a short report.

1. **Core.** `Construction`, proposers, branch agreement, generic `certify`;
   `least` as an instance; the ported tests pass unchanged.
2. **Minimal graph slice.** `Presentation` for `SimpleGraph (Fin n)`;
   reachability with the *naive* checkers (path, closed set); bridges through
   Mathlib lemmas; tiny graphs; axioms pinned. Correctness and shape only.
3. **Measure, then swap.** Scaling table; a faster checker under the same
   construction. Soundness is all each checker needs; branch agreement keeps
   the decisions consistent.
4. **Distance**, then **bipartiteness**.

## Open questions for review

1. Is the decision/evidence split the right reading of the subsingleton
   principle for propositions? Should canonical evidence be the default where
   cheap, or opt-in?
2. Typeclasses for registration: `Construction (P : Prop)`, plus proposers and
   presentations?
3. Naming: which of these is "the construction"?
4. Is "the ported tests pass with unchanged messages" the right acceptance test
   for step 1?
