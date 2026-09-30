# Corrections

Claims once made and later refuted or narrowed. Newest last.

## C1 — Error messages do not always depend only on the interface (2026-09-30)

**Claimed** in `docs/pitch.md` ("What is new"): error messages that provably
depend only on the interface.

**Holds** where the evidence in a message has exactly one correct form. In the
proof of concept every message states the least witness, which is unique, so
`judge_indep` proves the message independent of the implementation.

**Does not hold in general.** A claim about a graph can have several correct
pieces of evidence: two routes between the same vertices, two odd cycles in one
graph. Swapping implementations may then change which one a message shows. What
stays independent of the implementation is the verdict itself (proved or
refuted). Every piece of evidence shown is still checked by the kernel.

**Changed:** the sentence in `docs/pitch.md` now makes that distinction.

## C2 — `judge_indep` did not cover what `certify` built (2026-09-30)

**Claimed** in C1: "In the proof of concept every message states the least
witness, which is unique, so `judge_indep` proves the message independent of
the implementation."

**Narrowed.** `judge_indep` is about `judge`, a model of the tactic. The tactic
itself built its verdict with `Verdict.ofRewrite`, not with `judge`
(`Understory/Core/Certify.lean` before step 1). The independence held in fact,
but the proof was about the model, not about what was shown.

**Also narrowed:** independence holds only among implementations whose check
the kernel can run. With only a classical implementation the verdict is
undecided; adding a computing one turns it into an answer
(`Test/Core/Undecided.lean` against `Test/Core/NonDiv.lean`).

**Changed:** `judge` and `judge_indep` are removed. The independence is proven
for the blocks `certify` uses: `Verdict.ofValue_indep`,
`Construction.Decides.unique` and `least_message_indep` (D11). C1 is left as
written; the sentence in `docs/pitch.md` now mentions the kernel check.

## C3 — `certify` in the proof of concept worked only in `example` (2026-09-30)

**Implied** by the proof of concept's tests: `certify` proves claims. All of
them used `example`.

**Did not hold** in a named theorem. In a scratch copy of
`reference/lean-understory-kindling`, `theorem named_ok : lnd 12 = 5 := by
certify` fails with "cannot add declaration _certify… to environment as it is
restricted to the prefix named_ok", while the same claim as `example` works.
The tactic named its kernel-checked helper declarations without the prefix of
the declaration being elaborated.

**Changed:** fixed in step 1 (`mkAuxDeclName` in `Understory/Core/Certify.lean`),
pinned by the named theorems `lands_6_10_4` and `lands_6_10_4'` in
`Test/Core/Lands.lean`.
