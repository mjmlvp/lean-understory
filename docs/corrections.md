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
