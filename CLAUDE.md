# CLAUDE.md — lean-understory

## What this is

**Understory** is a Lean 4 library that sits underneath Mathlib. A classical
Mathlib definition stays as it is and acts as an *interface*. A *construction*
goes underneath it: a constructive implementation together with a *flattening
proof* that ties it to the classical concept. From that same proof follow two
things: Lean can compute, and a false claim yields a kernel-checked
counterexample in the user's own vocabulary instead of an opaque error.

The **proof of value (PoV)** lives in the same tree as a consumer of the
library: finite graph theory on concrete graphs, stated in Mathlib's own terms.

Background: `docs/pitch.md` (goal and vision), `reference/lean-understory-kindling/README.md`
(the proof of concept this grows from).

## The design principle — applies at every level

**Modular verification with deliberate underspecification, applied recursively
down to the capillaries.**

- An interface is a specification. A construction is an implementation.
  Everything downstream depends only on the interface.
- This holds at every level: repository, libraries, modules, definitions,
  proofs, and documentation. Every proof uses only the specification of what it
  calls, never the definitional unfolding of someone else's internals.
- At the top level: **Mathlib is the interface that underspecifies; Understory
  is the implementation; the PoV is the consumer.** We use Mathlib only through
  its lemmas, never by unfolding its definitions, and that includes bridge
  proofs. This keeps our code robust against Mathlib updates.
- Underspecification is proven, not promised. Where a computed value sits under
  an interface, choose a specification with at most one answer (a subsingleton),
  so that swapping implementations is a theorem.
- Why: changes stay local. This is what keeps formal code agile.

## Repository layout

Suggested; adjust names if Lake demands it, but keep the dependency rules.

```
Understory/Core/    verdicts, interface/construction pattern, certify — imports Lean core only
Understory/Graph/   constructions and bridge theorems under Mathlib concepts — imports Core + Mathlib
PoV/                the consumer: concrete graphs, tests, benchmarks — imports the public API only
reference/lean-understory-kindling/
                    the original proof of concept (frozen, read-only, not built)
docs/               decisions.md, corrections.md, benchmarks.md, pitch.md
docs/prompts/       assignments, numbered; once fired they are history, not instructions
ai-scratchpad/      working notes written by the AI: fallible, not endorsed, not for the user
scripts/            check-imports.sh and benchmark scripts
```

Dependency rules, enforced by `scripts/check-imports.sh` on every build:
- `Core` never imports Mathlib. `Graph` never imports `PoV`. Nothing imports `reference/`.
- `PoV` imports only public modules of Understory, never internal ones.
- Each module has minimal imports and is independently checkable.

## Hard rules

- No `sorry`. No custom axioms. No `native_decide` (it adds `Lean.ofReduceBool`).
- Mathlib is a dependency only: never fork or patch it. Pin the version; the
  toolchain follows Mathlib.
- **The build is the test.** Messages, successes and failures are pinned with
  `#guard_msgs`; axiom footprints with `#print axioms`. No claim and no commit
  without a green build.
- **Kernel versus runtime.** Only kernel computation can carry a proof. Code the
  kernel must run uses structural recursion on a bound, not well-founded
  recursion. Expect `Finset` and instances from `open Classical` sections to be
  slow or to block the kernel; prefer list-based checkers bridged to Mathlib.
- **Untrusted proposal, trusted check.** Search may be fast and unverified; the
  kernel checks the result. `certify` shows nothing the kernel has not checked.
  Keep the unverifiable seam minimal.
- **Errors are certificates, not labels.** A verdict proves something in each
  branch: the claim, a certificate that refutes it, or a named weaker statement.
- **Classical assumptions are local hypotheses**, never inserted to close a gap:
  `Classical.choice` makes results noncomputable and defeats the purpose.
- Never use Mathlib API names from memory. Check them in the pinned version
  (`grep`, `#check`) before relying on them.

## Terminology

- **interface** — a classical definition or statement that downstream relies on.
- **construction** — what the constructivist supplies: an implementation plus
  its flattening proof, registered via `@[construction]` or a class
  `Construction` (choose one and record why in `docs/decisions.md`).
- **flattening proof** — the proof that a construction realises the interface.
- **bridge theorem** — an equation between an untouched definition and a
  computable one.
- **verdict** — the object-level result of a check: proved, refuted with
  certificate, or undecided with a proven weaker statement.
- **`certify`** — the tactic the classical user calls. Do not name a tactic
  `construction`: "by construction" means "follows directly from the
  definition", and it is too close to Lean's `constructor`.

## Honesty

- Every report and README separates four things: **proven**, **checked by the
  build**, **trusted** (the seam, the kernel, the compiler), and **empirical**
  (timings, friction).
- Measure before claiming a gain, and compare with what Mathlib already does
  (`decide`, existing instances, `norm_num`) on the same examples.
- Record anything once claimed and later refuted in `docs/corrections.md`.
- Pitches, including `docs/pitch.md`, are hypotheses. Results decide what holds.
- If a concept cannot become a computing interface, that is a result: make the
  boundary explicit.

## Workflow

- Work in phases with explicit stop points. When the direction changes, propose
  first and wait for approval.
- Small steps, each with a green build. Commit only on explicit request, or as
  part of a plan agreed beforehand. When a commit seems warranted, say so, and
  keep reminding until it is decided. Never push without approval.
- At each stop point, draft the next assignment as `docs/prompts/NN-name.md`,
  whose first line is `Draft by AI, not yet fired.`; only the user fires it.
  Prompts stay thin (goal, scope, stop point, what counts as done, and a short
  tentative horizon of what later steps need from this one, marked as not in
  scope): a fresh session must be able to carry one out from the repository
  alone. Prompts never tell a session to read this file; it comes with every
  session anyway.
- A session given a prompt from `docs/prompts/` as its assignment, whose first
  line is not yet a "Fired on" line, first replaces that first line with
  `Fired on YYYY-MM-DD; historical. Lasting rules are in CLAUDE.md.` (today's
  date). Reading a prompt for reference, or drafting one, does not fire it.
- Do not widen the scope silently. After each concept, report briefly: what
  works, what does not, what was measured.
- Record design decisions in `docs/decisions.md` so later sessions do not
  reopen them.
- Keep this file an interface: contracts only. Details belong in `docs/`.

## AI working notes

- `ai-scratchpad/` holds notes the AI writes to serve the user. They are
  fallible and not endorsed by the user: nothing in them counts as a decision
  or a checked fact until verified.
- Read `ai-scratchpad/README.md` before: starting or resuming work on a phase,
  notion or design question; writing working material not meant for the user;
  relying on, changing or moving anything in that folder.

## Style

- English everywhere: code, comments, docs.
- Main theorems and definitions should read as evident.
- Follow Mathlib naming conventions.
- License: Apache 2.0.
