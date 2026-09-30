/-!
# Layer 1 — Verdicts

A verdict about `P` is a certificate, not a label. Every branch carries a
proof, and what a message may claim is exactly the proposition that branch
proves (`Verdict.says`).

* `proved`  — a proof of `P`;
* `refuted` — a certificate `C`, a proof of it, and `C → ¬P`;
* `unknown` — a named statement `W` with a proof. `W` is not `¬P`: the third
  branch cannot be read as a refutation, but it does not lie either.

Main theorems: `Verdict.says_true` (a verdict never claims anything false) and
`Verdict.branch_agree` (two verdicts on one claim never contradict each other).
`Verdict.ofValue` substitutes a checked value; `Verdict.ofValue_indep` shows
the result does not depend on how the value was found.

Imports only `Init`; uses no axioms.
-/

universe u

namespace Understory

inductive Verdict (P : Prop) : Type where
  | proved  (h : P)
  | refuted (C : Prop) (c : C) (sound : C → ¬P)
  | unknown (W : Prop) (w : W)

namespace Verdict

/-- What the verdict claims. -/
def says {P : Prop} : Verdict P → Prop
  | proved _      => P
  | refuted C _ _ => C
  | unknown W _   => W

/-- A verdict never claims anything false. -/
theorem says_true {P : Prop} : (v : Verdict P) → v.says
  | proved h      => h
  | refuted _ c _ => c
  | unknown _ w   => w

/-- A refutation is a proof of `¬P`. -/
theorem not_of_refuted {P C : Prop} {c : C} {s : C → ¬P} {v : Verdict P}
    (_ : v = refuted C c s) : ¬P := s c

/-- Transport along a proven equivalence. -/
def transport {P Q : Prop} (e : P ↔ Q) : Verdict P → Verdict Q
  | proved h      => proved (e.mp h)
  | refuted C c s => refuted C c (fun c q => s c (e.mpr q))
  | unknown W w   => unknown W w

/-- Naturality: transport leaves certificates untouched. What a refutation
claims depends only on the certificate, not on the route to it. -/
theorem says_transport_refuted {P Q : Prop} (e : P ↔ Q) (C : Prop) (c : C) (s : C → ¬P) :
    ((refuted C c s).transport e).says = C := rfl

/-! ## Branches, and branch agreement -/

/-- Which branch a verdict is in, forgetting the certificate. -/
inductive Branch where
  | proved
  | refuted
  | unknown

/-- The branch of a verdict. -/
def branch {P : Prop} : Verdict P → Branch
  | proved _      => .proved
  | refuted _ _ _ => .refuted
  | unknown _ _   => .unknown

/-- A verdict in the branch `proved` proves `P`. -/
theorem of_branch_proved {P : Prop} : (v : Verdict P) → v.branch = .proved → P
  | proved h, _ => h

/-- A verdict in the branch `refuted` proves `¬P`. -/
theorem not_of_branch_refuted {P : Prop} : (v : Verdict P) → v.branch = .refuted → ¬P
  | refuted _ c s, _ => s c

/-- Branch agreement: two verdicts on one claim never contradict each other,
whatever produced them. Only `unknown` may differ from a decisive branch. -/
theorem branch_agree {P : Prop} (v w : Verdict P) (hv : v.branch = .proved) :
    w.branch ≠ .refuted :=
  fun hw => not_of_branch_refuted w hw (of_branch_proved v hv)

/-! ## Values -/

/-- The verdict after substituting a checked value: knowing `t = n`, a verdict
on `G n` is a verdict on `G t`. A refutation or an unknown carries `t = n`
along, so that the message says which values were used. -/
def ofValue {α : Sort u} (G : α → Prop) (t n : α) (h : t = n) : Verdict (G n) → Verdict (G t)
  | proved g      => proved (h ▸ g)
  | refuted C c s => refuted (t = n ∧ C) ⟨h, c⟩ (fun ⟨e, c⟩ g => s c (e ▸ g))
  | unknown W w   => unknown (t = n ∧ W) ⟨h, w⟩

/-- Values are canonical: whichever checked value was found for `t`, the
verdict is the same. Messages about values therefore do not depend on the
implementation that found them. -/
theorem ofValue_indep {α : Sort u} (G : α → Prop) (t n₁ n₂ : α) (h₁ : t = n₁) (h₂ : t = n₂)
    (V : (n : α) → Verdict (G n)) : ofValue G t n₁ h₁ (V n₁) = ofValue G t n₂ h₂ (V n₂) := by
  cases h₁; cases h₂; rfl

end Verdict
end Understory
