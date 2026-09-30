/-!
# Layer 1 — Verdicts

A verdict about `P` is a certificate, not a label. Every branch carries a
proof, and what a message may claim is exactly the proposition that branch
proves (`Verdict.says`).

* `proved`  — a proof of `P`;
* `refuted` — a certificate `C`, a proof of it, and `C → ¬P`;
* `unknown` — a named statement `W` with a proof. `W` is not `¬P`: the third
  branch cannot be read as a refutation, but it does not lie either.

Imports only `Init`; uses no axioms.
-/

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

/-- The verdict of an evaluation: knowing `t = n`, `G n` decides `G t`. -/
def ofEval (G : Nat → Prop) (t n : Nat) (hv : t = n) [Decidable (G n)] : Verdict (G t) :=
  if h : G n then proved (hv ▸ h)
  else refuted (t = n ∧ ¬G n) ⟨hv, h⟩ (fun ⟨e, h⟩ g => h (e ▸ g))

/-- The verdict after rewriting: knowing `G = G'` with `G'` decidable, `G'`
decides `G`. A refutation carries the rewrites `C` along. -/
def ofRewrite {G G' : Prop} (h : G = G') [Decidable G'] (C : Prop) (c : C) : Verdict G :=
  if h' : G' then proved (h ▸ h')
  else refuted (C ∧ ¬G') ⟨c, h'⟩ (fun ⟨_, n⟩ g => n (h ▸ g))

end Verdict
end Understory
