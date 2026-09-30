/-!
# Layer 0 — Flattening

The classical reading of a proposition is its ¬¬-shadow. `¬¬` is an idempotent
monad on `Prop` (the ¬¬-topology); its unit `P → ¬¬P` is the flattening. The
stable propositions are exactly its fixed points.

Imports only `Init`; uses no axioms.
-/

namespace Kindling

/-- `P` is stable: the classical shadow of `P` implies `P`. -/
def Stable (P : Prop) : Prop := ¬¬P → P

/-- Flattening: constructively proven means classically true. -/
theorem flatten {P : Prop} (h : P) : ¬¬P := fun n => n h

/-- The reflector is idempotent. -/
theorem flat_idem {P : Prop} : ¬¬¬¬P ↔ ¬¬P :=
  ⟨fun h n => h (fun k => k n), flatten⟩

/-- Decidable propositions are stable: there the correspondence is an equivalence. -/
theorem stable_of_decidable (P : Prop) [Decidable P] : Stable P :=
  fun h => Decidable.byContradiction h

/-- Negations are stable: refutations transfer without loss. -/
theorem stable_not (P : Prop) : Stable (¬P) :=
  fun h p => h (fun n => n p)

/-- The formal boundary: equivalence everywhere is exactly classical logic. -/
theorem stable_everywhere_iff_em : (∀ P, Stable P) ↔ (∀ P : Prop, P ∨ ¬P) :=
  ⟨fun h _ => h _ (fun n => n (Or.inr (fun p => n (Or.inl p)))),
   fun em P hn => (em P).elim id (fun np => absurd np hn)⟩

/-- Local transfer: a classical refutation that uses excluded middle for one
named proposition `Q` is already a constructive refutation. -/
theorem refute_of_local_em {P Q : Prop} (h : (Q ∨ ¬Q) → ¬P) : ¬P :=
  fun p => (fun n : ¬(Q ∨ ¬Q) => n (Or.inr (fun q => n (Or.inl q)))) (fun e => h e p)

/-- Markov from one instance of excluded middle: for an ∃ the shadow suffices,
once excluded middle is available for exactly that ∃. -/
theorem markov {α : Sort _} {p : α → Prop}
    (em : (∃ a, p a) ∨ ¬(∃ a, p a)) (h : ¬¬∃ a, p a) : ∃ a, p a :=
  em.elim id (fun n => absurd n h)

end Kindling
