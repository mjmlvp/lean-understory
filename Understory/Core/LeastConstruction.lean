import Understory.Core.Least
import Understory.Core.Construction

/-!
# Layer 4 — Least witnesses as a construction

The least-witness case of the proof of concept, as one construction among
others. `least p` is a value: its proposer guesses it with the best
implementation found, and the construction for `least p = n` checks the guess
by letting the kernel compute with that implementation. Bisection therefore
keeps its speed.

Every proof here uses only the specification of layer 3 (`least_congr`,
`least_eq_val`, `least_spec`), never the implementations.

Main theorem: `least_message_indep`. For a claim `Q (least p)`, the verdict
`certify` assembles is the same for every implementation whose check the kernel
can run. An implementation the kernel cannot run gives an undecided verdict
instead; the theorem makes no claim there.

Imports only `Init` and layers 1–3; uses no axioms.
-/

namespace Understory

/-- The value of `least p`, proposed by the best implementation `s` found.
`inst` is the implementation in the user's term; it is not recomputed. -/
instance instProposerLeast {p : Nat → Prop} {inst : Search p} [s : Search p] :
    Proposer (@least p inst) :=
  ⟨s.val⟩

namespace Construction

/-- The construction for `least p = n`, computing with the implementation `s`.
Evidence is nothing: the kernel computes `s.val` and compares. Counter-evidence
is the value `m` it finds instead. -/
@[instance_reducible] def leastEq (p : Nat → Prop) (inst s : Search p) (n : Nat) :
    Construction (@least p inst = n) where
  Evidence := Unit
  Counterevidence := Nat
  check _ := decide (s.val = n)
  sound _ h := (least_congr p inst s).trans ((@least_eq_val p s).trans (of_decide_eq_true h))
  checkCounter m := decide (s.val = m ∧ ¬m = n)
  Says m := @least p inst = m ∧ ¬m = n
  says_of_check _ h :=
    have h' := of_decide_eq_true h
    ⟨(least_congr p inst s).trans ((@least_eq_val p s).trans h'.1), h'.2⟩
  refutes _ := fun ⟨h₁, h₂⟩ h => h₂ (h₁.symm.trans h)
  Known := IsLeastWitness p (@least p inst)
  known := @least_spec p inst
  hint := some (Bounded p)
  search := if s.val = n then .evidence () else .counter s.val

theorem leastEq_uniqueEvidence (p : Nat → Prop) (inst s : Search p) (n : Nat) :
    (leastEq p inst s n).UniqueEvidence := fun _ _ _ _ => rfl

theorem leastEq_uniqueCounter (p : Nat → Prop) (inst s : Search p) (n : Nat) :
    (leastEq p inst s n).UniqueCounter := fun _ _ h₁ h₂ =>
  (of_decide_eq_true h₁).1.symm.trans (of_decide_eq_true h₂).1

/-- Swapping the implementation does not change a checked refutation of
`least p = n`: counter-evidence is the least witness itself, which is unique. -/
theorem leastEq_ofCounter_indep (p : Nat → Prop) (inst s₁ s₂ : Search p) (n : Nat)
    (m₁ m₂ : Nat) (h₁ : (leastEq p inst s₁ n).checkCounter m₁ = true)
    (h₂ : (leastEq p inst s₂ n).checkCounter m₂ = true) :
    (leastEq p inst s₁ n).ofCounter m₁ h₁ = (leastEq p inst s₂ n).ofCounter m₂ h₂ := by
  have e : m₁ = m₂ := ((leastEq p inst s₁ n).says_of_check m₁ h₁).1.symm.trans
    ((leastEq p inst s₂ n).says_of_check m₂ h₂).1
  cases e; rfl

/-- The construction `certify` finds for `least p = n`: the best implementation
computes. -/
instance instLeastEq {p : Nat → Prop} {inst : Search p} [s : Search p] {n : Nat} :
    Construction (@least p inst = n) :=
  leastEq p inst s n

end Construction

/-- The message on a claim `Q (least p)` does not depend on the implementation.
`certify` checks a value `least p = s.val` with some implementation `s`, then
decides `Q s.val` with the fallback construction. The implementation enters only
through the checked value, and checked values agree, so any two
implementations whose checks passed give the same verdict. -/
theorem least_message_indep (p : Nat → Prop) (inst s₁ s₂ : Search p) (Q : Nat → Prop)
    [DecidablePred Q] (h₁ : @least p inst = s₁.val) (h₂ : @least p inst = s₂.val)
    (v₁ : Verdict (Q s₁.val)) (v₂ : Verdict (Q s₂.val))
    (hv₁ : (Construction.ofDecidable (Q s₁.val)).Decides v₁)
    (hv₂ : (Construction.ofDecidable (Q s₂.val)).Decides v₂) :
    Verdict.ofValue Q (@least p inst) s₁.val h₁ v₁ = Verdict.ofValue Q (@least p inst) s₂.val h₂ v₂ :=
  Construction.value_message_indep Q _ _ _ h₁ h₂ (fun n => Construction.ofDecidable (Q n))
    (fun n => Construction.ofDecidable_uniqueEvidence (Q n))
    (fun n => Construction.ofDecidable_uniqueCounter (Q n)) v₁ v₂ hv₁ hv₂

end Understory
