import Demo.Spec

/-!
# Demo — two implementations side by side, in one build

The classical search and a bounded search under the same interface. That they
cannot be told apart is a theorem, not an observation.
-/

open Kindling

namespace TwoImpls

theorem succ_not_dvd (m : Nat) [NeZero m] : ¬(m + 1) ∣ m := fun ⟨k, hk⟩ =>
  match k, hk with
  | 0, hk     => NeZero.ne m hk
  | k + 1, hk => Nat.not_succ_le_self m
      (Nat.le_trans (Nat.le_add_left (m + 1) ((m + 1) * k)) (Nat.le_of_eq hk.symm))

/-- Implementation 1: classical existence only. -/
@[instance_reducible] def viaClassical (m : Nat) [NeZero m] : Search (NonDiv m) := Search.ofSolvable (NonDiv m)

/-- Implementation 2: bounded search, with a looser bound `m + m`. -/
@[instance_reducible] def viaBound (m : Nat) [NeZero m] : Search (NonDiv m) :=
  @Search.ofBounded (NonDiv m) _
    ⟨m + m, m + 1, Nat.add_le_add_left (Nat.pos_of_ne_zero (NeZero.ne m)) m,
      Nat.succ_pos m, succ_not_dvd m⟩

/-- The same value. -/
theorem same_value (m : Nat) [NeZero m] :
    @least _ (viaClassical m) = @least _ (viaBound m) :=
  least_congr _ _ _

/-- The same verdict, hence the same message, for every claim. -/
theorem same_verdict (m : Nat) [NeZero m] (inst : Search (NonDiv m))
    (Q : Nat → Prop) [DecidablePred Q] :
    judge _ inst (viaClassical m) Q = judge _ inst (viaBound m) Q :=
  judge_indep _ _ _ _ Q

/-- A downstream theorem, polymorphic in the implementation. -/
theorem not_dvd_any (m : Nat) [NeZero m] (s : Search (NonDiv m)) : ¬(@least _ s) ∣ m :=
  (@least_spec _ s).holds.2

/-- The bounded implementation computes in the kernel. -/
example : @least _ (viaBound 12) = 5 := by decide +kernel

/-- The classical one does not, but through the theorem its value is computed anyway. -/
example : @least _ (viaClassical 12) = 5 := by rw [same_value]; decide +kernel

end TwoImpls
