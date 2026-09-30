import Understory.Core

/-!
# Core tests — the least non-divisor, classical interface only

Ported from the proof of concept (classical variant). Without a constructive
implementation the kernel cannot compute, and `certify` says so honestly.
-/

open Understory

namespace Test.Undecided
/-- `n` is a positive non-divisor of `m`. -/
def NonDiv (m n : Nat) : Prop := 0 < n ∧ ¬n ∣ m

instance (m : Nat) : DecidablePred (NonDiv m) :=
  fun n => inferInstanceAs (Decidable (0 < n ∧ ¬n ∣ m))

/-- Every positive number has a non-divisor. Suppose not: then `m + 1` divides
`m` as well, which is impossible. -/
theorem exists_nonDiv (m : Nat) [NeZero m] : ∃ n, NonDiv m n :=
  Classical.byContradiction fun H =>
    have : m + 1 ∣ m := Classical.byContradiction fun h => H ⟨m + 1, Nat.succ_pos m, h⟩
    Nat.not_succ_le_self m (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne m)) this)

instance (m : Nat) [NeZero m] : Solvable (NonDiv m) := ⟨exists_nonDiv m⟩

/-- The least non-divisor of `m`. -/
def lnd (m : Nat) [NeZero m] : Nat := least (NonDiv m)

/-! ## Computation: in compiled code yes, in the kernel no

The classical existence proof only serves termination and is erased. `#eval`
therefore computes, without `noncomputable`. The kernel gets stuck. -/

/-- info: 5 -/
#guard_msgs in #eval lnd 12

/--
error: Tactic `decide` failed for proposition
  lnd 12 = 5
because its `Decidable` instance
  instDecidableEqNat (lnd 12) 5
did not reduce to `isTrue` or `isFalse`.

Reduction got stuck at the `Decidable` instance
  match h : (lnd 12).beq 5 with
  | true => isTrue ⋯
  | false => isFalse ⋯
-/
#guard_msgs in example : lnd 12 = 5 := by decide +kernel

/-! ## Messages: honestly undecided, with what *is* proven -/

/--
error: Undecided: the kernel cannot evaluate lnd 12.
All that is proven:
  IsLeastWitness (NonDiv 12) (lnd 12)
No implementation found that computes in the kernel (for example an instance Bounded (NonDiv 12)).
-/
#guard_msgs in example : lnd 12 ≤ 4 := by certify

/-! ## Axioms: the classical proof is visible -/

/-- info: 'Test.Undecided.lnd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms lnd

end Test.Undecided
