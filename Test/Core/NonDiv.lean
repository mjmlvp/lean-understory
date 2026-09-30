import Understory.Core

/-!
# Core tests — the least non-divisor, with a constructive implementation

Ported from the proof of concept (`Demo/`, constructive variant). The classical
user's definitions, one block added by the constructivist, downstream theorems
that use only the interface, a pinned Mathlib-style definition, and the pinned
messages. The build is the test.
-/

open Understory

namespace Test.NonDiv
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

/-! ## Added by the constructivist

A bound with its proof. Nothing else changes, neither in this file nor downstream. -/

theorem succ_not_dvd (m : Nat) [NeZero m] : ¬(m + 1) ∣ m := fun ⟨k, hk⟩ =>
  match k, hk with
  | 0, hk     => NeZero.ne m hk
  | k + 1, hk => Nat.not_succ_le_self m
      (Nat.le_trans (Nat.le_add_left (m + 1) ((m + 1) * k)) (Nat.le_of_eq hk.symm))

instance (m : Nat) [NeZero m] : Bounded (NonDiv m) :=
  ⟨m + 1, m + 1, Nat.le_refl _, Nat.succ_pos m, succ_not_dvd m⟩

/-- The least non-divisor of `m`. -/
def lnd (m : Nat) [NeZero m] : Nat := least (NonDiv m)

theorem lnd_nonDiv (m : Nat) [NeZero m] : NonDiv m (lnd m) :=
  (least_spec (NonDiv m)).holds

theorem lnd_not_dvd (m : Nat) [NeZero m] : ¬lnd m ∣ m :=
  (lnd_nonDiv m).2

theorem dvd_of_lt_lnd (m : Nat) [NeZero m] {k : Nat} (hk : 0 < k) (h : k < lnd m) : k ∣ m :=
  Decidable.byContradiction fun hn => (least_spec (NonDiv m)).below k h ⟨hk, hn⟩

theorem two_le_lnd (m : Nat) [NeZero m] : 2 ≤ lnd m :=
  match h : lnd m with
  | 0     => by have := (lnd_nonDiv m).1; rw [h] at this; exact absurd this (Nat.lt_irrefl 0)
  | 1     => absurd (by rw [h]; exact Nat.one_dvd m) (lnd_not_dvd m)
  | _ + 2 => Nat.le_add_left 2 _

/-- A downstream definition: the least non-divisors of `1, …, k`. -/
def lndTable (k : Nat) : List Nat := (List.range k).map fun i => lnd (i + 1)

/-- The least non-divisor, pinned to the classical search. -/
def lnd' (m : Nat) [NeZero m] : Nat := @least (NonDiv m) (Search.ofSolvable (NonDiv m))

/-- Still the same value as `lnd`, whatever the implementation there. -/
theorem lnd'_eq_lnd (m : Nat) [NeZero m] : lnd' m = lnd m := least_congr _ _ _

/-! ## Computation: now in the kernel too -/

/-- info: 5 -/
#guard_msgs in #eval lnd 12

example : lnd 12 = 5 := by decide +kernel

example : lndTable 10 = [2, 3, 2, 3, 2, 4, 2, 3, 2, 3] := by decide +kernel

/-! ## Messages: refutations with a certificate, in the user's terms -/

example : lnd 12 = 5 := by certify

/--
error: Refuted (checked by the kernel):
  lnd 12 = 5
  ¬5 ≤ 4
-/
#guard_msgs in example : lnd 12 ≤ 4 := by certify

/--
error: Refuted (checked by the kernel):
  lnd 30 = 4
  ¬4 = 7
-/
#guard_msgs in example : lnd 30 = 7 := by certify

/-! ## Axioms: `Classical.choice` is gone

What remains is `propext`, which comes from `Nat.decidable_dvd` in core Lean, not
from the framework. -/

/-- info: 'Test.NonDiv.lnd' depends on axioms: [propext] -/
#guard_msgs in #print axioms lnd

/-- info: 'Test.NonDiv.lnd_nonDiv' depends on axioms: [propext] -/
#guard_msgs in #print axioms lnd_nonDiv

/-! ## The Mathlib test: a pinned definition, left untouched

The kernel cannot evaluate `lnd'`: for that, the definition itself would have
to change. -/

/--
error: Tactic `decide` failed for proposition
  lnd' 12 = 5
because its `Decidable` instance
  instDecidableEqNat (lnd' 12) 5
did not reduce to `isTrue` or `isFalse`.

Reduction got stuck at the `Decidable` instance
  match h : (lnd' 12).beq 5 with
  | true => isTrue ⋯
  | false => isFalse ⋯
-/
#guard_msgs in example : lnd' 12 = 5 := by decide +kernel

/-! But diagnosis and proof *do* work, through `least_congr`: -/

example : lnd' 12 = 5 := by certify

/--
error: Refuted (checked by the kernel):
  lnd' 12 = 5
  ¬5 ≤ 4
-/
#guard_msgs in example : lnd' 12 ≤ 4 := by certify

example : lnd' 12 = 5 := by rw [lnd'_eq_lnd]; decide +kernel

end Test.NonDiv
