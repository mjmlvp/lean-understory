import Kindling.Least

/-!
# Demo — the classical user's module

Written classically: a definition, a proof by contradiction, and the least
non-divisor. Nothing constructive in sight.
-/

open Kindling

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
