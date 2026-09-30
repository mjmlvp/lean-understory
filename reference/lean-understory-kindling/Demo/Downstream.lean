import Demo.Spec

/-!
# Demo — downstream

This file does not change when the constructivist adds an implementation. It
uses only the interface: `lnd` and `least_spec`.
-/

open Kindling

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
