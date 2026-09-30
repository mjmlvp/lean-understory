import Demo.Spec

/-!
# Demo — a pinned, Mathlib-style definition

Like `Nat.find` in Mathlib: the definition is fixed to the classical existence
proof and does not go through instance resolution. The constructivist may not
touch this file. What can still be achieved? See the tests.
-/

open Kindling

/-- The least non-divisor, pinned to the classical search. -/
def lnd' (m : Nat) [NeZero m] : Nat := @least (NonDiv m) (Search.ofSolvable (NonDiv m))

/-- Still the same value as `lnd`, whatever the implementation there. -/
theorem lnd'_eq_lnd (m : Nat) [NeZero m] : lnd' m = lnd m := least_congr _ _ _
