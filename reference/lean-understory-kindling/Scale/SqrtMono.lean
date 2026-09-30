import Scale.Sqrt
import Kindling.Mono
open Kindling

/-- Added: `SqGe m` is monotone. One instance; the rest follows. -/
instance (m : Nat) : Monotone (SqGe m) :=
  ⟨fun hab h => Nat.le_trans h (Nat.mul_le_mul hab hab)⟩

/-- The same definition, now with the bisection implementation underneath. -/
def csqrtM (m : Nat) : Nat := least (SqGe m)

/-- Provably the same function. -/
theorem csqrtM_eq (m : Nat) : csqrtM m = csqrt m := least_congr _ _ _
