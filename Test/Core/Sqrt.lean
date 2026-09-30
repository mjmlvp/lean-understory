import Understory.Core

/-!
# Core tests — ⌈√m⌉, bounded search and bisection under one interface

Ported from the proof of concept (`Scale/`). `csqrt` uses bounded search (linear
in the witness), `csqrtM` bisection (logarithmic). That they are the same
function is a theorem (`csqrtM_eq`).
-/

open Understory

namespace Test.Sqrt
/-- `n` is large enough: `m ≤ n²`. The least such `n` is ⌈√m⌉, so the witness grows with `m`. -/
def SqGe (m n : Nat) : Prop := m ≤ n * n
instance (m : Nat) : DecidablePred (SqGe m) := fun n => inferInstanceAs (Decidable (m ≤ n * n))

theorem le_mul_self (m : Nat) : m ≤ m * m :=
  match m with
  | 0 => Nat.le_refl 0
  | k + 1 => Nat.le_mul_of_pos_right (k + 1) (Nat.succ_pos k)

instance (m : Nat) : Bounded (SqGe m) := ⟨m, m, Nat.le_refl m, le_mul_self m⟩

def csqrt (m : Nat) : Nat := least (SqGe m)

/-- Control case: witness `k` with the tight bound `k`. -/
def AtLeast (k n : Nat) : Prop := k ≤ n
instance (k : Nat) : DecidablePred (AtLeast k) := fun n => inferInstanceAs (Decidable (k ≤ n))
instance (k : Nat) : Bounded (AtLeast k) := ⟨k, k, Nat.le_refl k, Nat.le_refl k⟩
def firstFrom (k : Nat) : Nat := least (AtLeast k)

/-- Added: `SqGe m` is monotone. One instance; the rest follows. -/
instance (m : Nat) : UpwardClosed (SqGe m) :=
  ⟨fun hab h => Nat.le_trans h (Nat.mul_le_mul hab hab)⟩

/-- The same definition, now with the bisection implementation underneath. -/
def csqrtM (m : Nat) : Nat := least (SqGe m)

/-- Provably the same function. -/
theorem csqrtM_eq (m : Nat) : csqrtM m = csqrt m := least_congr _ _ _

/-! ## Bisection computes in the kernel, even for large numbers -/

example : csqrtM 1000000000000 = 1000000 := by decide +kernel

/-! ## The theorem carries the speed over to the fixed definition -/

example : csqrt 1000000000000 = 1000000 := by rw [← csqrtM_eq]; decide +kernel

/-! ## `certify` picks the best implementation itself, even under `csqrt` -/

example : csqrt 1000000000000 = 1000000 := by certify

/--
error: Refuted (checked by the kernel):
  csqrt 1000000000000 = 1000000
  ¬1000000 ≤ 999999
-/
#guard_msgs in example : csqrt 1000000000000 ≤ 999999 := by certify

/-! ## Several witnesses in one goal -/

example : csqrt 10000 + csqrtM 99 = 110 := by certify

/--
error: Refuted (checked by the kernel):
  csqrt 10000 = 100
  csqrtM 99 = 10
  ¬100 + 10 = 111
-/
#guard_msgs in example : csqrt 10000 + csqrtM 99 = 111 := by certify

/-! ## Axiom-free, on the user's side too -/

/-- info: 'Test.Sqrt.csqrtM' does not depend on any axioms -/
#guard_msgs in #print axioms csqrtM

/-- info: 'Test.Sqrt.csqrtM_eq' does not depend on any axioms -/
#guard_msgs in #print axioms csqrtM_eq

end Test.Sqrt
