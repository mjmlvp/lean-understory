import Kindling.Least
open Kindling

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
