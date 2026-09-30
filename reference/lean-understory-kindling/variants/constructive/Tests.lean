import Demo.Downstream
import Demo.MathlibStyle
import Kindling.Certify

/-!
# Tests — with a constructive implementation

The build is the test: every message and every axiom footprint is pinned.
-/

open Kindling

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

/-- info: 'lnd' depends on axioms: [propext] -/
#guard_msgs in #print axioms lnd

/-- info: 'lnd_nonDiv' depends on axioms: [propext] -/
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
