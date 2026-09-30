import Demo.Downstream
import Demo.MathlibStyle
import Kindling.Certify

/-!
# Tests — classical interface only

The build is the test: every message and every axiom footprint is pinned.
-/

open Kindling

/-! ## Computation: in compiled code yes, in the kernel no

The classical existence proof only serves termination and is erased. `#eval`
therefore computes, without `noncomputable`. The kernel gets stuck. -/

/-- info: 5 -/
#guard_msgs in #eval lnd 12

/-- info: [2, 3, 2, 3, 2, 4, 2, 3, 2, 3] -/
#guard_msgs in #eval lndTable 10

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
  IsLeast (NonDiv 12) (lnd 12)
No implementation found that computes in the kernel (for example an instance Bounded (NonDiv 12)).
-/
#guard_msgs in example : lnd 12 ≤ 4 := by certify

/-! ## Axioms: the classical proof is visible -/

/-- info: 'lnd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms lnd
