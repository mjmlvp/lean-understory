import Scale.Sqrt
import Scale.SqrtMono
import Kindling.Certify

/-!
# Scaling tests — a faster implementation under the same interface

`csqrt` uses bounded search (linear in the witness), `csqrtM` uses bisection
(logarithmic). That they are the same function is a theorem (`csqrtM_eq`).
Measured timings are in the README; the build pins down *what* works.
-/

open Kindling

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

/-- info: 'csqrtM' does not depend on any axioms -/
#guard_msgs in #print axioms csqrtM

/-- info: 'csqrtM_eq' does not depend on any axioms -/
#guard_msgs in #print axioms csqrtM_eq
