import Kindling

/-!
# Audit — the framework is axiom-free

These tests are identical in both variants.
-/

open Kindling

/-- info: 'Kindling.stable_everywhere_iff_em' does not depend on any axioms -/
#guard_msgs in #print axioms stable_everywhere_iff_em

/-- info: 'Kindling.refute_of_local_em' does not depend on any axioms -/
#guard_msgs in #print axioms refute_of_local_em

/-- info: 'Kindling.markov' does not depend on any axioms -/
#guard_msgs in #print axioms markov

/-- info: 'Kindling.Verdict.says_true' does not depend on any axioms -/
#guard_msgs in #print axioms Verdict.says_true

/-- info: 'Kindling.Verdict.ofEval' does not depend on any axioms -/
#guard_msgs in #print axioms Verdict.ofEval

/-- info: 'Kindling.Search.subsingleton' does not depend on any axioms -/
#guard_msgs in #print axioms Search.subsingleton

/-- info: 'Kindling.least_congr' does not depend on any axioms -/
#guard_msgs in #print axioms least_congr

/-- info: 'Kindling.Search.ofBounded' does not depend on any axioms -/
#guard_msgs in #print axioms Search.ofBounded

/-- info: 'Kindling.Search.ofSolvable' does not depend on any axioms -/
#guard_msgs in #print axioms Search.ofSolvable

/-- info: 'Kindling.least_eq_bounded' does not depend on any axioms -/
#guard_msgs in #print axioms least_eq_bounded

/-- info: 'Kindling.judge_indep' does not depend on any axioms -/
#guard_msgs in #print axioms judge_indep

/-- info: 'Kindling.bisect_spec' does not depend on any axioms -/
#guard_msgs in #print axioms bisect_spec

/-- info: 'Kindling.Search.ofMonotone' does not depend on any axioms -/
#guard_msgs in #print axioms Search.ofMonotone
