import Understory.Core

/-!
# Core tests — the framework is axiom-free
-/

open Understory
/-- info: 'Understory.stable_everywhere_iff_em' does not depend on any axioms -/
#guard_msgs in #print axioms stable_everywhere_iff_em

/-- info: 'Understory.refute_of_local_em' does not depend on any axioms -/
#guard_msgs in #print axioms refute_of_local_em

/-- info: 'Understory.markov' does not depend on any axioms -/
#guard_msgs in #print axioms markov

/-- info: 'Understory.Verdict.says_true' does not depend on any axioms -/
#guard_msgs in #print axioms Verdict.says_true

/-- info: 'Understory.Verdict.ofEval' does not depend on any axioms -/
#guard_msgs in #print axioms Verdict.ofEval

/-- info: 'Understory.Search.subsingleton' does not depend on any axioms -/
#guard_msgs in #print axioms Search.subsingleton

/-- info: 'Understory.least_congr' does not depend on any axioms -/
#guard_msgs in #print axioms least_congr

/-- info: 'Understory.Search.ofBounded' does not depend on any axioms -/
#guard_msgs in #print axioms Search.ofBounded

/-- info: 'Understory.Search.ofSolvable' does not depend on any axioms -/
#guard_msgs in #print axioms Search.ofSolvable

/-- info: 'Understory.least_eq_bounded' does not depend on any axioms -/
#guard_msgs in #print axioms least_eq_bounded

/-- info: 'Understory.judge_indep' does not depend on any axioms -/
#guard_msgs in #print axioms judge_indep

/-- info: 'Understory.bisect_spec' does not depend on any axioms -/
#guard_msgs in #print axioms bisect_spec

/-- info: 'Understory.Search.ofUpwardClosed' does not depend on any axioms -/
#guard_msgs in #print axioms Search.ofUpwardClosed
