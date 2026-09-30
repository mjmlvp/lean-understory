import Understory.Core

/-!
# Core tests — the main theorems, and the framework is axiom-free

First the main theorem of each stage, restated so that the build pins its
statement; then the axiom footprints.
-/

open Understory

/-! ## Stage 1, verdicts: a verdict never claims anything false, and two
verdicts on one claim never contradict each other. -/

example {P : Prop} (v : Verdict P) : v.says := v.says_true

example {P : Prop} (v w : Verdict P) (hv : v.branch = .proved) : w.branch ≠ .refuted :=
  Verdict.branch_agree v w hv

/-- A checked value leaves one verdict, however it was found. -/
example {α : Type} (G : α → Prop) (t n₁ n₂ : α) (h₁ : t = n₁) (h₂ : t = n₂)
    (V : (n : α) → Verdict (G n)) :
    Verdict.ofValue G t n₁ h₁ (V n₁) = Verdict.ofValue G t n₂ h₂ (V n₂) :=
  Verdict.ofValue_indep G t n₁ n₂ h₁ h₂ V

/-! ## Stage 2, constructions: no swap of construction flips a verdict; a
construction that accepts only one piece of evidence delivers one verdict. -/

example {P : Prop} (c₁ c₂ : Construction P) (e : c₁.Evidence) (he : c₁.check e = true)
    (r : c₂.Counterevidence) (hr : c₂.checkCounter r = true) : False :=
  Construction.verdicts_agree c₁ c₂ e he r hr

example {P : Prop} (c : Construction P) (hE : c.UniqueEvidence) (hC : c.UniqueCounter)
    (v w : Verdict P) (hv : c.Decides v) (hw : c.Decides w) : v = w :=
  Construction.Decides.unique hE hC hv hw

/-! ## Stage 3, least witnesses as a construction: the implementation does not
change the verdict on a claim `Q (least p)`, among implementations whose check
the kernel ran. -/

example (p : Nat → Prop) (inst s₁ s₂ : Search p) (Q : Nat → Prop) [DecidablePred Q]
    (h₁ : @least p inst = s₁.val) (h₂ : @least p inst = s₂.val)
    (v₁ : Verdict (Q s₁.val)) (v₂ : Verdict (Q s₂.val))
    (hv₁ : (Construction.ofDecidable (Q s₁.val)).Decides v₁)
    (hv₂ : (Construction.ofDecidable (Q s₂.val)).Decides v₂) :
    Verdict.ofValue Q (@least p inst) s₁.val h₁ v₁ =
      Verdict.ofValue Q (@least p inst) s₂.val h₂ v₂ :=
  least_message_indep p inst s₁ s₂ Q h₁ h₂ v₁ v₂ hv₁ hv₂

/-- The value itself does not depend on the implementation. -/
example (p : Nat → Prop) (s₁ s₂ : Search p) : @least p s₁ = @least p s₂ := least_congr p s₁ s₂

/-! ## Axiom footprints -/
/-- info: 'Understory.stable_everywhere_iff_em' does not depend on any axioms -/
#guard_msgs in #print axioms stable_everywhere_iff_em

/-- info: 'Understory.refute_of_local_em' does not depend on any axioms -/
#guard_msgs in #print axioms refute_of_local_em

/-- info: 'Understory.markov' does not depend on any axioms -/
#guard_msgs in #print axioms markov

/-- info: 'Understory.Verdict.says_true' does not depend on any axioms -/
#guard_msgs in #print axioms Verdict.says_true

/-- info: 'Understory.Verdict.branch_agree' does not depend on any axioms -/
#guard_msgs in #print axioms Verdict.branch_agree

/-- info: 'Understory.Verdict.ofValue_indep' does not depend on any axioms -/
#guard_msgs in #print axioms Verdict.ofValue_indep

/-- info: 'Understory.Construction.verdicts_agree' does not depend on any axioms -/
#guard_msgs in #print axioms Construction.verdicts_agree

/-- info: 'Understory.Construction.Decides.unique' does not depend on any axioms -/
#guard_msgs in #print axioms Construction.Decides.unique

/-- info: 'Understory.Construction.value_message_indep' does not depend on any axioms -/
#guard_msgs in #print axioms Construction.value_message_indep

/-- info: 'Understory.Construction.ofDecidable' does not depend on any axioms -/
#guard_msgs in #print axioms Construction.ofDecidable

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

/-- info: 'Understory.Construction.leastEq' does not depend on any axioms -/
#guard_msgs in #print axioms Construction.leastEq

/-- info: 'Understory.Construction.leastEq_ofCounter_indep' does not depend on any axioms -/
#guard_msgs in #print axioms Construction.leastEq_ofCounter_indep

/-- info: 'Understory.least_message_indep' does not depend on any axioms -/
#guard_msgs in #print axioms least_message_indep

/-- info: 'Understory.bisect_spec' does not depend on any axioms -/
#guard_msgs in #print axioms bisect_spec

/-- info: 'Understory.Search.ofUpwardClosed' does not depend on any axioms -/
#guard_msgs in #print axioms Search.ofUpwardClosed
