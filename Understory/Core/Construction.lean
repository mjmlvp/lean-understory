import Understory.Core.Verdict

/-!
# Layer 2 — Constructions for claims

A *construction* for a claim `P` is what a constructivist puts under it:

* evidence for `P` and counter-evidence against it, as data;
* a `Bool` checker for each, with its soundness proof;
* what counter-evidence *says*, in the user's vocabulary;
* an untrusted search that proposes evidence. Only compiled code runs it; the
  kernel runs only the checkers.

Evidence need not be unique: many pieces may pass the checker. What never
depends on the construction is the verdict: `verdicts_agree` shows that no
two constructions for the same claim contradict each other. Where the checker
accepts only one piece (`UniqueEvidence`, `UniqueCounter`), the message does
not depend on the search either (`Decides.unique`).

Registration is by instance of the class `Construction P` (decision D9).

Imports only `Init` and layer 1; uses no axioms.
-/

namespace Understory

/-- What an untrusted search proposes. -/
inductive Found (α β : Type) where
  | evidence (e : α)
  | counter (r : β)
  | nothing

/-- A construction for the claim `P`: evidence on both sides, checkers, and
their soundness proofs. -/
class Construction (P : Prop) where
  /-- Evidence for `P`. -/
  Evidence : Type
  /-- Evidence against `P`. -/
  Counterevidence : Type
  /-- The checker for evidence; the kernel runs it. -/
  check : Evidence → Bool
  sound : ∀ e, check e = true → P
  /-- The checker for counter-evidence; the kernel runs it. -/
  checkCounter : Counterevidence → Bool
  /-- What checked counter-evidence states, in the user's vocabulary. -/
  Says : Counterevidence → Prop
  says_of_check : ∀ r, checkCounter r = true → Says r
  refutes : ∀ r, Says r → ¬P
  /-- What stays proven when the kernel cannot run a check. -/
  Known : Prop := True
  known : Known := by exact trivial
  /-- Advice, not checked: an instance that would let the kernel run the check. -/
  hint : Option Type := none
  /-- The untrusted search. Only compiled code runs it; its result is checked. -/
  search : Found Evidence Counterevidence

/-- An untrusted guess for the value of the term `t`. It is only a proposal:
`certify` checks it through a construction for `t = value`. -/
class Proposer {α : Type} (t : α) where
  value : α

namespace Construction

variable {P : Prop}

/-! ## Verdicts from checked evidence -/

/-- The verdict from checked evidence. -/
def ofEvidence (c : Construction P) (e : c.Evidence) (h : c.check e = true) : Verdict P :=
  .proved (c.sound e h)

/-- The verdict from checked counter-evidence. -/
def ofCounter (c : Construction P) (r : c.Counterevidence) (h : c.checkCounter r = true) :
    Verdict P :=
  .refuted (c.Says r) (c.says_of_check r h) (c.refutes r)

/-- The verdict when nothing was checked: what stays proven. -/
def ofKnown (c : Construction P) : Verdict P :=
  .unknown c.Known c.known

/-- The verdicts a construction delivers from checked evidence. -/
inductive Decides (c : Construction P) : Verdict P → Prop
  | evidence (e : c.Evidence) (h : c.check e = true) : Decides c (c.ofEvidence e h)
  | counter (r : c.Counterevidence) (h : c.checkCounter r = true) : Decides c (c.ofCounter r h)

/-! ## Agreement -/

/-- No swap of construction flips a verdict: checked evidence for one and
checked counter-evidence for another never exist together. -/
theorem verdicts_agree (c₁ c₂ : Construction P) (e : c₁.Evidence) (he : c₁.check e = true)
    (r : c₂.Counterevidence) (hr : c₂.checkCounter r = true) : False :=
  Verdict.branch_agree (c₁.ofEvidence e he) (c₂.ofCounter r hr) rfl rfl

/-! ## Canonical evidence

Where a checker accepts at most one piece of evidence, the verdict, and so the
message, does not depend on which search found it (decision D5: canonical
evidence where it comes at no cost). -/

/-- The checker accepts at most one piece of evidence. -/
def UniqueEvidence (c : Construction P) : Prop :=
  ∀ e₁ e₂, c.check e₁ = true → c.check e₂ = true → e₁ = e₂

/-- The checker accepts at most one piece of counter-evidence. -/
def UniqueCounter (c : Construction P) : Prop :=
  ∀ r₁ r₂, c.checkCounter r₁ = true → c.checkCounter r₂ = true → r₁ = r₂

theorem ofEvidence_indep (c : Construction P) (hu : c.UniqueEvidence)
    (e₁ e₂ : c.Evidence) (h₁ : c.check e₁ = true) (h₂ : c.check e₂ = true) :
    c.ofEvidence e₁ h₁ = c.ofEvidence e₂ h₂ := by
  cases hu e₁ e₂ h₁ h₂; rfl

theorem ofCounter_indep (c : Construction P) (hu : c.UniqueCounter)
    (r₁ r₂ : c.Counterevidence) (h₁ : c.checkCounter r₁ = true) (h₂ : c.checkCounter r₂ = true) :
    c.ofCounter r₁ h₁ = c.ofCounter r₂ h₂ := by
  cases hu r₁ r₂ h₁ h₂; rfl

/-- A construction that is canonical on both sides delivers at most one verdict. -/
theorem Decides.unique {c : Construction P} (hE : c.UniqueEvidence) (hC : c.UniqueCounter)
    {v w : Verdict P} (hv : c.Decides v) (hw : c.Decides w) : v = w :=
  match hv, hw with
  | .evidence e₁ h₁, .evidence e₂ h₂ => ofEvidence_indep c hE e₁ e₂ h₁ h₂
  | .counter r₁ h₁, .counter r₂ h₂   => ofCounter_indep c hC r₁ r₂ h₁ h₂
  | .evidence e h, .counter r h'     => (verdicts_agree c c e h r h').elim
  | .counter r h', .evidence e h     => (verdicts_agree c c e h r h').elim

/-- A claim about a value, decided by a canonical construction, gets one
verdict: neither the checked value nor the search that found the evidence
changes it. -/
theorem value_message_indep {α : Type} (G : α → Prop) (t n₁ n₂ : α)
    (h₁ : t = n₁) (h₂ : t = n₂) (c : (n : α) → Construction (G n))
    (hE : ∀ n, (c n).UniqueEvidence) (hC : ∀ n, (c n).UniqueCounter)
    (v₁ : Verdict (G n₁)) (v₂ : Verdict (G n₂))
    (hv₁ : (c n₁).Decides v₁) (hv₂ : (c n₂).Decides v₂) :
    Verdict.ofValue G t n₁ h₁ v₁ = Verdict.ofValue G t n₂ h₂ v₂ := by
  cases h₁; cases h₂; cases Decides.unique (hE t) (hC t) hv₁ hv₂; rfl

/-! ## The fallback: a decidable claim -/

/-- Any decidable claim has a construction: the kernel decides it. -/
@[instance_reducible] def ofDecidable (P : Prop) [Decidable P] : Construction P where
  Evidence := Unit
  Counterevidence := Unit
  check _ := decide P
  sound _ h := of_decide_eq_true h
  checkCounter _ := decide (¬P)
  Says _ := ¬P
  says_of_check _ h := of_decide_eq_true h
  refutes _ h := h
  search := match decide P with
    | true  => .evidence ()
    | false => .counter ()

theorem ofDecidable_uniqueEvidence (P : Prop) [Decidable P] :
    (ofDecidable P).UniqueEvidence := fun _ _ _ _ => rfl

theorem ofDecidable_uniqueCounter (P : Prop) [Decidable P] :
    (ofDecidable P).UniqueCounter := fun _ _ _ _ => rfl

/-- The fallback, below every dedicated construction. -/
instance (priority := low) instOfDecidable (P : Prop) [Decidable P] : Construction P :=
  ofDecidable P

end Construction
end Understory
