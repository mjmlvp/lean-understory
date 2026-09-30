/-!
# Layer 3 — Least witnesses

The fragment: Σ⁰₁ over `Nat` with a decidable predicate and a canonical
witness, the least one.

* `Solvable p` — the classical interface (a `Prop` class: nothing to compute with);
* `Bounded p`  — a constructive implementation: a bound below which a witness lies;
* `Search p`   — the implementation type, with the specification in its type.

The design principle: `Search p` is a subsingleton. Representation independence
is therefore a theorem (`least_congr`), not an appeal to parametricity.
Downstream sees only `least p` and `least_spec`; `least` is irreducible, so
proofs cannot look through it.

Imports only `Init`; uses no axioms. How least witnesses become a construction
for `certify` is in `Understory.Core.LeastConstruction`.
-/

namespace Understory

/-- `n` is the least witness of `p`. -/
structure IsLeastWitness (p : Nat → Prop) (n : Nat) : Prop where
  holds : p n
  below : ∀ m, m < n → ¬p m

/-- There is at most one least witness. -/
theorem IsLeastWitness.unique {p : Nat → Prop} {a b : Nat}
    (ha : IsLeastWitness p a) (hb : IsLeastWitness p b) : a = b :=
  match Nat.lt_trichotomy a b with
  | .inl h        => absurd ha.holds (hb.below a h)
  | .inr (.inl h) => h
  | .inr (.inr h) => absurd hb.holds (ha.below b h)

/-- An implementation: a number, with its specification in its type. -/
class Search (p : Nat → Prop) where
  val  : Nat
  spec : IsLeastWitness p val

/-- There is at most one implementation. -/
instance Search.subsingleton {p : Nat → Prop} : Subsingleton (Search p) :=
  ⟨fun ⟨_, ha⟩ ⟨_, hb⟩ => by cases ha.unique hb; rfl⟩

/-- The classical interface: a witness exists. -/
class Solvable (p : Nat → Prop) : Prop where
  exists_ : ∃ n, p n

/-- A constructive implementation: a bound below which a witness lies. -/
class Bounded (p : Nat → Prop) where
  bound     : Nat
  exists_le : ∃ n, n ≤ bound ∧ p n

/-! ## The interface as downstream sees it -/

/-- The least witness. -/
def least (p : Nat → Prop) [s : Search p] : Nat := s.val

theorem least_eq_val (p : Nat → Prop) [s : Search p] : least p = s.val := rfl

attribute [irreducible] least

/-- The specification: everything downstream may know about `least p`. -/
theorem least_spec (p : Nat → Prop) [s : Search p] : IsLeastWitness p (least p) :=
  (least_eq_val p) ▸ s.spec

/-- Representation independence: `least p` does not depend on the implementation. -/
theorem least_congr (p : Nat → Prop) (s₁ s₂ : Search p) :
    @least p s₁ = @least p s₂ := by
  cases Subsingleton.elim s₁ s₂; rfl

/-- A number meeting the specification *is* `least p`. -/
theorem least_eq_of_isLeast {p : Nat → Prop} [Search p] {n : Nat}
    (h : IsLeastWitness p n) : least p = n :=
  (least_spec p).unique h

/-! ## Constructive implementation: bounded search

Structural recursion on the fuel, so that the kernel can compute. -/

section
variable (p : Nat → Prop)

/-- The first `n ≥ i` with `p n`, or `i + fuel` if there is none within `fuel` steps. -/
def scan [DecidablePred p] : (fuel i : Nat) → Nat
  | 0, i        => i
  | fuel + 1, i => if p i then i else scan fuel (i + 1)

theorem scan_spec [DecidablePred p] : ∀ (fuel i : Nat), (∀ m, m < i → ¬p m) →
    (scan p fuel i < i + fuel → p (scan p fuel i)) ∧ ∀ m, m < scan p fuel i → ¬p m
  | 0, i, h => ⟨fun hl => absurd hl (Nat.lt_irrefl i), h⟩
  | fuel + 1, i, h =>
    if hpi : p i then
      have e : scan p (fuel + 1) i = i := ite_eq_left hpi
      by rw [e]; exact ⟨fun _ => hpi, h⟩
    else
      have e : scan p (fuel + 1) i = scan p fuel (i + 1) := ite_eq_right hpi
      have ih := scan_spec fuel (i + 1) fun m hm =>
        match Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hm) with
        | .inl h' => h m h'
        | .inr h' => h' ▸ hpi
      by rw [e]; exact ⟨fun hl => ih.1 (Nat.lt_of_lt_of_le hl
        (Nat.le_of_eq (Nat.succ_add i fuel).symm)), ih.2⟩

/-- The implementation from a bound. -/
@[instance_reducible] def Search.ofBounded [DecidablePred p] [b : Bounded p] : Search p where
  val  := scan p (b.bound + 1) 0
  spec := by
    have hs := scan_spec p (b.bound + 1) 0 fun m hm => absurd hm (Nat.not_lt_zero m)
    refine ⟨hs.1 ?_, hs.2⟩
    obtain ⟨n, hn, hpn⟩ := b.exists_le
    exact Decidable.byContradiction fun hge =>
      hs.2 n (Nat.lt_of_lt_of_le (Nat.lt_succ_of_le hn)
        (Nat.le_trans (Nat.le_of_eq (Nat.zero_add _).symm) (Nat.not_lt.mp hge))) hpn

/-! ## The classical fallback: search driven by the existence proof

The existence proof only serves termination and is erased: this computes in
compiled code, but the kernel gets stuck as soon as the proof is classical. -/

/-- One step up, as long as no witness has been found. -/
def Step (a b : Nat) : Prop := a = b + 1 ∧ ∀ j, j ≤ b → ¬p j

theorem step_wf (h : ∃ n, p n) : WellFounded (Step p) := by
  obtain ⟨n, hn⟩ := h
  have key : ∀ d k, n ≤ k + d → Acc (Step p) k := by
    intro d
    induction d with
    | zero      => exact fun k hk => ⟨k, fun _ ⟨_, hb⟩ => absurd hn (hb n hk)⟩
    | succ d ih => exact fun k hk => ⟨k, fun _ ⟨ha, _⟩ =>
        ha ▸ ih (k + 1) (Nat.le_trans hk (Nat.le_of_eq (Nat.succ_add k d).symm))⟩
  exact ⟨fun k => key n k (Nat.le_add_left n k)⟩

theorem below_succ {k : Nat} (hk : ∀ j, j < k → ¬p j) (hpk : ¬p k) :
    ∀ j, j ≤ k → ¬p j := fun j hj =>
  match Nat.lt_or_eq_of_le hj with
  | .inl h => hk j h
  | .inr h => h ▸ hpk

/-- The implementation from the classical interface alone. -/
@[instance_reducible] def Search.ofSolvable [DecidablePred p] [Solvable p] : Search p :=
  (step_wf p Solvable.exists_).fix (C := fun k => (∀ j, j < k → ¬p j) → Search p)
    (fun k ih hk =>
      if hpk : p k then ⟨k, hpk, hk⟩
      else ih (k + 1) ⟨rfl, below_succ p hk hpk⟩
        (fun j hj => below_succ p hk hpk j (Nat.le_of_lt_succ hj)))
    0 (fun j hj => absurd hj (Nat.not_lt_zero j))

/-- Classical as a fallback, constructive where possible. -/
instance (priority := low) instSearchOfSolvable [DecidablePred p] [Solvable p] : Search p := Search.ofSolvable p
instance instSearchOfBounded [DecidablePred p] [Bounded p] : Search p := Search.ofBounded p

/-- The bridge the tactic uses: whatever implementation stands behind `least p`,
one may compute with the bounded one. -/
theorem least_eq_bounded [DecidablePred p] [Bounded p] (s : Search p) :
    @least p s = @Search.val p (Search.ofBounded p) :=
  (@least_eq_val p s).trans (congrArg (@Search.val p) (Subsingleton.elim s _))

end

end Understory
