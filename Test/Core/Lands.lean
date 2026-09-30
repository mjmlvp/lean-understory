import Understory.Core

/-!
# Core tests — a yes/no claim with evidence on both sides

Not about least witnesses: can steps of `fwd` forward and `back` back end
exactly `gap` ahead? Evidence for it is a number of steps each way; there are
many. Evidence against it is a common divisor of both step sizes that does not
divide the gap; there may be several. A construction supplies a search and the
checkers; `certify` does the rest.
-/

open Understory

namespace Test.Lands

/-- Steps of `fwd` forward and `back` back can end exactly `gap` ahead. -/
def Lands (fwd back gap : Nat) : Prop := ∃ x y, fwd * x = back * y + gap

/-- A common divisor of both step sizes divides every position reached. -/
theorem not_lands_of_dvd {a b c g : Nat} (ha : g ∣ a) (hb : g ∣ b) (hc : ¬g ∣ c) :
    ¬Lands a b c := fun ⟨x, y, h⟩ =>
  hc ((Nat.dvd_add_right (Nat.dvd_mul_right_of_dvd hb y)).mp
    (h ▸ Nat.dvd_mul_right_of_dvd ha x))

/-! ## Added by the constructivist -/

/-- Untrusted search: the greatest common divisor as counter-evidence, or a
bounded scan for the number of steps. It may miss; then `certify` says so. -/
def searchLands (a b c : Nat) : Found (Nat × Nat) Nat :=
  let g := Nat.gcd a b
  if c % g != 0 then .counter g
  else match (List.range (b + c + 1)).find? (fun x => c ≤ a * x && (a * x - c) % b == 0) with
    | some x => .evidence (x, (a * x - c) / b)
    | none   => .nothing

instance (a b c : Nat) : Construction (Lands a b c) where
  Evidence := Nat × Nat
  Counterevidence := Nat
  check e := decide (a * e.1 = b * e.2 + c)
  sound e h := ⟨e.1, e.2, of_decide_eq_true h⟩
  checkCounter g := decide (g ∣ a ∧ g ∣ b ∧ ¬g ∣ c)
  Says g := g ∣ a ∧ g ∣ b ∧ ¬g ∣ c
  says_of_check _ h := of_decide_eq_true h
  refutes _ := fun ⟨ha, hb, hc⟩ => not_lands_of_dvd ha hb hc
  search := searchLands a b c

/-! ## Proved and refuted -/

theorem lands_6_10_4 : Lands 6 10 4 := by certify

/--
error: Refuted (checked by the kernel):
  2 ∣ 6
  2 ∣ 10
  ¬2 ∣ 3
-/
#guard_msgs in example : Lands 6 10 3 := by certify

/--
error: Refuted (checked by the kernel):
  6 ∣ 12
  6 ∣ 18
  ¬6 ∣ 3
-/
#guard_msgs in example : Lands 12 18 3 := by certify

/-! ## Undecided: the search finds nothing

`Lands 0 2 4` is false, but no common divisor shows it, and the scan finds no
steps. `certify` says so instead of guessing. -/

/-- error: Undecided: no evidence found for Lands 0 2 4. -/
#guard_msgs in example : Lands 0 2 4 := by certify

/-! ## A second construction: different evidence, the same verdict

The same checkers with another search, one that looks for the smallest common
divisor that does not divide the gap. The certificate changes; the verdict
cannot (`Construction.verdicts_agree`). -/

/-- Search for the smallest suitable divisor first. -/
def searchSmallest (a b c : Nat) : Found (Nat × Nat) Nat :=
  let g := Nat.gcd a b
  match (List.range (g + 1)).find? (fun d => 1 < d && g % d == 0 && c % d != 0) with
  | some d => .counter d
  | none   => searchLands a b c

@[instance_reducible] def bySmallest (a b c : Nat) : Construction (Lands a b c) :=
  { (inferInstance : Construction (Lands a b c)) with search := searchSmallest a b c }

section
attribute [local instance high] bySmallest

theorem lands_6_10_4' : Lands 6 10 4 := by certify

/--
error: Refuted (checked by the kernel):
  2 ∣ 12
  2 ∣ 18
  ¬2 ∣ 3
-/
#guard_msgs in example : Lands 12 18 3 := by certify
end

/-! ## Axioms

`propext` comes from core Lean's divisibility on `Nat` (`Nat.decidable_dvd`,
`Nat.dvd_add_right`), not from the framework. A proof by `certify` carries the
footprint of the whole construction it used. -/

/-- info: 'Test.Lands.not_lands_of_dvd' depends on axioms: [propext] -/
#guard_msgs in #print axioms not_lands_of_dvd

/-- info: 'Test.Lands.lands_6_10_4' depends on axioms: [propext] -/
#guard_msgs in #print axioms lands_6_10_4

end Test.Lands
