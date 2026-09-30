import Understory.Core.Least

/-!
# Layer 2b — Upward-closed predicates: a faster implementation under the same interface

Bounded search costs the kernel one step per candidate. For an upward-closed
predicate, bisection needs only logarithmically many steps. This is another
implementation of the same `Search p`; since that is a subsingleton, nothing
changes downstream, and that is a theorem (`least_congr`).

No division or subtraction: only addition and powers of two, so that all proofs
stay axiom-free.
-/

namespace Understory

/-- `p` is upward closed. -/
class UpwardClosed (p : Nat → Prop) : Prop where
  mono : ∀ {a b : Nat}, a ≤ b → p a → p b

section
variable (p : Nat → Prop) [DecidablePred p]

/-- Bisection, bit by bit. Invariant: `p` holds nowhere below `a`, and `p (a + 2^j)`. -/
def bisect : (j a : Nat) → Nat
  | 0, a     => if p a then a else a + 1
  | j + 1, a => if p (a + 2 ^ j) then bisect j a else bisect j (a + 2 ^ j + 1)

theorem bisect_spec [UpwardClosed p] : ∀ (j a : Nat), (∀ m, m < a → ¬p m) →
    p (a + 2 ^ j) → IsLeastWitness p (bisect p j a)
  | 0, a, hb, hp =>
    if h : p a then by
      rw [bisect, ite_eq_left h]; exact ⟨h, hb⟩
    else by
      rw [bisect, ite_eq_right h]
      exact ⟨hp, fun m hm =>
        match Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hm) with
        | .inl h' => hb m h'
        | .inr h' => h' ▸ h⟩
  | j + 1, a, hb, hp =>
    if h : p (a + 2 ^ j) then by
      rw [bisect, ite_eq_left h]; exact bisect_spec j a hb h
    else by
      rw [bisect, ite_eq_right h]
      refine bisect_spec j (a + 2 ^ j + 1) (fun m hm pm => h (UpwardClosed.mono (Nat.le_of_lt_succ hm) pm)) ?_
      refine UpwardClosed.mono ?_ hp
      rw [Nat.pow_succ, Nat.mul_two, ← Nat.add_assoc]
      exact Nat.add_le_add_right (Nat.le_succ _) _

/-- The least `k ≥ k₀` with `B ≤ 2^k`, within `fuel` steps. -/
def expAbove (B : Nat) : (fuel k : Nat) → Nat
  | 0, k        => k
  | fuel + 1, k => if B ≤ 2 ^ k then k else expAbove B fuel (k + 1)

/-- The bisection implementation. Should the exponent not be found, it falls
back to bounded search; this avoids having to prove that the fuel suffices. -/
@[instance_reducible] def Search.ofUpwardClosed [UpwardClosed p] [b : Bounded p] : Search p :=
  let k := expAbove b.bound (b.bound + 1) 0
  if h : b.bound ≤ 2 ^ k then
    ⟨bisect p k 0, bisect_spec p k 0 (fun m hm => absurd hm (Nat.not_lt_zero m)) (by
      obtain ⟨n, hn, hpn⟩ := b.exists_le
      exact UpwardClosed.mono (Nat.le_trans hn (Nat.le_trans h (Nat.le_of_eq (Nat.zero_add _).symm))) hpn)⟩
  else Search.ofBounded p

instance (priority := high) instSearchOfUpwardClosed [UpwardClosed p] [Bounded p] : Search p :=
  Search.ofUpwardClosed p

end
end Understory
