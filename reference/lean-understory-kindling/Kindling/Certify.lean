import Lean
import Kindling.Least

/-!
# Layer 3 — The seam: `certify`

The tactic is a conduit. It decides nothing itself:

1. it finds all terms `tᵢ` in the goal that are `least pᵢ`;
2. it asks the instance system for the best implementation of `Search pᵢ`
   (a public interface; it never inspects the implementation behind `tᵢ`);
3. compiled code proposes a value `nᵢ` (untrusted);
4. the **kernel** checks `tᵢ = nᵢ`, via `least_congr`, exactly once;
5. the object-level verdict `Verdict.ofRewrite` decides the rewritten goal,
   and the kernel checks that too;
6. only what the checked verdict proves is shown.

What remains trusted: reading off the verdict's branch, and printing.
-/

open Lean Meta Elab Tactic

namespace Kindling.Certify

/-- Unfold `t` to `@least p s`, if possible. -/
partial def unfoldToLeast (t : Expr) (fuel : Nat := 8) : MetaM (Option (Expr × Expr)) := do
  if t.isAppOfArity ``least 2 then return some (t.appFn!.appArg!, t.appArg!)
  if fuel = 0 then return none
  match ← unfoldDefinition? t with
  | some t' => unfoldToLeast t'.headBeta (fuel - 1)
  | none    => return none

/-- A subterm `t` of `e` with `t ≡ @least p s`. -/
partial def findLeast (e : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  if !e.hasLooseBVars && e.getAppFn.isConst then
    if let some (p, s) ← unfoldToLeast e then return some (e, p, s)
  match e with
  | .app f a   => do
    if let some r ← findLeast f then return some r
    findLeast a
  | .mdata _ b => findLeast b
  | _          => return none

unsafe def evalNatImpl (e : Expr) : MetaM Nat := evalExpr Nat (mkConst ``Nat) e
/-- An untrusted candidate from compiled code; the kernel checks it. -/
@[implemented_by evalNatImpl] opaque evalNat (e : Expr) : MetaM Nat

/-- Have the kernel check `v : T`, and return the name of the result. -/
def kernelCheck (T v : Expr) (isProp : Bool) : MetaM Name := do
  let name ← mkFreshUserName `_certify
  let decl := if isProp then
      Declaration.thmDecl { name, levelParams := [], type := T, value := v }
    else
      Declaration.defnDecl { name, levelParams := [], type := T, value := v,
                             hints := .opaque, safety := .safe }
  -- synchronous: a message may only appear after the check
  withOptions (fun o => o.setBool `Elab.async false) (addDecl decl)
  return name

partial def conjuncts (e : Expr) : List Expr :=
  if e.isAppOfArity ``And 2 then conjuncts e.appFn!.appArg! ++ conjuncts e.appArg! else [e]

def lines (C : Expr) : MetaM MessageData := do
  let C ← Core.betaReduce (← instantiateMVars C)
  let ls ← (conjuncts C).mapM fun c => do return m!"\n  {← ppExpr c}"
  return MessageData.joinSep ls ""

/-- One rewriting step: `t = n`, checked by the kernel. -/
structure Step where
  eq   : Expr   -- the proposition `t = n`
  pf   : Expr   -- the checked constant
  step : Expr   -- `G = G'` for this step
deriving Inhabited

def one := Level.one
def nat := mkConst ``Nat

/-- Report honestly that the kernel cannot evaluate `t`, with what *is* proven. -/
def unknown {α : Type} (t p s : Expr) : MetaM α := do
  let W := mkApp2 (mkConst ``IsLeast) p t
  let _ ← kernelCheck W (mkApp2 (mkConst ``least_spec) p s) true
  throwError m!"Undecided: the kernel cannot evaluate {← ppExpr t}.\
    \nAll that is proven:{← lines W}\
    \nNo implementation found that computes in the kernel \
    (for example an instance Bounded ({← ppExpr p}))."

/-- Evaluate `t ≡ @least p s`, or report honestly that the kernel cannot. -/
def evalLeast (G t p s : Expr) : MetaM (Step × Expr) := do
  let some sBest ← synthInstance? (mkApp (mkConst ``Search) p) | unknown t p s
  let val := mkApp2 (mkConst ``Search.val) p sBest
  let n ← evalNat val
  let nE := mkNatLit n
  let eqV := mkApp3 (mkConst ``Eq [one]) nat val nE
  let hB  := mkApp3 (mkConst ``of_decide_eq_true) eqV
               (mkApp2 (mkConst ``instDecidableEqNat) val nE)
               (mkApp2 (mkConst ``Eq.refl [one]) (mkConst ``Bool) (mkConst ``Bool.true))
  let lb  := mkApp2 (mkConst ``least) p sBest
  let hv  := mkApp6 (mkConst ``Eq.trans [one]) nat t lb nE
               (mkApp3 (mkConst ``least_congr) p s sBest)
               (mkApp6 (mkConst ``Eq.trans [one]) nat lb val nE
                 (mkApp2 (mkConst ``least_eq_val) p sBest) hB)
  let eqT := mkApp3 (mkConst ``Eq [one]) nat t nE
  let name ← try kernelCheck eqT hv true catch _ => unknown t p s
  let body ← kabstract G t
  let Gfun := Expr.lam `x nat body .default
  let G' := body.instantiate1 nE
  let step := mkApp6 (mkConst ``congrArg [one, one]) nat (mkSort Level.zero) t nE Gfun (mkConst name)
  return ({ eq := eqT, pf := mkConst name, step }, G')

elab "certify" : tactic => withMainContext do
  let goal ← getMainGoal
  let G₀ ← instantiateMVars (← goal.getType)
  let mut G := G₀
  let mut steps : Array Step := #[]
  repeat
    let some (t, p, s) ← findLeast G | break
    let (st, G') ← evalLeast G t p s
    steps := steps.push st
    G := G'
  if steps.isEmpty then throwError "certify: the goal contains no least witness"
  let prop := mkSort Level.zero
  -- `G₀ = G`, as a chain of steps
  let mut hG := steps[0]!.step
  for st in steps[1:] do
    let ends := (← inferType st.step).getAppArgs
    hG := mkApp6 (mkConst ``Eq.trans [one]) prop G₀ ends[1]! ends[2]! hG st.step
  -- the rewrites as certificate `C`, with proof `c`
  let (C, c) := steps.pop.foldr (fun st (C, c) =>
      (mkAnd st.eq C, mkApp4 (mkConst ``And.intro) st.eq C st.pf c))
    (steps.back!.eq, steps.back!.pf)
  let some decG ← synthInstance? (mkApp (mkConst ``Decidable) G)
    | throwError "certify: {← ppExpr G} is not decidable"
  let verdict := mkApp6 (mkConst ``Verdict.ofRewrite) G₀ G hG decG C c
  let _ ← kernelCheck (mkApp (mkConst ``Verdict) G₀) verdict false
  let v ← withTransparency .all <| whnf verdict
  match v.getAppFn.constName?, v.getAppArgs with
  | some ``Verdict.proved, #[_, h] =>
    goal.assign h
    replaceMainGoal []
  | some ``Verdict.refuted, #[_, C', c', sound] =>
    let _ ← kernelCheck C' c' true
    let _ ← kernelCheck (mkNot G₀) (mkApp sound c') true
    throwError m!"Refuted (checked by the kernel):{← lines C'}"
  | _, _ => throwError "certify: could not read the verdict"

end Kindling.Certify
