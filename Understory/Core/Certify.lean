import Lean
import Understory.Core.Construction

/-!
# Layer 5 — The seam: `certify`

The tactic is a conduit. It decides nothing itself, and it knows no particular
construction:

1. it finds the value terms `tᵢ` in the goal: those with a registered
   `Proposer` (possibly after unfolding definitions);
2. compiled code proposes a value `nᵢ` (untrusted); the construction for
   `tᵢ = nᵢ` is found by instance search, its search proposes evidence
   (untrusted), and the **kernel** checks it, once;
3. for the rewritten goal, the construction found by instance search (the
   `Decidable` fallback included) proposes evidence, and the kernel checks it;
4. `Verdict.ofValue` assembles the verdict on the original goal; the kernel
   checks it, and reads off its branch (`Verdict.of_branch_proved`,
   `Verdict.not_of_branch_refuted`);
5. only the statement the checked verdict proves is shown, and the kernel
   checks that it is that statement.

What remains trusted: turning compiled results into terms, and printing.
-/

open Lean Meta Elab Tactic

namespace Understory.Certify

deriving instance ToExpr for Found

/-- `t` and its unfoldings, at most `fuel` of them. -/
partial def unfoldings (t : Expr) (fuel : Nat := 8) : MetaM (List Expr) := do
  if fuel = 0 then return [t]
  match ← unfoldDefinition? t with
  | some t' => return t :: (← unfoldings t'.headBeta (fuel - 1))
  | none    => return [t]

/-- The registered proposer for `t`, if any. -/
def proposer? (t : Expr) : MetaM (Option Expr) := do
  try synthInstance? (← mkAppOptM ``Proposer #[none, t]) catch _ => return none

/-- A value term in `e`: a subterm `t`, an unfolding `t'` of it, and the
proposer for `t'`. -/
partial def findValue (e : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  if !e.hasLooseBVars && e.getAppFn.isConst then
    for t' in ← unfoldings e do
      if let some p ← proposer? t' then return some (e, t', p)
  match e with
  | .app f a   => do
    if let some r ← findValue f then return some r
    findValue a
  | .mdata _ b => findValue b
  | _          => return none

unsafe def evalToExprImpl (α e : Expr) : MetaM Expr := do
  let inst ← synthInstance (mkApp (mkConst ``ToExpr [Level.zero]) α)
  evalExpr Expr (mkConst ``Expr) (mkApp3 (mkConst ``ToExpr.toExpr [Level.zero]) α inst e)
/-- Evaluate `e : α` in compiled code and return the result as a term.
Untrusted: whatever comes out is checked by the kernel before it is used. -/
@[implemented_by evalToExprImpl] opaque evalToExpr (α e : Expr) : MetaM Expr

/-- Unfold instances and projections, for display and for finding `ToExpr`. -/
def reduceInst (e : Expr) : MetaM Expr :=
  withReducibleAndInstances do whnf (← instantiateMVars e)

/-- What the search of construction `c` for `P` proposes. -/
inductive Proposal where
  | evidence (e : Expr)
  | counter (r : Expr)
  | nothing

/-- Run the search of the construction `c` for `P` in compiled code. -/
def search (P c : Expr) : MetaM Proposal := do
  try
    let E ← reduceInst (mkApp2 (mkConst ``Construction.Evidence) P c)
    let R ← reduceInst (mkApp2 (mkConst ``Construction.Counterevidence) P c)
    let f ← evalToExpr (mkApp2 (mkConst ``Found) E R)
      (mkApp2 (mkConst ``Construction.search) P c)
    if f.isAppOfArity ``Found.evidence 3 then return .evidence f.appArg!
    if f.isAppOfArity ``Found.counter 3 then return .counter f.appArg!
    return .nothing
  catch _ => return .nothing

/-- Have the kernel check `v : T`, and return the name of the result. -/
def kernelCheck (T v : Expr) (isProp : Bool) : MetaM Name := do
  let name ← mkAuxDeclName (kind := `_certify)
  let decl := if isProp then
      Declaration.thmDecl { name, levelParams := [], type := T, value := v }
    else
      Declaration.defnDecl { name, levelParams := [], type := T, value := v,
                             hints := .abbrev, safety := .safe }
  -- synchronous: a message may only appear after the check
  withOptions (fun o => o.setBool `Elab.async false) (addDecl decl)
  return name

partial def conjuncts (e : Expr) : List Expr :=
  if e.isAppOfArity ``And 2 then conjuncts e.appFn!.appArg! ++ conjuncts e.appArg! else [e]

/-- The conjuncts of `C` worth showing: all but `True`. -/
def shown (C : Expr) : MetaM (List Expr) := do
  let C ← Core.betaReduce (← instantiateMVars C)
  return (conjuncts C).filter (!·.isConstOf ``True)

def lines (C : Expr) : MetaM MessageData := do
  let ls ← (← shown C).mapM fun c => do return m!"\n  {← ppExpr c}"
  return MessageData.joinSep ls ""

def rflTrue : Expr := mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true)

/-- A verdict on the current goal, checked by the kernel, with what it states. -/
structure Decided where
  /-- the checked verdict -/
  verdict : Expr
  /-- its branch: `Verdict.Branch.proved`, `.refuted` or `.unknown` -/
  branch  : Name
  /-- what it states, for display: the counter-evidence's statement, or what is known -/
  says    : Expr := mkConst ``True
  /-- why it is undecided -/
  reason  : MessageData := m!""
  /-- the construction's hint, if undecided -/
  hint    : Option Expr := none

def hint? (P c : Expr) : MetaM (Option Expr) := do
  let h ← reduceInst (mkApp2 (mkConst ``Construction.hint) P c)
  return if h.isAppOfArity ``Option.some 2 then some h.appArg! else none

/-- The verdict `Construction.ofKnown` of `c` for `P`, as undecided. -/
def known (P c : Expr) (reason : MessageData) : MetaM Decided := do
  let v := mkApp2 (mkConst ``Construction.ofKnown) P c
  let name ← kernelCheck (mkApp (mkConst ``Verdict) P) v false
  return { verdict := mkConst name, branch := ``Verdict.Branch.unknown, reason,
           says := ← reduceInst (mkApp2 (mkConst ``Construction.Known) P c),
           hint := ← hint? P c }

/-- Decide the goal `G` through its construction. -/
def decideRest (G : Expr) : MetaM Decided := do
  let some c ← synthInstance? (mkApp (mkConst ``Construction) G)
    | throwError "certify: no construction for {← ppExpr G}, and it is not decidable"
  let verdictT := mkApp (mkConst ``Verdict) G
  let unchecked := m!"the kernel could not check the evidence found for {← ppExpr G}"
  match ← search G c with
  | .evidence e =>
    let v := mkApp4 (mkConst ``Construction.ofEvidence) G c e rflTrue
    try return { verdict := mkConst (← kernelCheck verdictT v false), branch := ``Verdict.Branch.proved }
    catch _ => known G c unchecked
  | .counter r =>
    let v := mkApp4 (mkConst ``Construction.ofCounter) G c r rflTrue
    try
      let name ← kernelCheck verdictT v false
      return { verdict := mkConst name, branch := ``Verdict.Branch.refuted,
               says := ← reduceInst (mkApp3 (mkConst ``Construction.Says) G c r) }
    catch _ => known G c unchecked
  | .nothing => known G c m!"no evidence found for {← ppExpr G}"

/-- One checked value: `h : t = n`, and `G` with `t` abstracted. -/
structure Step where
  α : Expr
  u : Level
  G : Expr
  t : Expr
  n : Expr
  h : Expr

/-- Check a value `t` (unfolding to `t'`, with proposer `p`) in the goal `G`:
either a checked step and the rewritten goal, or an undecided verdict on `G`. -/
def checkValue (G t t' p : Expr) : MetaM (Except Decided (Step × Expr)) := do
  let α ← inferType t'
  let .sort u ← whnf (← inferType α) | throwError "certify: {← ppExpr t} is not a value"
  let n ← evalToExpr α (mkApp3 (mkConst ``Proposer.value) α t' p)
  let P ← mkEq t' n
  let some c ← synthInstance? (mkApp (mkConst ``Construction) P)
    | throwError "certify: no construction checks {← ppExpr t} = {← ppExpr n}"
  let undecided : MetaM Decided := do
    let W ← reduceInst (mkApp2 (mkConst ``Construction.Known) P c)
    let W := (← kabstract W t').instantiate1 t
    let v := mkApp3 (mkConst ``Verdict.unknown) G W (mkApp2 (mkConst ``Construction.known) P c)
    let name ← kernelCheck (mkApp (mkConst ``Verdict) G) v false
    return { verdict := mkConst name, branch := ``Verdict.Branch.unknown, says := W,
             reason := m!"the kernel cannot evaluate {← ppExpr t}", hint := ← hint? P c }
  match ← search P c with
  | .evidence e =>
    let pf := mkApp4 (mkConst ``Construction.sound) P c e rflTrue
    let some h ← (try some <$> kernelCheck (← mkEq t n) pf true catch _ => pure none)
      | return .error (← undecided)
    let body ← kabstract G t
    return .ok ({ α, u, G := .lam `x α body .default, t, n, h := mkConst h },
                body.instantiate1 n)
  | .counter r =>
    let v := mkApp4 (mkConst ``Construction.ofCounter) P c r rflTrue
    let _ ← kernelCheck (mkApp (mkConst ``Verdict) P) v false
    throwError m!"certify: the proposed value {← ppExpr n} of {← ppExpr t} is refuted \
      (checked by the kernel):\
      {← lines (← reduceInst (mkApp3 (mkConst ``Construction.Says) P c r))}"
  | .nothing => return .error (← undecided)

elab "certify" : tactic => withMainContext do
  let goal ← getMainGoal
  let G₀ ← instantiateMVars (← goal.getType)
  -- 1. values
  let mut G := G₀
  let mut steps : Array Step := #[]
  let mut stuck : Option Decided := none
  repeat
    let some (t, t', p) ← findValue G | break
    match ← checkValue G t t' p with
    | .ok (st, G') => steps := steps.push st; G := G'
    | .error d     => stuck := some d; break
  -- 2. the rest
  let d ← match stuck with
    | some d => pure d
    | none   => decideRest G
  -- 3. assemble, and have the kernel check the verdict on the original goal
  let verdict := steps.foldr (init := d.verdict) fun st v =>
    mkApp6 (mkConst ``Verdict.ofValue [st.u]) st.α st.G st.t st.n st.h v
  let v := mkConst (← kernelCheck (mkApp (mkConst ``Verdict) G₀) verdict false)
  -- what it states, for display: the checked values, then the rest
  let C ← steps.foldrM (init := d.says) fun st C => return mkAnd (← mkEq st.t st.n) C
  -- 4. the kernel reads the branch
  let hb := mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Verdict.Branch) (mkConst d.branch)
  if d.branch == ``Verdict.Branch.proved then
    let name ← kernelCheck G₀ (mkApp3 (mkConst ``Verdict.of_branch_proved) G₀ v hb) true
    goal.assign (mkConst name)
    replaceMainGoal []
    return
  -- 5. show only what the kernel checked
  let _ ← kernelCheck C (mkApp2 (mkConst ``Verdict.says_true) G₀ v) true
  if d.branch == ``Verdict.Branch.refuted then
    let _ ← kernelCheck (mkNot G₀) (mkApp3 (mkConst ``Verdict.not_of_branch_refuted) G₀ v hb) true
    throwError m!"Refuted (checked by the kernel):{← lines C}"
  let proven ← if (← shown C).isEmpty then pure m!""
    else pure m!"\nAll that is proven:{← lines C}"
  let hint ← match d.hint with
    | some h => pure m!"\nNo implementation found that computes in the kernel \
        (for example an instance {← ppExpr h})."
    | none   => pure m!""
  throwError m!"Undecided: {d.reason}.{proven}{hint}"

end Understory.Certify
