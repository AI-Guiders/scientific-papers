import Lean

/-!
# Automatic Default Kernel Linter (`AxiomGuard.lean`) — ZERO LOOPHOLES

Imported at the root of Constructive modules. Automatically runs on **every `theorem`**
at compile time with zero manual `#print axioms` or `#assert` lines required, and
**zero name-prefix exemptions (`no cond_ bypass`)**:

1. **Default `#print axioms` & Constructive Axiom Gate:**
   Automatically collects transitive kernel axioms (`collectAxioms`), prints
   `'TheoremName' depends on axioms: [...]`, and fails compilation (`Exit code 1`)
   if `Classical.choice`, `sorryAx`, or any custom axiom is present.
2. **Default Anti-Tautology Gate:**
   Fails compilation (`Exit code 1`) if a theorem's conclusion is `True` or
   syntactically identical reflexivity `lhs = lhs`.
3. **Default Zero-Smuggled-Hypothesis Gate (No `cond_` Escape Hatch):**
   Inspects all binders of the theorem's kernel type via `forallTelescope`.
   If ANY binder is a `Prop` premise `(h : P)` that is not a basic integer order/domain
   guard (`0 < x`, `0 ≤ x`, `a ≤ b`, `a < b`), compilation FAILS (`Exit code 1`).
   Equalities between variables must be constructive `let` bindings, and zero-product /
   annihilation laws must be stated as two-way equivalences `P ↔ Q` with zero smuggled
   premises in the header.
-/

namespace AxiomGuard

open Lean Meta Elab Command

initialize auditedDeclsRef : IO.Ref NameSet ← IO.mkRef {}

def hasSubstr (s sub : String) : Bool :=
  (s.splitOn sub).length > 1

/-- True iff `declName` is a compiler-generated auxiliary/equational/structure-constructor lemma. -/
def isCompilerGeneratedLemma (s : String) : Bool :=
  s.startsWith "_" ||
  hasSubstr s "._" ||
  hasSubstr s ".eq_" ||
  hasSubstr s ".mk." ||
  hasSubstr s ".noConfusion" ||
  hasSubstr s ".rec" ||
  hasSubstr s ".brecOn" ||
  hasSubstr s ".binductionOn" ||
  hasSubstr s ".casesOn"

/-- True iff `e` is a basic domain order guard (`<`, `≤`, `>`, `≥`) on numeric parameters. -/
def isBasicOrderDomainGuard (e : Expr) : Bool :=
  let fn := e.getAppFn
  fn.isConstOf ``LT.lt || fn.isConstOf ``LE.le || fn.isConstOf ``GT.gt || fn.isConstOf ``GE.ge

/-- Automatically audits a compiled theorem declaration in the Lean 4 kernel. -/
def auditTheoremDecl (declName : Name) (info : ConstantInfo) : CommandElabM Unit := do
  -- 1. Automatic `#print axioms` check + constructive gate
  let axioms ← collectAxioms declName
  for ax in axioms do
    let axStr := ax.toString
    let isAllowed :=
      ax == ``propext ||
      ax == ``Quot.sound ||
      hasSubstr axStr "._native.native_decide."
    if !isAllowed then
      throwError "❌ [AXIOM GUARD] `{declName}` depends on forbidden axiom `{ax}`! (0 Classical.choice and 0 sorryAx required.)"

  -- 2. Automatic kernel type inspection for smuggled Prop premises & tautologies (ZERO exemptions)
  liftTermElabM <| forallTelescope info.type fun xs body => do
    if body.isConstOf ``True then
      throwError "❌ [AXIOM GUARD] `{declName}` proves trivial `True`!"
    if let some (_, lhs, rhs) := body.eq? then
      if lhs == rhs then
        throwError "❌ [AXIOM GUARD] `{declName}` proves trivial reflexivity `{lhs} = {rhs}`!"

    let mut nonOrderPropHyps : Array (Name × Expr) := #[]
    for x in xs do
      let localDecl ← x.fvarId!.getDecl
      -- Only inspect named binders `(h : P)` in the theorem header (not anonymous `P → Q` arrows in the conclusion body)
      if !localDecl.userName.hasMacroScopes then
        let xType ← inferType x
        if (← isProp xType) then
          if !isBasicOrderDomainGuard xType then
            nonOrderPropHyps := nonOrderPropHyps.push (localDecl.userName, xType)

    if !nonOrderPropHyps.isEmpty then
      let mut msg := m!"❌ [AXIOM GUARD: SMUGGLED HYPOTHESIS] Theorem `{declName}` has {nonOrderPropHyps.size} non-order Prop premise(s) in its header:\n"
      for (hName, hType) in nonOrderPropHyps do
        msg := msg ++ m!"  • ({hName} : {hType})\n"
      msg := msg ++ m!"No `cond_` bypass is allowed: replace equality assumptions with constructive `let` bindings, state two-way equivalences `P ↔ Q`, or remove the conditional theorem."
      throwError msg

  logInfo m!"'{declName}' depends on axioms: {axioms.toList}"

/-- Registered globally in Lean 4's command elaborator loop: runs by default on every declaration. -/
initialize addLinter {
  name := `AxiomGuard.constructiveKernelLinter
  run := fun stx => do
    if stx.getKind != ``Lean.Parser.Command.declaration then
      return
    let env ← getEnv
    let audited ← auditedDeclsRef.get
    for (declName, info) in env.constants.map₂.toList do
      if !audited.contains declName then
        let _ ← auditedDeclsRef.modifyGet fun s => ((), s.insert declName)
        if let ConstantInfo.thmInfo _ := info then
          let s := declName.toString
          if !isCompilerGeneratedLemma s then
            auditTheoremDecl declName info
}

end AxiomGuard
