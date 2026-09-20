import ConstitutiveSearch.NPAndOrP.GenericConstitutiveTraversal
import ConstitutiveSearch.ConstitutedPrimitivePath

/-!
An executable sequence of local paths. Different entries retain different
root formulas and sibling endpoints. Compilation does not claim that those
endpoints compose. Assignment succession is proved separately below.
-/

namespace ConstitutiveSearch.NPAndOrP

open SAT

structure LocalPrimitiveAtom where
  rootFormula : Cnf
  entry : ConstitutedLocalWitness rootFormula

def LocalPrimitiveAtom.path (atom : LocalPrimitiveAtom) :
    ConstitutedPrimitivePath (GeneratedStructuralFlipAtRelation atom.entry.var)
      atom.entry.source atom.entry.target :=
  .atom atom.entry.relation

structure CompiledLocalAtom where
  atom : LocalPrimitiveAtom
  code : TransportCode (GeneratedStructuralFlipAtRelation atom.entry.var)
    atom.entry.source atom.entry.target
  codeExact : code = atom.path.toTransportCode

def LocalPrimitiveAtom.compile (atom : LocalPrimitiveAtom) : CompiledLocalAtom :=
  ⟨atom, atom.path.toTransportCode, rfl⟩

theorem CompiledLocalAtom.canonical (compiled : CompiledLocalAtom) :
    compiled.atom.compile = compiled := by
  cases compiled with
  | mk atom code codeExact =>
    cases codeExact
    rfl

def SequentialHistory.localPath :
    {depth count : Nat} → {input : SequentialAssignment depth} →
    SequentialHistory depth input count → List LocalPrimitiveAtom
  | _, _, _, .nil _ _ => []
  | _, _, _, .step head tail =>
    ⟨_, head.schedule.entry⟩ :: tail.localPath

def SequentialHistory.returnedCodes :
    {depth count : Nat} → {input : SequentialAssignment depth} →
    SequentialHistory depth input count → List CompiledLocalAtom
  | _, _, _, .nil _ _ => []
  | _, _, _, .step head tail =>
    ⟨⟨_, head.schedule.entry⟩, head.execution.code,
      executedDiscoverySchedule_code head.execution⟩ :: tail.returnedCodes

theorem localPath_compiles_to_returnedCodes
    {depth count : Nat} {input : SequentialAssignment depth}
    (history : SequentialHistory depth input count) :
    history.localPath.map LocalPrimitiveAtom.compile = history.returnedCodes := by
  induction history with
  | nil => rfl
  | step head tail ih =>
    change LocalPrimitiveAtom.compile _ :: tail.localPath.map _ = _ :: tail.returnedCodes
    rw [ih]
    let returned : CompiledLocalAtom :=
      ⟨⟨_, head.schedule.entry⟩, head.execution.code,
        executedDiscoverySchedule_code head.execution⟩
    exact congrArg (fun head => head :: tail.returnedCodes)
      (CompiledLocalAtom.canonical returned)

theorem localPath_length
    {depth count : Nat} {input : SequentialAssignment depth}
    (history : SequentialHistory depth input count) : history.localPath.length = count := by
  induction history with
  | nil => rfl
  | step head tail ih => exact congrArg (fun n => n + 1) ih

def compiledLocalSize : List CompiledLocalAtom → Nat
  | [] => 0
  | head :: tail => head.code.size + compiledLocalSize tail

theorem returnedCodes_size
    {depth count : Nat} {input : SequentialAssignment depth}
    (history : SequentialHistory depth input count) :
    compiledLocalSize history.returnedCodes = count := by
  induction history with
  | nil => rfl
  | step head tail ih =>
    change head.execution.code.size + compiledLocalSize tail.returnedCodes = _
    rw [executedDiscoverySchedule_code, ConstitutedLocalWitness.code_size, ih]
    exact Nat.add_comm 1 _

/-- Evaluate a heterogeneous schedule of certified one-atom local codes. -/
def foldOperationalSteps : List CompiledLocalAtom → Assignment → Assignment
  | [], input => input
  | head :: tail, input =>
    foldOperationalSteps tail (Assignment.flipAt head.atom.entry.var input)

theorem terminalAssignment_is_operational_fold
    {depth count : Nat} {input : SequentialAssignment depth}
    (history : SequentialHistory depth input count) :
    history.final.assignment = foldOperationalSteps history.returnedCodes input.assignment := by
  induction history with
  | nil => rfl
  | @step depth count input head tail ih =>
    change tail.final.assignment =
      foldOperationalSteps tail.returnedCodes
        (Assignment.flipAt head.schedule.entry.var input.assignment)
    rw [← sequentialStage_next_from_input head]
    exact ih

end ConstitutiveSearch.NPAndOrP

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NPAndOrP.LocalPrimitiveAtom.path
#print axioms ConstitutiveSearch.NPAndOrP.SequentialHistory.localPath
#print axioms ConstitutiveSearch.NPAndOrP.SequentialHistory.returnedCodes
#print axioms ConstitutiveSearch.NPAndOrP.localPath_compiles_to_returnedCodes
#print axioms ConstitutiveSearch.NPAndOrP.localPath_length
#print axioms ConstitutiveSearch.NPAndOrP.returnedCodes_size
#print axioms ConstitutiveSearch.NPAndOrP.sequentialStage_next_from_input
#print axioms ConstitutiveSearch.NPAndOrP.terminalAssignment_is_operational_fold
/- AXIOM_AUDIT_END -/
