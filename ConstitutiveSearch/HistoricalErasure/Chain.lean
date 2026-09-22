import ConstitutiveSearch.HistoricalErasure.Local

/-!
# Executed historical erasure for a chain of coupled blocks

For cells (d_i,y_i,z_i), the acceptance condition is exactly
  G(z) and (d_i -> y_i=z_i) and (d_i -> d_(i-1) or y_(i-1)!=z_(i-1)).
The first incoming guard is true. G is kept separate and never evaluated by
discovery or execution. This is a structural-input implementation of the family,
not a claimed verification of the earlier Python CNF parser/synthesizer.

Each stage stores its actual discovery, separate recheck, and produced cell.
The tail is indexed by the guard read from that cell, not by a recomputed
canonical replacement. The complete map is total, before acceptance is known.
-/

namespace ConstitutiveSearch.HistoricalErasure

structure Cell where
  decision : Bool
  payload : Bool
  core : Bool
  deriving DecidableEq, Repr

def Cell.outgoing (c : Cell) : Bool := outgoingGuard c.decision c.payload c.core

def CellOK (guard : Bool) (c : Cell) : Prop :=
  c.decision = true → c.payload = c.core ∧ guard = true

def ChainOK : Bool → List Cell → Prop
  | _, [] => True
  | guard, c :: rest => CellOK guard c ∧ ChainOK c.outgoing rest

def coreValues (cells : List Cell) : List Bool := cells.map Cell.core

def decisionValues (cells : List Cell) : List Bool := cells.map Cell.decision

def Accepted (G : List Bool → Prop) (guard : Bool) (cells : List Cell) : Prop :=
  G (coreValues cells) ∧ ChainOK guard cells

/-- A true incoming guard weakens the first guard constraint, not the core. -/
theorem chainOK_guard_true (guard : Bool) (cells : List Cell)
    (accepted : ChainOK guard cells) : ChainOK true cells := by
  cases cells with
  | nil => exact True.intro
  | cons c rest => exact ⟨fun selected => ⟨(accepted.1 selected).1, rfl⟩, accepted.2⟩

/-- Full opening-and-retention action: the already-true branch is included. -/
def applyCell (table : PayloadTable) (c : Cell) : Cell :=
  match c.decision with
  | false => ⟨true, table.eval c.payload c.core, c.core⟩
  | true => c

theorem applyCell_decision (table : PayloadTable) (c : Cell) :
    (applyCell table c).decision = true := by
  cases c with
  | mk d p z => cases d <;> rfl

theorem applyCell_core (table : PayloadTable) (c : Cell) :
    (applyCell table c).core = c.core := by
  cases c with
  | mk d p z => cases d <;> rfl

theorem applyCell_outgoing (table : PayloadTable) (c : Cell) :
    (applyCell table c).outgoing = true := by
  unfold Cell.outgoing outgoingGuard
  rw [applyCell_decision]
  rfl

theorem resetTable_eval (payload core : Bool) : resetTable.eval payload core = core := by
  cases payload <;> cases core <;> rfl

theorem applyCell_sound (guard : Bool) (table : PayloadTable)
    (checked : (checkTable guard table).valid = true)
    (c : Cell) (accepted : CellOK guard c) : CellOK guard (applyCell table c) := by
  have exactTable := checkTable_unique guard table checked
  rw [exactTable.2]
  cases c with
  | mk d p z =>
    cases d with
    | false => exact fun _ => ⟨resetTable_eval p z, exactTable.1⟩
    | true => exact accepted

/-- Produced data and their provenance are stored before any later projection. -/
structure Stage (guard : Bool) (input : Cell) where
  discovery : Discovery guard
  discoveryExact : discovery = discover guard
  certificate : Certificate guard
  found : discovery.result = some certificate
  validation : RowCheck
  validationExact : validation = checkTable guard certificate.val
  produced : Cell
  producedExact : produced = applyCell certificate.val input

@[noinline] def buildStage (guard : Bool) (enabled : guard = true) (input : Cell) : Stage guard input :=
  let searched := discover guard
  match found : searched.result with
  | none => False.elim (by cases enabled; exact discover_true_found found)
  | some certificate =>
      let validation := checkTable guard certificate.val
      let produced := applyCell certificate.val input
      ⟨searched, rfl, certificate, found, validation, rfl, produced, rfl⟩

namespace Stage

def nextGuard {guard : Bool} {input : Cell} (stage : Stage guard input) : Bool :=
  stage.produced.outgoing

/-- The transmitted determination is read from the executed output. -/
def determination {guard : Bool} {input : Cell} (stage : Stage guard input) : Bool :=
  stage.produced.decision

theorem nextGuard_true {guard : Bool} {input : Cell} (stage : Stage guard input) :
    stage.nextGuard = true := by
  unfold nextGuard
  rw [stage.producedExact]
  exact applyCell_outgoing _ _

theorem determination_true {guard : Bool} {input : Cell} (stage : Stage guard input) :
    stage.determination = true := by
  unfold determination
  rw [stage.producedExact]
  exact applyCell_decision _ _

theorem core_preserved {guard : Bool} {input : Cell} (stage : Stage guard input) :
    stage.produced.core = input.core := by
  rw [stage.producedExact]
  exact applyCell_core _ _

theorem accepts {guard : Bool} {input : Cell} (stage : Stage guard input)
    (accepted : CellOK guard input) : CellOK guard stage.produced := by
  rw [stage.producedExact]
  exact applyCell_sound guard _ stage.certificate.property input accepted

/-- Declared source-level ledger: discovery rows, validation rows, and four
    fixed per-stage bookkeeping/application units. Not a machine-time model. -/
def work {guard : Bool} {input : Cell} (stage : Stage guard input) : Nat :=
  stage.discovery.rowVisits + stage.validation.visits + 4

theorem work_exact {guard : Bool} {input : Cell} (stage : Stage guard input) :
    stage.work = 60 := by
  have enabled := (checkTable_unique guard _ stage.certificate.property).1
  unfold work
  rw [stage.discoveryExact, stage.validationExact, checkTable_visits, enabled,
    discover_true_rows]

theorem attempts_exact {guard : Bool} {input : Cell} (stage : Stage guard input) :
    stage.discovery.attempts = 6 := by
  have enabled := (checkTable_unique guard _ stage.certificate.property).1
  rw [stage.discoveryExact, enabled, discover_true_attempts]

end Stage

/-- The tail is indexed by this head's produced guard. -/
inductive Execution : Bool → List Cell → Type where
  | nil (guard : Bool) : Execution guard []
  | step {guard : Bool} {input : Cell} {rest : List Cell}
      (stage : Stage guard input)
      (tail : Execution stage.nextGuard rest) : Execution guard (input :: rest)

/-- One authoritative recursion. No accepted continuation is required. -/
@[noinline] def executeFrom : (cells : List Cell) → (guard : Bool) → guard = true → Execution guard cells
  | [], guard, _ => .nil guard
  | input :: rest, guard, enabled =>
      let stage := buildStage guard enabled input
      .step stage (executeFrom rest stage.nextGuard stage.nextGuard_true)

@[noinline] def execute (cells : List Cell) : Execution true cells := executeFrom cells true rfl

namespace Execution

@[noinline] def output : {guard : Bool} → {cells : List Cell} → Execution guard cells → List Cell
  | _, _, .nil _ => []
  | _, _, .step stage tail => stage.produced :: tail.output

@[noinline] def history : {guard : Bool} → {cells : List Cell} → Execution guard cells → List Bool
  | _, _, .nil _ => []
  | _, _, .step stage tail => stage.determination :: tail.history

@[noinline] def program : {guard : Bool} → {cells : List Cell} → Execution guard cells → List PayloadTable
  | _, _, .nil _ => []
  | _, _, .step stage tail => stage.certificate.val :: tail.program

@[noinline] def work : {guard : Bool} → {cells : List Cell} → Execution guard cells → Nat
  | _, _, .nil _ => 0
  | _, _, .step stage tail => stage.work + tail.work

@[noinline] def attempts : {guard : Bool} → {cells : List Cell} → Execution guard cells → Nat
  | _, _, .nil _ => 0
  | _, _, .step stage tail => stage.discovery.attempts + tail.attempts

theorem output_length {guard : Bool} {cells : List Cell} (run : Execution guard cells) :
    run.output.length = cells.length := by
  induction run with
  | nil => rfl
  | step stage tail ih => exact congrArg Nat.succ ih

theorem output_cores {guard : Bool} {cells : List Cell} (run : Execution guard cells) :
    coreValues run.output = coreValues cells := by
  induction run with
  | nil => rfl
  | @step guard input rest stage tail ih =>
    change stage.produced.core :: coreValues tail.output = input.core :: coreValues rest
    rw [stage.core_preserved, ih]

theorem output_decisions {guard : Bool} {cells : List Cell} (run : Execution guard cells) :
    decisionValues run.output = List.replicate cells.length true := by
  induction run with
  | nil => rfl
  | @step guard input rest stage tail ih =>
    change stage.determination :: decisionValues tail.output = List.replicate (rest.length + 1) true
    rw [stage.determination_true, ih, List.replicate_succ]

theorem history_is_output {guard : Bool} {cells : List Cell} (run : Execution guard cells) :
    run.history = decisionValues run.output := by
  induction run with
  | nil => rfl
  | @step guard input rest stage tail ih =>
    change stage.determination :: tail.history =
      stage.determination :: decisionValues tail.output
    exact congrArg (List.cons stage.determination) ih

theorem program_length {guard : Bool} {cells : List Cell} (run : Execution guard cells) :
    run.program.length = cells.length := by
  induction run with
  | nil => rfl
  | step stage tail ih => exact congrArg Nat.succ ih

theorem work_exact {guard : Bool} {cells : List Cell} (run : Execution guard cells) :
    run.work = 60 * cells.length := by
  induction run with
  | nil => rfl
  | @step guard input rest stage tail ih =>
    change stage.work + tail.work = 60 * (rest.length + 1)
    rw [stage.work_exact, ih, Nat.mul_add, Nat.mul_one]
    omega

theorem attempts_exact {guard : Bool} {cells : List Cell} (run : Execution guard cells) :
    run.attempts = 6 * cells.length := by
  induction run with
  | nil => rfl
  | @step guard input rest stage tail ih =>
    change stage.discovery.attempts + tail.attempts = 6 * (rest.length + 1)
    rw [stage.attempts_exact, ih, Nat.mul_add, Nat.mul_one]
    omega

theorem preserves_chain {guard : Bool} {cells : List Cell} (run : Execution guard cells) :
    ChainOK guard cells → ChainOK guard run.output := by
  induction run with
  | nil => exact fun _ => True.intro
  | @step guard input rest stage tail ih =>
    intro accepted
    have restOK : ChainOK stage.nextGuard rest := by
      rw [stage.nextGuard_true]
      exact chainOK_guard_true input.outgoing rest accepted.2
    exact ⟨stage.accepts accepted.1, ih restOK⟩

theorem preserves_acceptance {guard : Bool} {cells : List Cell}
    (run : Execution guard cells) (G : List Bool → Prop) :
    Accepted G guard cells → Accepted G guard run.output := by
  intro accepted
  constructor
  · rw [run.output_cores]
    exact accepted.1
  · exact run.preserves_chain accepted.2

end Execution

/-- History is a structural prefix, not an acceptance certificate. -/
def Realizes (history : List Bool) (cells : List Cell) : Prop :=
  ∃ rest, decisionValues cells = history ++ rest

def chainSystem (n : Nat) (G : List Bool → Prop) : SearchSystem where
  State := List Bool
  Continuation := fun history => {cells : List Cell // cells.length = n ∧ Realizes history cells}
  Accept := fun _ c => Accepted G true c.val

def retainedHistory (n : Nat) : List Bool := List.replicate n true

/-- Total map to the one retained history, using the executed discovered program. -/
def normalizingTransport (n : Nat) (G : List Bool → Prop) (history : List Bool) :
    AcceptingContinuationTransport (chainSystem n G) history (retainedHistory n) where
  map := fun c =>
    let run := execute c.val
    have decisions : decisionValues run.output = retainedHistory n :=
      run.output_decisions.trans
        (congrArg (fun k => List.replicate k true) c.property.1)
    ⟨run.output, ⟨run.output_length.trans c.property.1,
      ⟨[], decisions.trans (List.append_nil (retainedHistory n)).symm⟩⟩⟩
  preservesAccept := by
    intro c accepted
    exact (execute c.val).preserves_acceptance G accepted

/-- Forgetting history does not change the assignment or its acceptance. -/
def toRoot (n : Nat) (G : List Bool → Prop) (history : List Bool) :
    AcceptingContinuationTransport (chainSystem n G) history [] where
  map := fun c => ⟨c.val, c.property.1, ⟨decisionValues c.val, rfl⟩⟩
  preservesAccept := fun _ accepted => accepted

theorem root_viable_iff_retained (n : Nat) (G : List Bool → Prop) :
    (chainSystem n G).Viable [] ↔ (chainSystem n G).Viable (retainedHistory n) :=
  ⟨(normalizingTransport n G []).preservesViable,
    (toRoot n G (retainedHistory n)).preservesViable⟩

/-- One explicit accepted realization of any branch, given the unchanged core. -/
def witnessCell (decision core : Bool) : Cell :=
  ⟨decision, if decision then core else !core, core⟩

theorem witnessCell_valid (decision core : Bool) : CellOK true (witnessCell decision core) := by
  cases decision <;> cases core <;> decide

theorem witnessCell_outgoing (decision core : Bool) : (witnessCell decision core).outgoing = true := by
  cases decision <;> cases core <;> decide

def branchWitness : List Bool → List Bool → List Cell
  | [], _ => []
  | _ :: _, [] => []
  | d :: ds, z :: zs => witnessCell d z :: branchWitness ds zs

theorem branchWitness_correct (bits cores : List Bool) (same : bits.length = cores.length) :
    (branchWitness bits cores).length = bits.length ∧
    decisionValues (branchWitness bits cores) = bits ∧
    coreValues (branchWitness bits cores) = cores ∧
    ChainOK true (branchWitness bits cores) := by
  induction bits generalizing cores with
  | nil =>
    cases cores with
    | nil => exact ⟨rfl, rfl, rfl, True.intro⟩
    | cons z zs => exact False.elim (Nat.noConfusion same)
  | cons d ds ih =>
    cases cores with
    | nil => exact False.elim (Nat.noConfusion same)
    | cons z zs =>
      have tail := ih zs (Nat.succ.inj same)
      refine ⟨congrArg Nat.succ tail.1, ?_, ?_, ?_⟩
      · change d :: decisionValues (branchWitness ds zs) = d :: ds
        exact congrArg (List.cons d) tail.2.1
      · change z :: coreValues (branchWitness ds zs) = z :: zs
        exact congrArg (List.cons z) tail.2.2.1
      · change CellOK true (witnessCell d z) ∧
          ChainOK (witnessCell d z).outgoing (branchWitness ds zs)
        rw [witnessCell_outgoing]
        exact ⟨witnessCell_valid d z, tail.2.2.2⟩

theorem every_branch_viable (n : Nat) (G : List Bool → Prop)
    (cores bits : List Bool) (coresLength : cores.length = n)
    (bitsLength : bits.length = n) (coreAccepted : G cores) :
    (chainSystem n G).Viable bits := by
  have correct := branchWitness_correct bits cores (bitsLength.trans coresLength.symm)
  refine ⟨⟨branchWitness bits cores, correct.1.trans bitsLength,
    ⟨[], correct.2.1.trans (List.append_nil bits).symm⟩⟩, ?_⟩
  change G (coreValues (branchWitness bits cores)) ∧ ChainOK true (branchWitness bits cores)
  rw [correct.2.2.1]
  exact ⟨coreAccepted, correct.2.2.2⟩

end ConstitutiveSearch.HistoricalErasure

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.HistoricalErasure.ChainOK
#print axioms ConstitutiveSearch.HistoricalErasure.applyCell_sound
#print axioms ConstitutiveSearch.HistoricalErasure.buildStage
#print axioms ConstitutiveSearch.HistoricalErasure.Stage.nextGuard_true
#print axioms ConstitutiveSearch.HistoricalErasure.executeFrom
#print axioms ConstitutiveSearch.HistoricalErasure.Execution.output_length
#print axioms ConstitutiveSearch.HistoricalErasure.Execution.output_cores
#print axioms ConstitutiveSearch.HistoricalErasure.Execution.output_decisions
#print axioms ConstitutiveSearch.HistoricalErasure.Execution.history_is_output
#print axioms ConstitutiveSearch.HistoricalErasure.Execution.work_exact
#print axioms ConstitutiveSearch.HistoricalErasure.Execution.attempts_exact
#print axioms ConstitutiveSearch.HistoricalErasure.Execution.preserves_acceptance
#print axioms ConstitutiveSearch.HistoricalErasure.normalizingTransport
#print axioms ConstitutiveSearch.HistoricalErasure.root_viable_iff_retained
#print axioms ConstitutiveSearch.HistoricalErasure.branchWitness_correct
#print axioms ConstitutiveSearch.HistoricalErasure.every_branch_viable
/- AXIOM_AUDIT_END -/
