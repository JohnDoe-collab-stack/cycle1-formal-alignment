import ConstitutiveSearch.ClassicalDecisionComplexity
import ConstitutiveSearch.SAT.TrajectoryConstitutedLocalSchedule
import ConstitutiveSearch.SAT.ParametricSymmetricFamily

/-!
# Post-audit nonconstant executable decision benchmark

F(n) remains a structural/schedule/accounting benchmark only.

This module introduces one deliberately small decision family with genuine YES
and NO instances.  It does not aim at general SAT.

For input zero the formula is one symmetric block.  For every nonzero input the
same block is followed by an empty clause.  Variable zero is split in both
cases.

The procedure does not receive the useful flip witness:
* it builds the generated children from the presented formula;
* it calls generatedStructuralFlipAtSearch at the announced split variable;
* on success it builds the one-atom constituted local code from the returned
  witness;
* it validates that code;
* it executes the actual candidate-free local run;
* it reads a terminal syntactic condition from the retained residual formula.

Discovery, schedule production, validation, execution and the terminal check
are recorded separately in the returned statistics.
-/

namespace ConstitutiveSearch
namespace SAT

/-- Background distinguishing the YES instance from all NO instances. -/
def auditedDecisionBackground
    (input : Nat) : Cnf :=
  if input = 0 then
    []
  else
    [[]]

/-- Presented decision formula. -/
def auditedDecisionFormula
    (input : Nat) : Cnf :=
  symmetricBlockFamily
    0
    1
    (auditedDecisionBackground input)

/-- Concrete encoded input size for the Nat-coded presented family. -/
def auditedDecisionInputSize
    (input : Nat) : Nat :=
  BinaryRepresentation.natBitSize input +
    1

/-- Root generated state of the presented formula. -/
def auditedDecisionRoot
    (input : Nat) :
    GeneratedStructuralBranchContext
      (auditedDecisionFormula input) :=
  GeneratedStructuralBranchContext.root
    (auditedDecisionFormula input)

/-- Variable zero is structurally fresh at every root. -/
theorem auditedDecisionRootFresh
    (input : Nat) :
    StructuralDecisionsAvoid
      0
      (auditedDecisionRoot
        input).context.decisions := by
  exact True.intro

/-- False generated child used by the executable discovery query. -/
def auditedDecisionFalseChild
    (input : Nat) :
    GeneratedStructuralBranchContext
      (auditedDecisionFormula input) :=
  GeneratedStructuralBranchContext.child
    (auditedDecisionRoot input)
    0
    false
    (auditedDecisionRootFresh input)

/-- Retained true child used as the terminal state. -/
def auditedDecisionTrueChild
    (input : Nat) :
    GeneratedStructuralBranchContext
      (auditedDecisionFormula input) :=
  GeneratedStructuralBranchContext.child
    (auditedDecisionRoot input)
    0
    true
    (auditedDecisionRootFresh input)

/-- The benchmark background never mentions the split variable zero. -/
theorem auditedDecisionBackground_avoids
    (input : Nat) :
    Cnf.AvoidsVar
      0
      (auditedDecisionBackground input) := by
  unfold auditedDecisionBackground
  by_cases inputZero : input = 0
  · rw [if_pos inputZero]
    exact True.intro
  · rw [if_neg inputZero]
    exact
      ⟨True.intro,
        True.intro⟩

/-- The two-clause block is structurally symmetric independently of YES/NO. -/
theorem auditedDecision_flipSymmetric
    (input : Nat) :
    FlipSymmetricAt
      (auditedDecisionFormula input)
      0 := by
  apply
    symmetricBlockFamily_flipSymmetric
      (var := 0)
      (anchor := 1)
      (background :=
        auditedDecisionBackground input)
  · decide
  · exact
      auditedDecisionBackground_avoids
        input

/-- Exact relation known mathematically, used only to prove discovery completeness. -/
def auditedDecisionExpectedRelation
    (input : Nat) :
    GeneratedStructuralFlipAtRelation
      0
      (auditedDecisionFalseChild input)
      (auditedDecisionTrueChild input) :=
  flipSymmetricSiblingRelation
    (auditedDecisionRoot input)
    0
    (auditedDecisionRootFresh input)
    (auditedDecision_flipSymmetric input)

/--
Executable structural discovery.

No SAT query is performed; this is the exact generated structural flip search.
-/
def auditedDecisionDiscover
    (input : Nat) :
    Option
      (GeneratedStructuralFlipAtRelation
        0
        (auditedDecisionFalseChild input)
        (auditedDecisionTrueChild input)) :=
  (generatedStructuralFlipAtSearch
    (auditedDecisionFormula input)
    0).find
      (auditedDecisionFalseChild input)
      (auditedDecisionTrueChild input)

/-- Discovery succeeds for every presented benchmark instance. -/
theorem auditedDecisionDiscover_found
    (input : Nat) :
    auditedDecisionDiscover input ≠
      none := by
  unfold auditedDecisionDiscover
  dsimp [generatedStructuralFlipAtSearch]
  rw [
    dif_pos
      (auditedDecisionExpectedRelation
        input).formulaExact,
    dif_pos
      (auditedDecisionExpectedRelation
        input).decisionsExact
  ]
  intro impossible
  cases impossible

/-- Package a discovered relation as one constituted local schedule entry. -/
def auditedDecisionEntry
    (input : Nat)
    (relation :
      GeneratedStructuralFlipAtRelation
        0
        (auditedDecisionFalseChild input)
        (auditedDecisionTrueChild input)) :
    ConstitutedLocalWitness
      (auditedDecisionFormula input) :=
  { var := 0
    source :=
      auditedDecisionFalseChild input
    target :=
      auditedDecisionTrueChild input
    relation :=
      relation }

/-- Syntactic terminal test: detect whether a CNF contains an empty clause. -/
def containsEmptyClause : Cnf → Bool
  | [] =>
      false
  | clause :: rest =>
      if clause = [] then
        true
      else
        containsEmptyClause rest

/--
Terminal decision reads the actually retained residual formula.

For this benchmark, satisfiability is equivalent to absence of the deliberately
inserted empty clause after the symmetric split.
-/
def auditedTerminalDecision
    (input : Nat) : Bool :=
  !(containsEmptyClause
      (auditedDecisionTrueChild
        input).context.formula)

/-- YES witness assignment. -/
def auditedYesAssignment : Assignment
  | _ =>
      true

/-- The zero input is genuinely satisfiable. -/
theorem auditedDecision_zero_satisfies :
    Satisfies
      auditedYesAssignment
      (auditedDecisionFormula 0) := by
  exact
    .cons
      rfl
      (.cons
        rfl
        .nil)

/-- Every nonzero input contains an unsatisfied empty clause. -/
theorem auditedDecision_nonzero_not_satisfiable
    {input : Nat}
    (inputNonzero : input ≠ 0) :
    ¬
      ∃ assignment : Assignment,
        Satisfies
          assignment
          (auditedDecisionFormula input) := by
  intro satisfiable
  rcases satisfiable with
    ⟨assignment, satisfaction⟩
  unfold auditedDecisionFormula at satisfaction
  unfold auditedDecisionBackground at satisfaction
  rw [if_neg inputNonzero] at satisfaction
  cases satisfaction with
  | cons firstSatisfied restSatisfied =>
      cases restSatisfied with
      | cons secondSatisfied finalSatisfied =>
          cases finalSatisfied with
          | cons emptySatisfied tailSatisfied =>
              change false = true at emptySatisfied
              cases emptySatisfied

/-- Extensional benchmark acceptance is genuine SAT viability of the presented formula. -/
def auditedDecisionProblem :
    DecisionProblem :=
  { inputSize :=
      auditedDecisionInputSize
    Accept := fun input =>
      ∃ assignment : Assignment,
        Satisfies
          assignment
          (auditedDecisionFormula input) }

/-- The benchmark decision is nonconstant and characterized exactly by input zero. -/
theorem auditedDecisionProblem_accept_iff_zero
    (input : Nat) :
    auditedDecisionProblem.Accept input ↔
      input = 0 := by
  constructor
  · intro accepted
    by_cases inputZero : input = 0
    · exact inputZero
    · exact
        False.elim
          ((auditedDecision_nonzero_not_satisfiable
              inputZero)
            accepted)
  · intro inputZero
    subst input
    exact
      ⟨auditedYesAssignment,
        auditedDecision_zero_satisfies⟩

/-- Explicit YES instance. -/
theorem auditedDecision_yes :
    auditedDecisionProblem.Accept 0 :=
  (auditedDecisionProblem_accept_iff_zero
    0).2
    rfl

/-- Explicit NO instance. -/
theorem auditedDecision_no :
    ¬
      auditedDecisionProblem.Accept 1 := by
  intro accepted
  have zero :
      (1 : Nat) = 0 :=
    (auditedDecisionProblem_accept_iff_zero
      1).1
      accepted
  cases zero

/-- Exact true-branch residual for every benchmark input. -/
theorem auditedTrueChild_formula
    (input : Nat) :
    (auditedDecisionTrueChild
      input).context.formula =
      symmetricNegativeClause 0 1 ::
        auditedDecisionBackground input := by
  change
    branchResidual
        (auditedDecisionFormula input)
        0
        true =
      symmetricNegativeClause 0 1 ::
        auditedDecisionBackground input
  unfold auditedDecisionFormula
  unfold symmetricBlockFamily
  rw [
    branchResidual_cons_hit
      (symmetricPositiveClause 0 1)
      (symmetricNegativeClause 0 1 ::
        auditedDecisionBackground input)
      0
      true
      (by rfl)
  ]
  rw [
    branchResidual_cons_miss
      (symmetricNegativeClause 0 1)
      (auditedDecisionBackground input)
      0
      true
      (by rfl)
  ]
  rw [
    Cnf.branchResidual_eq_self
      (auditedDecisionBackground_avoids input)
      true
  ]

/-- Exact terminal residual formula of the YES instance. -/
theorem auditedTrueChild_formula_zero :
    (auditedDecisionTrueChild 0).context.formula =
      [symmetricNegativeClause 0 1] := by
  rw [
    auditedTrueChild_formula
  ]
  rfl

/-- Exact terminal residual formula of every NO instance. -/
theorem auditedTrueChild_formula_nonzero
    {input : Nat}
    (inputNonzero : input ≠ 0) :
    (auditedDecisionTrueChild
      input).context.formula =
      [symmetricNegativeClause 0 1, []] := by
  rw [
    auditedTrueChild_formula
  ]
  unfold auditedDecisionBackground
  rw [
    if_neg inputNonzero
  ]

/-- Terminal decision is exactly the benchmark yes/no answer. -/
theorem auditedTerminalDecision_correct
    (input : Nat) :
    auditedTerminalDecision input =
        true ↔
      auditedDecisionProblem.Accept input := by
  rw [
    auditedDecisionProblem_accept_iff_zero
  ]
  by_cases inputZero : input = 0
  · subst input
    simp [
      auditedTerminalDecision,
      auditedTrueChild_formula_zero,
      containsEmptyClause
    ]
  · have terminalFormula :=
      auditedTrueChild_formula_nonzero
        inputZero
    simp [
      auditedTerminalDecision,
      terminalFormula,
      containsEmptyClause,
      inputZero
    ]

/-- Separate executed phase counters of the complete constitutive procedure. -/
structure AuditedDecisionProcedureStats where
  discoveryQueries : Nat
  scheduleAtoms : Nat
  validationQueries : Nat
  executionPrimitiveQueries : Nat
  executionCompositionCandidates : Nat
  terminalChecks : Nat

namespace AuditedDecisionProcedureStats

/-- Total charged source-level event count. -/
def total
    (stats : AuditedDecisionProcedureStats) : Nat :=
  stats.discoveryQueries +
    stats.scheduleAtoms +
    stats.validationQueries +
    stats.executionPrimitiveQueries +
    stats.executionCompositionCandidates +
    stats.terminalChecks

end AuditedDecisionProcedureStats

/-- Complete executable run of the repaired decision benchmark. -/
structure AuditedDecisionProcedureRun where
  result : Bool
  stats : AuditedDecisionProcedureStats

/--
Presented input -> structural discovery -> local schedule production ->
validation -> actual local execution -> terminal decision.

The relation witness is obtained only from auditedDecisionDiscover.
-/
def executeAuditedDecision
    (input : Nat) :
    AuditedDecisionProcedureRun :=
  match found :
      auditedDecisionDiscover input with
  | none =>
      { result := false
        stats :=
          { discoveryQueries := 1
            scheduleAtoms := 0
            validationQueries := 0
            executionPrimitiveQueries := 0
            executionCompositionCandidates := 0
            terminalChecks := 1 } }
  | some relation =>
      let entry :=
        auditedDecisionEntry
          input
          relation
      let validation :=
        validateSearchableCode
          (generatedStructuralFlipAtSearch
            (auditedDecisionFormula input)
            0)
          entry.code
      let execution :=
        entry.executionRun
      { result :=
          auditedTerminalDecision input
        stats :=
          { discoveryQueries := 1
            scheduleAtoms :=
              entry.code.size
            validationQueries :=
              validation.primitiveQueries
            executionPrimitiveQueries :=
              execution.stats.primitiveQueries
            executionCompositionCandidates :=
              execution.stats.compositionCandidates
            terminalChecks := 1 } }

/-- The executable structural discovery failure branch is unreachable. -/
theorem executeAuditedDecision_success_branch
    (input : Nat) :
    ∃ relation,
      auditedDecisionDiscover input =
          some relation := by
  cases found :
      auditedDecisionDiscover input with
  | none =>
      exact
        False.elim
          ((auditedDecisionDiscover_found
              input)
            found)
  | some relation =>
      exact
        ⟨relation,
          rfl⟩

/-- Complete procedure returns the correct terminal yes/no answer. -/
theorem executeAuditedDecision_correct
    (input : Nat) :
    (executeAuditedDecision
      input).result =
        true ↔
      auditedDecisionProblem.Accept input := by
  rcases
      executeAuditedDecision_success_branch
        input with
    ⟨relation, found⟩
  unfold executeAuditedDecision
  rw [found]
  exact
    auditedTerminalDecision_correct
      input

/-- Discovery cost is explicitly one structural relation query. -/
theorem executeAuditedDecision_discoveryQueries
    (input : Nat) :
    (executeAuditedDecision
      input).stats.discoveryQueries =
      1 := by
  rcases
      executeAuditedDecision_success_branch
        input with
    ⟨relation, found⟩
  unfold executeAuditedDecision
  rw [found]

/-- Schedule production is exactly one actually discovered transport atom. -/
theorem executeAuditedDecision_scheduleAtoms
    (input : Nat) :
    (executeAuditedDecision
      input).stats.scheduleAtoms =
      1 := by
  rcases
      executeAuditedDecision_success_branch
        input with
    ⟨relation, found⟩
  unfold executeAuditedDecision
  rw [found]
  exact
    (auditedDecisionEntry
      input
      relation).code_size

/-- Executable validation performs exactly one primitive query. -/
theorem executeAuditedDecision_validationQueries
    (input : Nat) :
    (executeAuditedDecision
      input).stats.validationQueries =
      1 := by
  rcases
      executeAuditedDecision_success_branch
        input with
    ⟨relation, found⟩
  unfold executeAuditedDecision
  rw [found]
  exact
    (auditedDecisionEntry
      input
      relation).validation_primitiveQueries

/-- Actual local execution performs exactly one primitive query. -/
theorem executeAuditedDecision_executionPrimitiveQueries
    (input : Nat) :
    (executeAuditedDecision
      input).stats.executionPrimitiveQueries =
      1 := by
  rcases
      executeAuditedDecision_success_branch
        input with
    ⟨relation, found⟩
  unfold executeAuditedDecision
  rw [found]
  exact
    ((auditedDecisionEntry
      input
      relation).executionRun_stats).1

/-- Actual local execution inspects no composition candidates. -/
theorem executeAuditedDecision_executionCompositionCandidates
    (input : Nat) :
    (executeAuditedDecision
      input).stats.executionCompositionCandidates =
      0 := by
  rcases
      executeAuditedDecision_success_branch
        input with
    ⟨relation, found⟩
  unfold executeAuditedDecision
  rw [found]
  exact
    ((auditedDecisionEntry
      input
      relation).executionRun_stats).2

/-- Terminal decision is explicitly charged once. -/
theorem executeAuditedDecision_terminalChecks
    (input : Nat) :
    (executeAuditedDecision
      input).stats.terminalChecks =
      1 := by
  rcases
      executeAuditedDecision_success_branch
        input with
    ⟨relation, found⟩
  unfold executeAuditedDecision
  rw [found]

/-- Complete source-level charged event count is exactly five. -/
theorem executeAuditedDecision_total
    (input : Nat) :
    (executeAuditedDecision
      input).stats.total =
      5 := by
  unfold AuditedDecisionProcedureStats.total
  rw [
    executeAuditedDecision_discoveryQueries,
    executeAuditedDecision_scheduleAtoms,
    executeAuditedDecision_validationQueries,
    executeAuditedDecision_executionPrimitiveQueries,
    executeAuditedDecision_executionCompositionCandidates,
    executeAuditedDecision_terminalChecks
  ]

/-- Complete real procedure cost is polynomial in the declared input size. -/
theorem executeAuditedDecision_total_inputPolynomiallyBounded :
    InputPolynomiallyBounded
      auditedDecisionProblem.inputSize
      (fun input =>
        (executeAuditedDecision
          input).stats.total) := by
  refine
    ⟨CostPolynomial.constant 5, ?_⟩
  intro input
  change
    (executeAuditedDecision
        input).stats.total ≤
      (CostPolynomial.constant 5).eval
        (auditedDecisionProblem.inputSize input)
  rw [
    executeAuditedDecision_total
  ]
  exact Nat.le_refl 5

/-- Minimal executable classical decider code for the same extensional language. -/
def auditedDecisionDeciderCode :
    DeciderCode :=
  .inputEq 0

/-- The fixed decider code agrees with the complete constitutive procedure result. -/
theorem auditedDecisionDeciderCode_agrees
    (input : Nat) :
    (executeDecider
        auditedDecisionDeciderCode
        input).result =
      (executeAuditedDecision
        input).result := by
  by_cases inputZero : input = 0
  · subst input
    simp [
      auditedDecisionDeciderCode,
      executeDecider,
      executeAuditedDecision_correct,
      auditedDecision_yes
    ]
  · have notAccepted :
      ¬ auditedDecisionProblem.Accept input := by
        intro accepted
        exact
          inputZero
            ((auditedDecisionProblem_accept_iff_zero
              input).1
              accepted)
    have procedureFalse :
        (executeAuditedDecision
          input).result =
            false := by
      cases result :
          (executeAuditedDecision
            input).result with
      | false =>
          rfl
      | true =>
          have accepted :=
            (executeAuditedDecision_correct
              input).1
              result
          exact
            False.elim
              (notAccepted accepted)
    simp [
      auditedDecisionDeciderCode,
      executeDecider,
      inputZero,
      procedureFalse
    ]

/-- Positive executable P interface for the nonconstant benchmark. -/
def auditedDecisionPolynomialDecider :
    PolynomialDecider
      auditedDecisionProblem :=
  { code :=
      auditedDecisionDeciderCode
    correct := by
      intro input
      rw [
        auditedDecisionDeciderCode_agrees,
        executeAuditedDecision_correct
      ] }

/-- The repaired P bridge is inhabited by a real executable code. -/
theorem auditedDecision_inP :
    InP
      auditedDecisionProblem :=
  ⟨auditedDecisionPolynomialDecider⟩

/-- Minimal verifier: input must be zero and certificate must be zero. -/
def auditedDecisionVerifierCode :
    VerifierCode :=
  .both
    (.inputEq 0)
    (.witnessEq 0)

/-- Positive executable NP verifier interface for the same nonconstant benchmark. -/
def auditedDecisionPolynomialVerifier :
    PolynomialVerifier
      auditedDecisionProblem :=
  { code :=
      auditedDecisionVerifierCode
    certificateBound :=
      CostPolynomial.constant 1
    sound := by
      intro input witness verified
      by_cases inputZero : input = 0
      · exact
          (auditedDecisionProblem_accept_iff_zero
            input).2
            inputZero
      · have impossible :
            (false : Bool) = true := by
          simpa [
            auditedDecisionVerifierCode,
            executeVerifier,
            inputZero
          ] using verified
        cases impossible
    complete := by
      intro input accepted
      have inputZero :=
        (auditedDecisionProblem_accept_iff_zero
          input).1
          accepted
      subst input
      refine
        ⟨0, ?_, ?_⟩
      · change
          BinaryRepresentation.natBitSize 0 ≤
            1
        decide
      · rfl }

/-- The repaired NP bridge is inhabited by a real executable verifier. -/
theorem auditedDecision_inNP :
    InNP
      auditedDecisionProblem :=
  ⟨auditedDecisionPolynomialVerifier⟩

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.auditedDecisionFormula
#print axioms ConstitutiveSearch.SAT.auditedDecisionDiscover
#print axioms ConstitutiveSearch.SAT.auditedDecisionDiscover_found
#print axioms ConstitutiveSearch.SAT.auditedDecisionProblem
#print axioms ConstitutiveSearch.SAT.auditedDecisionProblem_accept_iff_zero
#print axioms ConstitutiveSearch.SAT.auditedDecision_yes
#print axioms ConstitutiveSearch.SAT.auditedDecision_no
#print axioms ConstitutiveSearch.SAT.auditedTerminalDecision
#print axioms ConstitutiveSearch.SAT.auditedTerminalDecision_correct
#print axioms ConstitutiveSearch.SAT.executeAuditedDecision
#print axioms ConstitutiveSearch.SAT.executeAuditedDecision_correct
#print axioms ConstitutiveSearch.SAT.executeAuditedDecision_total
#print axioms ConstitutiveSearch.SAT.executeAuditedDecision_total_inputPolynomiallyBounded
#print axioms ConstitutiveSearch.SAT.auditedDecisionPolynomialDecider
#print axioms ConstitutiveSearch.SAT.auditedDecision_inP
#print axioms ConstitutiveSearch.SAT.auditedDecisionPolynomialVerifier
#print axioms ConstitutiveSearch.SAT.auditedDecision_inNP
/- AXIOM_AUDIT_END -/
