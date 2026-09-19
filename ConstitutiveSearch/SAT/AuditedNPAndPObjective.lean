import ConstitutiveSearch.SAT.TrajectoryScheduleComposition
import ConstitutiveSearch.SAT.TrajectoryConstitutiveSynthesis
import ConstitutiveSearch.SAT.UngatedProvenanceNonFactorization
import ConstitutiveSearch.SAT.PostAuditDecisionBenchmark

/-!
# Audited closure of the NP AND/OR P objective

This is the post-audit closure certificate.

It does not reuse the pre-audit projection-loss package and it does not use
F(n) as the final decision problem.

The retained structural results are:
* exact endpoint composability for local schedules;
* proof that multi-step FlipSymmetricTrajectory schedules remain local sibling
  reductions rather than fake parent-to-child transport paths;
* the already-audited quantitative synthesis on F(n), used only as a structural
  trajectory/schedule/accounting benchmark.

The repaired decision result is instead the nonconstant
PostAuditDecisionBenchmark:
* a real YES and a real NO instance;
* structural relation discovery is executable and charged;
* the one-atom schedule is produced from the discovery result;
* validation is executable and charged;
* local execution is an actual candidate-free run;
* terminal scanning is executable and charged by its own run statistics;
* the total declared source-level event cost is input-polynomial;
* P/NP interfaces derive cost from executable code runs;
* the P-like and NP-like SearchSystem roles have non-vacu executable bridges.

Projection loss is certified only by the ungated provenance separator using one
and the same generatedStructuralFlipAtSearch engine on both sides.

No statement about SAT general, P = NP, P != NP, or all CNF is contained here.
-/

namespace ConstitutiveSearch
namespace SAT

/--
Post-audit closure of the constitutive program itself.

The F(n) component below is structural/quantitative only. Decision closure is
supplied separately by auditedDecisionProblem.
-/
structure AuditedNPAndPProgramClosed : Prop where
  endpointComposition :
    ∀ {rootFormula : Cnf}
      (first :
        ConstitutedLocalWitness rootFormula)
      (rest :
        List (ConstitutedLocalWitness rootFormula)),
      ConstitutedLocalSchedule.EndpointComposable
          (first :: rest) →
        ∃ target :
            GeneratedStructuralBranchContext rootFormula,
          ∃ code :
              TransportClosure
                (GeneratedStructuralFlipWitness
                  (rootFormula := rootFormula))
                first.source
                target,
            code.size =
              (first :: rest).length
  trajectorySchedulesRemainLocal :
    ∀ {rootFormula : Cnf}
      {start finish :
        GeneratedStructuralBranchContext rootFormula}
      {length : Nat}
      (trajectory :
        FlipSymmetricTrajectory
          start
          finish
          length),
      2 ≤ length →
        ¬
          ConstitutedLocalSchedule.EndpointComposable
            trajectory.constitutedLocalWitnesses
  structuralQuantitativeBenchmark :
    ExplicitFamilyQuantitativeProgramClosed
  decisionYes :
    auditedDecisionProblem.Accept 0
  decisionNo :
    ¬
      auditedDecisionProblem.Accept 1
  discoveredSchedule :
    ∀ input : Nat,
      ∃ schedule,
        auditedDecisionSchedule input =
            some schedule ∧
          schedule.length = 1
  decisionCorrect :
    ∀ input : Nat,
      (executeAuditedDecision
        input).result =
          true ↔
        auditedDecisionProblem.Accept input
  discoveryQueryExact :
    ∀ input : Nat,
      (executeAuditedDecision
        input).stats.discoveryQueries =
        1
  scheduleAtomExact :
    ∀ input : Nat,
      (executeAuditedDecision
        input).stats.scheduleAtoms =
        1
  validationQueryExact :
    ∀ input : Nat,
      (executeAuditedDecision
        input).stats.validationQueries =
        1
  executionPrimitiveExact :
    ∀ input : Nat,
      (executeAuditedDecision
        input).stats.executionPrimitiveQueries =
        1
  executionCompositionExact :
    ∀ input : Nat,
      (executeAuditedDecision
        input).stats.executionCompositionCandidates =
        0
  terminalCostDerived :
    ∀ input : Nat,
      (executeAuditedDecision
        input).stats.terminalChecks =
        (auditedTerminalRun
          input).clauseChecks
  totalCostPolynomial :
    InputPolynomiallyBounded
      auditedDecisionProblem.inputSize
      (fun input =>
        (executeAuditedDecision
          input).stats.total)
  ungatedProjectionLoss :
    UngatedConstitutiveProjectionLoss

/-- All four post-audit program obligations are jointly realized. -/
theorem auditedNPAndPProgramClosed :
    AuditedNPAndPProgramClosed :=
  { endpointComposition :=
      ConstitutedLocalSchedule.endpointComposable_hasTransportCode
    trajectorySchedulesRemainLocal :=
      FlipSymmetricTrajectory.constitutedLocalWitnesses_not_endpointComposable_of_two_le
    structuralQuantitativeBenchmark :=
      explicitFamilyQuantitativeProgramClosed
    decisionYes :=
      auditedDecision_yes
    decisionNo :=
      auditedDecision_no
    discoveredSchedule :=
      auditedDecisionSchedule_found
    decisionCorrect :=
      executeAuditedDecision_correct
    discoveryQueryExact :=
      executeAuditedDecision_discoveryQueries
    scheduleAtomExact :=
      executeAuditedDecision_scheduleAtoms
    validationQueryExact :=
      executeAuditedDecision_validationQueries
    executionPrimitiveExact :=
      executeAuditedDecision_executionPrimitiveQueries
    executionCompositionExact :=
      executeAuditedDecision_executionCompositionCandidates
    terminalCostDerived :=
      executeAuditedDecision_terminalChecks
    totalCostPolynomial :=
      executeAuditedDecision_total_inputPolynomiallyBounded
    ungatedProjectionLoss :=
      ungatedConstitutiveProjectionLoss }

/--
Final repaired bridge certificate.

The classical/extensional view preserves the yes/no answer, but the ungated
separator in the program field proves that provenance-sensitive
reconstructibility and resulting reduction width do not factor through the
residual-only projection.
-/
structure AuditedNPAndPObjectiveComplete : Prop where
  program :
    AuditedNPAndPProgramClosed
  extensionalDecisionPreserved :
    ∀ input : Nat,
      (executeDecider
        auditedDecisionDeciderCode
        input).result =
      (executeAuditedDecision
        input).result
  pInterface :
    InP
      auditedDecisionProblem
  npInterface :
    InNP
      auditedDecisionProblem
  pLikeProjection :
    InP
      (searchSystemDecisionProblem
        satSystem
        auditedDecisionFormula
        auditedDecisionInputSize)
  npLikeProjection :
    InNP
      (searchSystemDecisionProblem
        satSystem
        auditedDecisionFormula
        auditedDecisionInputSize)
  deciderCostFromExecution :
    InputPolynomiallyBounded
      auditedDecisionProblem.inputSize
      auditedDecisionPolynomialDecider.executedCost
  verifierCostFromExecution :
    ∀ input witness : Nat,
      auditedDecisionPolynomialVerifier.executedCost
          input
          witness ≤
        (CostPolynomial.constant
          auditedDecisionPolynomialVerifier.code.size).eval
            (auditedDecisionProblem.inputSize
              input)
  noFictionalZeroDeciderCost :
    ∀ (code : DeciderCode)
      (input : Nat),
      (executeDecider
        code
        input).stats.steps ≠
          0
  noFictionalZeroVerifierCost :
    ∀ (code : VerifierCode)
      (input witness : Nat),
      (executeVerifier
        code
        input
        witness).stats.steps ≠
          0

/--
POST-AUDIT OBJECTIVE MARKER.

This theorem is the only closure marker intended to certify the repaired
NP AND/OR P objective.
-/
theorem auditedNPAndPObjectiveComplete :
    AuditedNPAndPObjectiveComplete :=
  { program :=
      auditedNPAndPProgramClosed
    extensionalDecisionPreserved :=
      auditedDecisionDeciderCode_agrees
    pInterface :=
      auditedDecision_inP
    npInterface :=
      auditedDecision_inNP
    pLikeProjection :=
      auditedDecision_pLike_projects
    npLikeProjection :=
      auditedDecision_npLike_projects
    deciderCostFromExecution :=
      auditedDecisionPolynomialDecider.executedCostPolynomial
    verifierCostFromExecution := by
      intro input witness
      exact
        auditedDecisionPolynomialVerifier.executedCostBound
          input
          witness
    noFictionalZeroDeciderCost :=
      executeDecider_steps_ne_zero
    noFictionalZeroVerifierCost :=
      executeVerifier_steps_ne_zero }

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.AuditedNPAndPProgramClosed
#print axioms ConstitutiveSearch.SAT.auditedNPAndPProgramClosed
#print axioms ConstitutiveSearch.SAT.AuditedNPAndPObjectiveComplete
#print axioms ConstitutiveSearch.SAT.auditedNPAndPObjectiveComplete
/- AXIOM_AUDIT_END -/
