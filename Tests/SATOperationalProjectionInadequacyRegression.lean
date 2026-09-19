import ConstitutiveSearch.SAT.OperationalProjectionInadequacy

namespace ConstitutiveSearch.Tests.SATOperationalProjectionInadequacyRegression

open ConstitutiveSearch
open SAT

/-- The successful run obtains and evaluates exactly one transport atom. -/
theorem codeIsApplied
    (input : Nat) :
    (runIntegratedOperational
      input
      .reconstructible).execution.terminalBit = some true /\
    (runIntegratedOperational
      input
      .reconstructible).execution.codeAtoms = 1 :=
  ⟨runIntegratedOperational_reconstructible input,
    runIntegratedOperational_reconstructible_codeAtoms input⟩

/-- Generic success exposes the exact code-evaluation equation, not a target copy. -/
theorem terminalEquationIsCodeEvaluation
    {rootFormula : Cnf}
    (selected observed : Var)
    (source target : GeneratedStructuralBranchContext rootFormula)
    (continuation : GeneratedStructuralBranchContinuation source)
    (search : InstrumentedFlipSearchRun selected source target)
    (relation : GeneratedStructuralFlipAtRelation selected source target)
    (found : search.relation? = some relation) :
    (executeInstrumentedSearchResult
        selected observed source target continuation search).terminalBit =
      some
        (((((TransportCode.ofGenerator relation).eval
            (generatedStructuralFlipAtAction rootFormula selected)).map
          continuation).1) observed) :=
  (executeInstrumentedSearchResult_success_exact
    selected observed source target continuation search relation found).1

/-- A provenance mismatch produces neither a terminal bit nor a code atom. -/
theorem mismatchCannotReuseTarget
    (input : Nat) :
    (runIntegratedOperational
      input
      .provenanceMismatch).execution.terminalBit = none /\
    (runIntegratedOperational
      input
      .provenanceMismatch).execution.codeAtoms = 0 :=
  ⟨runIntegratedOperational_provenanceMismatch input,
    runIntegratedOperational_provenanceMismatch_codeAtoms input⟩

/-- The public two-organization experiment accepts only an input index. -/
theorem publicExperimentIsInputOnly
    (input : Nat) :
    (runOperationalProjectionExperiment
        input).reconstructible.execution.terminalBit = some true /\
      (runOperationalProjectionExperiment
        input).provenanceMismatch.execution.terminalBit = none :=
  runOperationalProjectionExperiment_outputs input

/-- The discovery trace carries executable data and is not a proof singleton. -/
theorem discoveryTraceCarriesData :
    ¬ Subsingleton RetainedDiscoveryTrace :=
  retainedDiscoveryTrace_not_subsingleton

/-- The useful variable and its work are outputs of the discovery run. -/
theorem discoveryIsEndogenous
    (input : Nat) :
    (operationalDiscoveryTrace input).selected? =
        some (growingDiscoverySplitVar input) /\
      (operationalDiscoveryTrace input).attempts = input + 2 /\
      (operationalDiscoveryTrace input).extractionStats.literalVisits =
        input + 5 :=
  ⟨operationalDiscoveryTrace_selected input,
    operationalDiscoveryTrace_attempts input,
    (operationalDiscoveryTrace_extraction input).2⟩

/-- The instrumented attempt itself chooses the witness it accounts for. -/
theorem instrumentedAttemptIsAuthoritative
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula)
    (candidate : Var) :
    (runInstrumentedCandidateAttempt state candidate).discovery? =
      tryEndogenousFlipCandidate state candidate :=
  runInstrumentedCandidateAttempt_discovery_exact state candidate

/-- The downstream schedule is fed by the proof-relevant witness returned by the run. -/
theorem proofRelevantDiscoveryFlows
    (input : Nat) :
    exists discovery,
      (operationalInstrumentedDiscoveryRun
        input).outcome.discovered? = some discovery /\
      discovery.var = growingDiscoverySplitVar input :=
  operationalInstrumentedDiscoveryRun_found input

/-- Rejected candidates and the successful candidate are retained in order. -/
theorem discoveryRetainsAttemptedPrefix
    (input : Nat) :
    (operationalDiscoveryTrace input).attemptTrace.map
        InstrumentedCandidateAttemptRecord.candidate =
      distinctDecoyVariables (input + 1) ++
        [growingDiscoverySplitVar input] :=
  operationalDiscoveryTrace_attemptedCandidates input

/-- Discovery relation work is the fold of the per-candidate executed traces. -/
theorem discoveryAccountingIsTraceDerived
    (input : Nat) :
    (operationalDiscoveryTrace input).relationStats =
      aggregateInstrumentedAttemptStats
        (operationalDiscoveryTrace input).attemptTrace :=
  operationalDiscoveryTrace_relationStats_exact input

/-- Both witnesses have the same input and the same strong public snapshot. -/
theorem sameInputCannotBypassProjection
    (input : Nat) :
    (reconstructibleInstance input).input =
        (provenanceMismatchInstance input).input /\
      inputAwareExtensionalProjection (reconstructibleInstance input) =
        inputAwareExtensionalProjection (provenanceMismatchInstance input) /\
      operationalObservation (reconstructibleInstance input) ≠
        operationalObservation (provenanceMismatchInstance input) :=
  ⟨rfl,
    operational_same_input_same_extensional_projection input,
    operational_same_input_observations_different input⟩

/-- Constitutive difference is proved before and independently of projection equality. -/
theorem constitutionsDifferBeforeProjection
    (input : Nat) :
    (operationalPositiveTarget input).context.decisions ≠
      (operationalNegativeTarget input).context.decisions :=
  operationalTarget_constitutions_different input

/-- Input-aware reconstruction of the operational result is impossible. -/
theorem inputAwareFactorizationStillFails :
    ¬ InputAwareProjectionContextuallyAdequate :=
  inputAwareProjection_not_contextually_adequate

/-- Formula transformation counters charge every traversed CNF literal. -/
theorem transformationChargesWholeFormula
    (selected : Var)
    (formula : Cnf) :
    (runCnfFlip selected formula).literalVisits =
      Cnf.literalCount formula :=
  runCnfFlip_literalVisits selected formula

/-- The integrated relation tester, not only its primitive, exposes that charge. -/
theorem relationTestChargesWholeSource
    {rootFormula : Cnf}
    (selected : Var)
    (source target : GeneratedStructuralBranchContext rootFormula) :
    (runInstrumentedFlipSearch
      selected source target).stats.formulaTransformLiteralVisits =
        Cnf.literalCount source.context.formula :=
  runInstrumentedFlipSearch_formulaTransformLiteralVisits
    selected source target

/-- Equality validation counters charge every traversed CNF literal. -/
theorem comparisonChargesWholeFormula
    (formula : Cnf) :
    (runCnfComparison formula formula).literalVisits =
      Cnf.literalCount formula :=
  runCnfComparison_equal_literalVisits formula

/-- The late mismatch is reached after the complete growing common prefix. -/
theorem deepMismatchWorkIsExact
    (input : Nat) :
    (runIntegratedOperational
      input
      .provenanceMismatch).execution.stats.historyComparisonDecisionVisits =
        input + 2 :=
  runIntegratedOperational_provenanceMismatch_historyVisits input

/-- Published phase costs are projections of the executed integrated run. -/
theorem accountingComesFromRun
    (input : Nat)
    (organization : OperationalOrganization) :
    (integratedOperationalStats input organization).discoveryAttempts =
        input + 2 /\
      (integratedOperationalStats
        input
        organization).extractionLiteralVisits = input + 5 :=
  ⟨integratedOperationalStats_discoveryAttempts input organization,
    integratedOperationalStats_extractionLiteralVisits input organization⟩

/-- Terminal readout accounting follows the branch actually executed. -/
theorem terminalReadoutAccountingIsOperational
    (input : Nat) :
    (integratedOperationalStats
      input
      .reconstructible).terminalReadouts = 1 /\
      (integratedOperationalStats
        input
        .provenanceMismatch).terminalReadouts = 0 :=
  ⟨integratedOperationalStats_reconstructible_terminalReadouts input,
    integratedOperationalStats_provenanceMismatch_terminalReadouts input⟩

/-- Input growth changes depth and three independently executed work measures. -/
theorem indexIsOperational
    (input : Nat) :
    (operationalSource input).depth <
        (operationalSource (input + 1)).depth /\
      (operationalDiscoveryTrace input).attempts <
        (operationalDiscoveryTrace (input + 1)).attempts /\
      (operationalDiscoveryTrace input).extractionStats.literalVisits <
        (operationalDiscoveryTrace
          (input + 1)).extractionStats.literalVisits /\
      (runIntegratedOperational
        input
        .provenanceMismatch).execution.stats.historyComparisonDecisionVisits <
        (runIntegratedOperational
          (input + 1)
          .provenanceMismatch).execution.stats.historyComparisonDecisionVisits :=
  ⟨operationalDepth_strict input,
    operationalDiscoveryAttempts_strict input,
    operationalExtractionLiteralVisits_strict input,
    operationalNegativeHistoryWork_strict input⟩

/-- The complete scoped certificate remains available as one regression gate. -/
theorem integratedCertificate :
    OperationalProjectionInadequacyCertificate :=
  operationalProjectionInadequacyCertified

/-- The repair exposes only a review marker, never a global completion marker. -/
theorem reviewBoundary :
    operationalProjectionRepairStatus =
      OperationalProjectionRepairStatus.readyForIndependentAdversarialAudit :=
  operationalProjectionRepair_readyForIndependentAudit

end ConstitutiveSearch.Tests.SATOperationalProjectionInadequacyRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATOperationalProjectionInadequacyRegression.codeIsApplied
#print axioms ConstitutiveSearch.Tests.SATOperationalProjectionInadequacyRegression.terminalEquationIsCodeEvaluation
#print axioms ConstitutiveSearch.Tests.SATOperationalProjectionInadequacyRegression.mismatchCannotReuseTarget
#print axioms ConstitutiveSearch.Tests.SATOperationalProjectionInadequacyRegression.publicExperimentIsInputOnly
#print axioms ConstitutiveSearch.Tests.SATOperationalProjectionInadequacyRegression.discoveryTraceCarriesData
#print axioms ConstitutiveSearch.Tests.SATOperationalProjectionInadequacyRegression.discoveryIsEndogenous
#print axioms ConstitutiveSearch.Tests.SATOperationalProjectionInadequacyRegression.instrumentedAttemptIsAuthoritative
#print axioms ConstitutiveSearch.Tests.SATOperationalProjectionInadequacyRegression.proofRelevantDiscoveryFlows
#print axioms ConstitutiveSearch.Tests.SATOperationalProjectionInadequacyRegression.discoveryRetainsAttemptedPrefix
#print axioms ConstitutiveSearch.Tests.SATOperationalProjectionInadequacyRegression.discoveryAccountingIsTraceDerived
#print axioms ConstitutiveSearch.Tests.SATOperationalProjectionInadequacyRegression.sameInputCannotBypassProjection
#print axioms ConstitutiveSearch.Tests.SATOperationalProjectionInadequacyRegression.constitutionsDifferBeforeProjection
#print axioms ConstitutiveSearch.Tests.SATOperationalProjectionInadequacyRegression.inputAwareFactorizationStillFails
#print axioms ConstitutiveSearch.Tests.SATOperationalProjectionInadequacyRegression.transformationChargesWholeFormula
#print axioms ConstitutiveSearch.Tests.SATOperationalProjectionInadequacyRegression.relationTestChargesWholeSource
#print axioms ConstitutiveSearch.Tests.SATOperationalProjectionInadequacyRegression.comparisonChargesWholeFormula
#print axioms ConstitutiveSearch.Tests.SATOperationalProjectionInadequacyRegression.deepMismatchWorkIsExact
#print axioms ConstitutiveSearch.Tests.SATOperationalProjectionInadequacyRegression.accountingComesFromRun
#print axioms ConstitutiveSearch.Tests.SATOperationalProjectionInadequacyRegression.terminalReadoutAccountingIsOperational
#print axioms ConstitutiveSearch.Tests.SATOperationalProjectionInadequacyRegression.indexIsOperational
#print axioms ConstitutiveSearch.Tests.SATOperationalProjectionInadequacyRegression.integratedCertificate
#print axioms ConstitutiveSearch.Tests.SATOperationalProjectionInadequacyRegression.reviewBoundary
/- AXIOM_AUDIT_END -/
