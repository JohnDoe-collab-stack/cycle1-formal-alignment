import ConstitutiveSearch.BitMachineAdequacyStress
import ConstitutiveSearch.SAT.AuditedNPAndPObjective
import ConstitutiveSearch.SAT.GrowingDiscoveryBenchmark
import ConstitutiveSearch.SAT.CausalProjectionNonFactorization
import ConstitutiveSearch.SAT.ParametricProvenanceNonFactorization

/-!
# Historical readiness boundary submitted after the second-audit repair

This module preserves the exact evidence package that was submitted to the
third adversarial review.  That review found material scope gaps, so this status
is historical and is superseded by `OperationalProjectionInadequacy`.  It is
deliberately not a replacement for the withdrawn global closure marker.

The computational claims in this package are scoped to `BitMachine`.  No field
asserts an equivalence with classical P or NP.  Its former readiness value is
preserved so the audited commit remains reproducible; it is not the active
readiness boundary after the successful counterprobes.
-/

namespace ConstitutiveSearch
namespace SAT

/-- Explicit computational scope of the repaired executable claims. -/
inductive SecondAuditComputationalScope where
  | bitMachineOnly
  deriving DecidableEq, Repr

/-- Historical pre-third-audit status; not a completion or closure status. -/
inductive SecondAuditRepairStatus where
  | readyForIndependentAdversarialAudit
  deriving DecidableEq, Repr

def secondAuditComputationalScope : SecondAuditComputationalScope :=
  .bitMachineOnly

def secondAuditRepairStatus : SecondAuditRepairStatus :=
  .readyForIndependentAdversarialAudit

/--
Evidence already constructed for the repaired computational, discovery,
causal, and projection-loss boundaries.
-/
structure SecondAuditRepairEvidence : Prop where
  oldClosureWithdrawn :
    firstAuditClosureStatus =
      FirstAuditClosureStatus.withdrawnAfterSecondAudit
  parityExecutableP :
    InBitMachineP bitParityProblem
  parityExecutableNP :
    InBitMachineNP bitParityProblem
  parityCostStrict :
    ∀ (input : List Bool) (bit : Bool),
      bitParityPolynomialDecider.executedCost input <
        bitParityPolynomialDecider.executedCost (input ++ [bit])
  certificateOperational :
    ∀ input : List Bool,
      (executeBitMachineWithCertificate
          certificateEchoProgram input [true] 4).result? ≠
        (executeBitMachineWithCertificate
          certificateEchoProgram input [false] 4).result?
  workTapeUnbounded :
    ∀ bound : Nat,
      exists input : List Bool,
        bound <
          (executeBitMachine
            workGrowthProgram
            input
            (workGrowthFuelPolynomial.eval input.length)).finalState.workLeft.length
  extractionInstrumented :
    ∀ input : Nat,
      (runCandidateExtraction
          (distinctGrowingDiscoveryRoot input)).stats.clauseVisits = 3 /\
        (runCandidateExtraction
          (distinctGrowingDiscoveryRoot input)).stats.literalVisits =
            input + 5
  discoveryExactAndGrowing :
    ∀ input : Nat,
      (∃ discovery,
        (runEndogenousFlipDiscovery
          (distinctGrowingDiscoveryRoot input)).outcome.discovered? =
            some discovery /\
        discovery.var = growingDiscoverySplitVar input /\
        (runEndogenousFlipDiscovery
          (distinctGrowingDiscoveryRoot input)).outcome.attempts =
            input + 2) /\
      (runEndogenousFlipDiscovery
          (distinctGrowingDiscoveryRoot input)).outcome.attempts <
        (runEndogenousFlipDiscovery
          (distinctGrowingDiscoveryRoot (input + 1))).outcome.attempts
  causalDecisionCorrect :
    ∀ input : Nat,
      (executeCausalDecision input).result = true <->
        CausalDecisionAccept input
  terminalFromExecution :
    ∀ input : Nat,
      let run := executeCausalDecisionCertified input
      run.terminal.scan =
        scanExecutedTerminal
          run.execution.producedState.context.formula
  causalProjectionLoss :
    CausalCertifiedProjectionLoss
  parametricProjectionLoss :
    ParametricProvenanceProjectionLoss

/-- Constructed evidence at the exact boundary submitted for re-audit. -/
theorem secondAuditRepairEvidence :
    SecondAuditRepairEvidence :=
  { oldClosureWithdrawn := firstAuditClosure_isWithdrawn
    parityExecutableP := bitParity_inBitMachineP
    parityExecutableNP := bitParity_inBitMachineNP
    parityCostStrict := bitParityProgram_cost_strict_append
    certificateOperational := certificateChannel_isOperational
    workTapeUnbounded := workTapeGrowth_unbounded
    extractionInstrumented := distinctGrowingDiscovery_extraction_stats
    discoveryExactAndGrowing := by
      intro input
      exact
        ⟨distinctGrowingDiscovery_found_after_exact_attempts input,
          distinctGrowingDiscovery_attempts_strict input⟩
    causalDecisionCorrect := executeCausalDecision_correct
    terminalFromExecution := by
      intro input
      exact
        (executeCausalDecisionCertified input).terminal_from_execution
    causalProjectionLoss := causalCertifiedProjectionLoss
    parametricProjectionLoss := parametricProvenanceProjectionLoss }

/-- The historical submitted status remains reproducible. -/
theorem secondAuditRepair_isReadyForIndependentAudit :
    secondAuditRepairStatus =
      .readyForIndependentAdversarialAudit :=
  rfl

/-- The executable complexity vocabulary remains explicitly BitMachine-scoped. -/
theorem secondAuditRepair_scope_isBitMachineOnly :
    secondAuditComputationalScope = .bitMachineOnly :=
  rfl

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.SecondAuditComputationalScope
#print axioms ConstitutiveSearch.SAT.SecondAuditRepairStatus
#print axioms ConstitutiveSearch.SAT.SecondAuditRepairEvidence
#print axioms ConstitutiveSearch.SAT.secondAuditRepairEvidence
#print axioms ConstitutiveSearch.SAT.secondAuditRepair_isReadyForIndependentAudit
#print axioms ConstitutiveSearch.SAT.secondAuditRepair_scope_isBitMachineOnly
/- AXIOM_AUDIT_END -/
