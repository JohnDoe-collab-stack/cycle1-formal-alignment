import ConstitutiveSearch.SAT.ProvenanceSequentialization

namespace ConstitutiveSearch.Tests.SATProvenanceSequentializationRegression

open ConstitutiveSearch
open SAT

theorem explicitFamilyPrimitiveComplete
    (count : Nat) :
    (explicitFamilyResourceTrajectory count).trajectory.primitiveSearch.WitnessComplete :=
  (explicitFamilyResourceTrajectory count).trajectory.primitiveSearch_witnessComplete

theorem explicitFamilyCodeSequentializable
    (count : Nat)
    {source target :
      GeneratedStructuralBranchContext
        (explicitStackedSymmetricFamily count)}
    (code :
      TransportClosure
        (ProvenanceStructuralFlipWitness
          (rootFormula :=
            explicitStackedSymmetricFamily count)
          (explicitFamilyTrajectoryDecisionVars count))
        source
        target) :
    ∃ path :
        PrimitiveHitPath
          (explicitFamilyResourceTrajectory count).trajectory.primitiveSearch
          source
          target,
      path.length = code.size :=
  (explicitFamilyResourceTrajectory count).trajectory.transportCode_hasPrimitiveHitPath
    code

theorem explicitFamilyCodeSequentialExecution
    (count : Nat)
    (fuel : Nat)
    (fuelPositive : 0 < fuel)
    {source target :
      GeneratedStructuralBranchContext
        (explicitStackedSymmetricFamily count)}
    (code :
      TransportClosure
        (ProvenanceStructuralFlipWitness
          (rootFormula :=
            explicitStackedSymmetricFamily count)
          (explicitFamilyTrajectoryDecisionVars count))
        source
        target) :
    ∃ path :
        PrimitiveHitPath
          (explicitFamilyResourceTrajectory count).trajectory.primitiveSearch
          source
          target,
      path.length = code.size ∧
        (path.sequentialStats
            (explicitFamilyTrajectoryClosureCandidates count)
            fuel).primitiveQueries =
          code.size ∧
        (path.sequentialStats
            (explicitFamilyTrajectoryClosureCandidates count)
            fuel).compositionCandidates =
          0 :=
  (explicitFamilyResourceTrajectory count).trajectory.transportCode_hasSequentialExecution
    (explicitFamilyTrajectoryClosureCandidates count)
    fuel
    fuelPositive
    code

end ConstitutiveSearch.Tests.SATProvenanceSequentializationRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATProvenanceSequentializationRegression.explicitFamilyPrimitiveComplete
#print axioms ConstitutiveSearch.Tests.SATProvenanceSequentializationRegression.explicitFamilyCodeSequentializable
#print axioms ConstitutiveSearch.Tests.SATProvenanceSequentializationRegression.explicitFamilyCodeSequentialExecution
/- AXIOM_AUDIT_END -/
