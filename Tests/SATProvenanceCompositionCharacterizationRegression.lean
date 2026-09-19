import ConstitutiveSearch.SAT.ProvenanceCompositionCharacterization

namespace ConstitutiveSearch.Tests.SATProvenanceCompositionCharacterizationRegression

open ConstitutiveSearch
open SAT

theorem explicitFamilyCompositionCharacterization
    (count : Nat)
    (source target :
      GeneratedStructuralBranchContext
        (explicitStackedSymmetricFamily count)) :
    PrimitiveHitPath.GlobalCompositionRequired
        (explicitFamilyResourceTrajectory count).trajectory.primitiveSearch
        source
        target ↔
      (explicitFamilyResourceTrajectory count).trajectory.primitiveSearch.find
          source
          target =
        none ∧
        ∃ code :
            TransportClosure
              (ProvenanceStructuralFlipWitness
                (rootFormula :=
                  explicitStackedSymmetricFamily count)
                (explicitFamilyTrajectoryDecisionVars count))
              source
              target,
          2 ≤ code.size :=
  (explicitFamilyResourceTrajectory count).trajectory.globalCompositionRequired_iff_provenanceCode
    source
    target

end ConstitutiveSearch.Tests.SATProvenanceCompositionCharacterizationRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATProvenanceCompositionCharacterizationRegression.explicitFamilyCompositionCharacterization
/- AXIOM_AUDIT_END -/
