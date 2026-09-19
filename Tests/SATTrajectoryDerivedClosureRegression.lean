import ConstitutiveSearch.SAT.TrajectoryDerivedClosure

namespace ConstitutiveSearch.Tests.SATTrajectoryDerivedClosureRegression

open ConstitutiveSearch
open SAT

theorem explicitThreeGeneratorCount :
    (explicitFamilyTrajectoryDecisionVars 3).length =
      3 :=
  explicitFamilyTrajectoryDecisionVars_length 3

theorem explicitThreeCandidateCount :
    (explicitFamilyTrajectoryClosureCandidates 3).length =
      6 := by
  simpa using
    explicitFamilyTrajectoryClosureCandidates_length 3

theorem explicitThreeFuel :
    explicitFamilyTrajectoryClosureFuel 3 =
      3 :=
  explicitFamilyTrajectoryClosureFuel_eq 3

theorem explicitThreeDerivedSearchExists :
    ∃ search :
        RelationSearch
          (TransportClosure
            (ProvenanceStructuralFlipWitness
              (rootFormula :=
                explicitStackedSymmetricFamily 3)
              (explicitFamilyTrajectoryDecisionVars 3))),
      search =
        explicitFamilyTrajectoryDerivedClosureSearch 3 :=
  ⟨explicitFamilyTrajectoryDerivedClosureSearch 3, rfl⟩

end ConstitutiveSearch.Tests.SATTrajectoryDerivedClosureRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATTrajectoryDerivedClosureRegression.explicitThreeGeneratorCount
#print axioms ConstitutiveSearch.Tests.SATTrajectoryDerivedClosureRegression.explicitThreeCandidateCount
#print axioms ConstitutiveSearch.Tests.SATTrajectoryDerivedClosureRegression.explicitThreeFuel
#print axioms ConstitutiveSearch.Tests.SATTrajectoryDerivedClosureRegression.explicitThreeDerivedSearchExists
/- AXIOM_AUDIT_END -/
