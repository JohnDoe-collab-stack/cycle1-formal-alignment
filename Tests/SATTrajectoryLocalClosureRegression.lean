import ConstitutiveSearch.SAT.TrajectoryLocalClosure

namespace ConstitutiveSearch.Tests.SATTrajectoryLocalClosureRegression

open ConstitutiveSearch
open SAT

theorem explicitThreePrimitiveQueries :
    (explicitFamilyTrajectoryLocalClosureStats 3).primitiveQueries =
      3 :=
  explicitFamilyTrajectoryLocalClosureStats_primitiveQueries 3

theorem explicitThreeCompositionCandidates :
    (explicitFamilyTrajectoryLocalClosureStats 3).compositionCandidates =
      0 :=
  explicitFamilyTrajectoryLocalClosureStats_compositionCandidates 3

theorem explicitLocalPrimitivePolynomial :
    InputPolynomiallyBounded
      explicitFamilyInputBitSize
      (fun count =>
        (explicitFamilyTrajectoryLocalClosureStats count).primitiveQueries) :=
  explicitFamilyTrajectoryLocalPrimitiveQueries_inputPolynomiallyBounded

theorem explicitLocalCompositionPolynomial :
    InputPolynomiallyBounded
      explicitFamilyInputBitSize
      (fun count =>
        (explicitFamilyTrajectoryLocalClosureStats count).compositionCandidates) :=
  explicitFamilyTrajectoryLocalCompositionCandidates_inputPolynomiallyBounded

end ConstitutiveSearch.Tests.SATTrajectoryLocalClosureRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATTrajectoryLocalClosureRegression.explicitThreePrimitiveQueries
#print axioms ConstitutiveSearch.Tests.SATTrajectoryLocalClosureRegression.explicitThreeCompositionCandidates
#print axioms ConstitutiveSearch.Tests.SATTrajectoryLocalClosureRegression.explicitLocalPrimitivePolynomial
#print axioms ConstitutiveSearch.Tests.SATTrajectoryLocalClosureRegression.explicitLocalCompositionPolynomial
/- AXIOM_AUDIT_END -/
