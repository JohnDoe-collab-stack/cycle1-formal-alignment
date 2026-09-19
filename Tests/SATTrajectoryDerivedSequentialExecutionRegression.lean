import ConstitutiveSearch.SAT.TrajectoryDerivedSequentialExecution

namespace ConstitutiveSearch.Tests.SATTrajectoryDerivedSequentialExecutionRegression

open ConstitutiveSearch
open SAT

theorem primitiveQueries3 :
    (explicitFamilySequentialDerivedClosureStats 3).primitiveQueries =
      3 :=
  explicitFamilySequentialDerivedClosureStats_primitiveQueries 3

theorem compositionCandidates3 :
    (explicitFamilySequentialDerivedClosureStats 3).compositionCandidates =
      0 :=
  explicitFamilySequentialDerivedClosureStats_compositionCandidates 3

theorem primitiveExecutedPolynomial :
    InputPolynomiallyBounded
      explicitFamilyInputBitSize
      (fun count =>
        (explicitFamilySequentialDerivedClosureStats count).primitiveQueries) :=
  explicitFamilySequentialDerivedClosurePrimitive_inputPolynomiallyBounded

theorem compositionExecutedPolynomial :
    InputPolynomiallyBounded
      explicitFamilyInputBitSize
      (fun count =>
        (explicitFamilySequentialDerivedClosureStats count).compositionCandidates) :=
  explicitFamilySequentialDerivedClosureComposition_inputPolynomiallyBounded

end ConstitutiveSearch.Tests.SATTrajectoryDerivedSequentialExecutionRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATTrajectoryDerivedSequentialExecutionRegression.primitiveQueries3
#print axioms ConstitutiveSearch.Tests.SATTrajectoryDerivedSequentialExecutionRegression.compositionCandidates3
#print axioms ConstitutiveSearch.Tests.SATTrajectoryDerivedSequentialExecutionRegression.primitiveExecutedPolynomial
#print axioms ConstitutiveSearch.Tests.SATTrajectoryDerivedSequentialExecutionRegression.compositionExecutedPolynomial
/- AXIOM_AUDIT_END -/
