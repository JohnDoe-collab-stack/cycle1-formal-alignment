import ConstitutiveSearch.SAT.TrajectoryConstitutedLocalSchedule

namespace ConstitutiveSearch.Tests.SATTrajectoryConstitutedLocalScheduleRegression

open ConstitutiveSearch
open SAT

theorem witnessCount3 :
    (explicitFamilyConstitutedLocalWitnesses 3).length =
      3 :=
  explicitFamilyConstitutedLocalWitnesses_length 3

theorem variablesExact3 :
    (explicitFamilyConstitutedLocalWitnesses 3).map
        (fun entry => entry.var) =
      (explicitFamilyResourceTrajectory 3).trajectory.decisionVars :=
  explicitFamilyConstitutedLocalWitnesses_vars 3

theorem atomCount3 :
    ConstitutedLocalSchedule.atomCount
        (explicitFamilyConstitutedLocalWitnesses 3) =
      3 :=
  explicitFamilyConstitutedLocalAtomCount 3

theorem validationQueries3 :
    ConstitutedLocalSchedule.validationPrimitiveQueries
        (explicitFamilyConstitutedLocalWitnesses 3) =
      3 :=
  explicitFamilyConstitutedLocalValidationQueries 3

theorem executionQueries3 :
    ConstitutedLocalSchedule.executionPrimitiveQueries
        (explicitFamilyConstitutedLocalWitnesses 3) =
      3 :=
  explicitFamilyConstitutedLocalExecutionQueries 3

theorem executionComposition3 :
    ConstitutedLocalSchedule.executionCompositionCandidates
        (explicitFamilyConstitutedLocalWitnesses 3) =
      0 :=
  explicitFamilyConstitutedLocalExecutionCompositionCandidates 3

theorem validationSucceeds3 :
    ConstitutedLocalSchedule.ValidationSucceeds
      (explicitFamilyConstitutedLocalWitnesses 3) :=
  explicitFamilyConstitutedLocalValidationSucceeds 3

theorem localExecutions3 :
    ConstitutedLocalSchedule.HasLocalExecutions
      (explicitFamilyConstitutedLocalWitnesses 3) :=
  explicitFamilyConstitutedLocalHasLocalExecutions 3

theorem productionPolynomial :
    InputPolynomiallyBounded
      explicitFamilyInputBitSize
      (fun count =>
        ConstitutedLocalSchedule.atomCount
          (explicitFamilyConstitutedLocalWitnesses count)) :=
  explicitFamilyConstitutedLocalAtomCount_inputPolynomiallyBounded

theorem executionPolynomial :
    InputPolynomiallyBounded
      explicitFamilyInputBitSize
      (fun count =>
        ConstitutedLocalSchedule.executionPrimitiveQueries
          (explicitFamilyConstitutedLocalWitnesses count)) :=
  explicitFamilyConstitutedLocalExecution_inputPolynomiallyBounded

theorem executionCompositionPolynomial :
    InputPolynomiallyBounded
      explicitFamilyInputBitSize
      (fun count =>
        ConstitutedLocalSchedule.executionCompositionCandidates
          (explicitFamilyConstitutedLocalWitnesses count)) :=
  explicitFamilyConstitutedLocalExecutionComposition_inputPolynomiallyBounded

theorem validationPolynomial :
    InputPolynomiallyBounded
      explicitFamilyInputBitSize
      (fun count =>
        ConstitutedLocalSchedule.validationPrimitiveQueries
          (explicitFamilyConstitutedLocalWitnesses count)) :=
  explicitFamilyConstitutedLocalValidation_inputPolynomiallyBounded

end ConstitutiveSearch.Tests.SATTrajectoryConstitutedLocalScheduleRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATTrajectoryConstitutedLocalScheduleRegression.witnessCount3
#print axioms ConstitutiveSearch.Tests.SATTrajectoryConstitutedLocalScheduleRegression.variablesExact3
#print axioms ConstitutiveSearch.Tests.SATTrajectoryConstitutedLocalScheduleRegression.atomCount3
#print axioms ConstitutiveSearch.Tests.SATTrajectoryConstitutedLocalScheduleRegression.validationQueries3
#print axioms ConstitutiveSearch.Tests.SATTrajectoryConstitutedLocalScheduleRegression.executionQueries3
#print axioms ConstitutiveSearch.Tests.SATTrajectoryConstitutedLocalScheduleRegression.executionComposition3
#print axioms ConstitutiveSearch.Tests.SATTrajectoryConstitutedLocalScheduleRegression.validationSucceeds3
#print axioms ConstitutiveSearch.Tests.SATTrajectoryConstitutedLocalScheduleRegression.localExecutions3
#print axioms ConstitutiveSearch.Tests.SATTrajectoryConstitutedLocalScheduleRegression.productionPolynomial
#print axioms ConstitutiveSearch.Tests.SATTrajectoryConstitutedLocalScheduleRegression.executionPolynomial
#print axioms ConstitutiveSearch.Tests.SATTrajectoryConstitutedLocalScheduleRegression.executionCompositionPolynomial
#print axioms ConstitutiveSearch.Tests.SATTrajectoryConstitutedLocalScheduleRegression.validationPolynomial
/- AXIOM_AUDIT_END -/
