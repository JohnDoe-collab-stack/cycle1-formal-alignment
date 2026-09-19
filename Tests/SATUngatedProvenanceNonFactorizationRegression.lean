import ConstitutiveSearch.SAT.UngatedProvenanceNonFactorization

namespace ConstitutiveSearch.Tests.SATUngatedProvenanceNonFactorizationRegression

open ConstitutiveSearch
open SAT

theorem sameProjection :
    eraseGeneratedProvenance
        UngatedProvenanceCase.reconstructible =
      eraseGeneratedProvenance
        UngatedProvenanceCase.provenanceMismatch :=
  ungatedProjection_same

theorem positiveFound :
    ActualUngatedRelationReconstructible
      UngatedProvenanceCase.reconstructible :=
  ungatedPositive_reconstructible

theorem negativeMissing :
    ¬
      ActualUngatedRelationReconstructible
        UngatedProvenanceCase.provenanceMismatch :=
  ungatedNegative_not_reconstructible

theorem relationDoesNotFactor :
    ¬
      PredicateFactorsThrough
        eraseGeneratedProvenance
        ActualUngatedRelationReconstructible :=
  actualUngatedRelationReconstructibility_not_factor_through_residuals

theorem positiveWidth :
    (ungatedCaseReduction
      UngatedProvenanceCase.reconstructible).width =
      1 :=
  ungatedPositive_width

theorem negativeWidth :
    (ungatedCaseReduction
      UngatedProvenanceCase.provenanceMismatch).width =
      2 :=
  ungatedNegative_width

theorem widthDoesNotFactor :
    ¬
      ValueFactorsThrough
        eraseGeneratedProvenance
        ungatedWidthObservation :=
  ungatedWidth_not_factor_through_residuals

theorem closed :
    UngatedConstitutiveProjectionLoss :=
  ungatedConstitutiveProjectionLoss

end ConstitutiveSearch.Tests.SATUngatedProvenanceNonFactorizationRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATUngatedProvenanceNonFactorizationRegression.sameProjection
#print axioms ConstitutiveSearch.Tests.SATUngatedProvenanceNonFactorizationRegression.positiveFound
#print axioms ConstitutiveSearch.Tests.SATUngatedProvenanceNonFactorizationRegression.negativeMissing
#print axioms ConstitutiveSearch.Tests.SATUngatedProvenanceNonFactorizationRegression.relationDoesNotFactor
#print axioms ConstitutiveSearch.Tests.SATUngatedProvenanceNonFactorizationRegression.positiveWidth
#print axioms ConstitutiveSearch.Tests.SATUngatedProvenanceNonFactorizationRegression.negativeWidth
#print axioms ConstitutiveSearch.Tests.SATUngatedProvenanceNonFactorizationRegression.widthDoesNotFactor
#print axioms ConstitutiveSearch.Tests.SATUngatedProvenanceNonFactorizationRegression.closed
/- AXIOM_AUDIT_END -/
