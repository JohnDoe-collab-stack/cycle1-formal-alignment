import ConstitutiveSearch.SAT.ParametricProvenanceNonFactorization

namespace ConstitutiveSearch.Tests.SATParametricProvenanceNonFactorizationRegression

open ConstitutiveSearch
open SAT

/-- Every indexed positive/negative pair has the same nonempty projection. -/
theorem sameAtEveryIndex
    (index : Nat) :
    eraseParametricProvenance (.reconstructible index) =
      eraseParametricProvenance (.provenanceMismatch index) :=
  parametricProjection_same index

/-- The strengthened family never falls back to the empty residual pair. -/
theorem residualsAreNonempty
    (index : Nat) :
    eraseParametricProvenance (.reconstructible index) ≠
      (([] : Cnf), ([] : Cnf)) :=
  parametricProjection_nonempty index

/-- The projection is not a constant map across the infinite family. -/
theorem projectionChanges
    (index : Nat) :
    eraseParametricProvenance (.reconstructible index) ≠
      eraseParametricProvenance (.reconstructible (index + 1)) :=
  parametricProjection_strict index

/-- The common ungated engine finds every positive sibling organization. -/
theorem everyPositiveFound
    (index : Nat) :
    ParametricRelationReconstructible (.reconstructible index) :=
  parametricPositive_reconstructible index

/-- The same engine rejects every mismatched provenance organization. -/
theorem everyNegativeMissing
    (index : Nat) :
    ¬ ParametricRelationReconstructible (.provenanceMismatch index) :=
  parametricNegative_not_reconstructible index

/-- Negative cases pass formula matching and fail specifically on provenance. -/
theorem negativeFormulaStillMatches
    (index : Nat) :
    (parametricNegativeTarget index).context.formula =
      Cnf.flipAt
        (parametricEngineVar index)
        (parametricNegativeSource index).context.formula :=
  parametricNegative_formula_matches_engine index

/-- Residual syntax alone cannot reconstruct the operational relation result. -/
theorem relationDoesNotFactor :
    ¬ PredicateFactorsThrough
        eraseParametricProvenance
        ParametricRelationReconstructible :=
  parametricRelationReconstructibility_not_factor_through_residuals

/-- Complete strengthened evidence package. -/
theorem closed :
    ParametricProvenanceProjectionLoss :=
  parametricProvenanceProjectionLoss

end ConstitutiveSearch.Tests.SATParametricProvenanceNonFactorizationRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATParametricProvenanceNonFactorizationRegression.sameAtEveryIndex
#print axioms ConstitutiveSearch.Tests.SATParametricProvenanceNonFactorizationRegression.residualsAreNonempty
#print axioms ConstitutiveSearch.Tests.SATParametricProvenanceNonFactorizationRegression.projectionChanges
#print axioms ConstitutiveSearch.Tests.SATParametricProvenanceNonFactorizationRegression.everyPositiveFound
#print axioms ConstitutiveSearch.Tests.SATParametricProvenanceNonFactorizationRegression.everyNegativeMissing
#print axioms ConstitutiveSearch.Tests.SATParametricProvenanceNonFactorizationRegression.negativeFormulaStillMatches
#print axioms ConstitutiveSearch.Tests.SATParametricProvenanceNonFactorizationRegression.relationDoesNotFactor
#print axioms ConstitutiveSearch.Tests.SATParametricProvenanceNonFactorizationRegression.closed
/- AXIOM_AUDIT_END -/
