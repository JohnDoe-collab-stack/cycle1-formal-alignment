import ConstitutiveSearch.SAT.ConstitutiveProjectionSeparators

namespace ConstitutiveSearch.Tests.SATConstitutiveProjectionSeparatorsRegression

open ConstitutiveSearch
open SAT

abbrev c0p : Clause :=
  [Literal.positive 0, Literal.positive 2]

abbrev c0n : Clause :=
  [Literal.negative 0, Literal.positive 2]

abbrev formula : Cnf :=
  [c0p, c0n]

abbrev root :
    GeneratedStructuralBranchContext formula :=
  GeneratedStructuralBranchContext.root formula

theorem rootFresh :
    StructuralDecisionsAvoid
      0
      root.context.decisions :=
  True.intro

def anchor :
    GeneratedSplitAnchor formula :=
  { parent := root
    var := 0
    fresh := rootFresh }

theorem symmetric :
    FlipSymmetricAt
      root.context.formula
      0 := by
  change
    FlipSymmetricAt
      formula
      0
  exact
    symmetricBlockFamily_flipSymmetric
      (var := 0)
      (anchor := 2)
      (background := [])
      (by decide)
      True.intro

theorem relationLoss :
    ¬
      PredicateFactorsThrough
        forgetSplitConstitution
        (SplitRelationReconstructible
          anchor) :=
  splitRelationReconstructibility_not_factor_through_frontier
    anchor
    symmetric

theorem endpointCostLoss3 :
    ¬
      ValueFactorsThrough
        (composedEndpointProjection
          3)
        (composedCompositionCandidateObservation
          3) :=
  composedExecutionCost_not_factor_through_endpoints
    3

theorem closed :
    ConstitutiveProjectionLossClosed :=
  constitutiveProjectionLossClosed

end ConstitutiveSearch.Tests.SATConstitutiveProjectionSeparatorsRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATConstitutiveProjectionSeparatorsRegression.relationLoss
#print axioms ConstitutiveSearch.Tests.SATConstitutiveProjectionSeparatorsRegression.endpointCostLoss3
#print axioms ConstitutiveSearch.Tests.SATConstitutiveProjectionSeparatorsRegression.closed
/- AXIOM_AUDIT_END -/
