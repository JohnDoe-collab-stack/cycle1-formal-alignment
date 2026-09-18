import ConstitutiveSearch.ConstitutiveComplexityComposition

namespace ConstitutiveSearch.Tests.ConstitutiveComplexityCompositionRegression

open ConstitutiveSearch

def first : ConstitutiveComplexityProfile :=
  { inputBits := 5
    depth := 3
    maxFrontierWidth := 2
    events :=
      { syntaxUnits := 4
        frontierSlots := 2
        provenanceUnits := 1
        certificateAtoms := 1
        relationFindCalls := 2
        closurePrimitiveQueries := 0
        closureCompositionCandidates := 0
        terminalChecks := 1 }
    representationCharge := 20 }

def second : ConstitutiveComplexityProfile :=
  { inputBits := 5
    depth := 2
    maxFrontierWidth := 3
    events :=
      { syntaxUnits := 0
        frontierSlots := 2
        provenanceUnits := 0
        certificateAtoms := 2
        relationFindCalls := 0
        closurePrimitiveQueries := 3
        closureCompositionCandidates := 1
        terminalChecks := 0 }
    representationCharge := 12 }

theorem first_bounded :
    first.BoundedBy
      (ConstitutiveComplexityProfile.compose
        first
        second) :=
  ConstitutiveComplexityProfile.left_boundedBy_compose
    first
    second

theorem second_bounded :
    second.BoundedBy
      (ConstitutiveComplexityProfile.compose
        first
        second) :=
  ConstitutiveComplexityProfile.right_boundedBy_compose
    first
    second

theorem composed_depth :
    (ConstitutiveComplexityProfile.compose
      first
      second).depth = 5 := by
  rfl

theorem composed_width :
    (ConstitutiveComplexityProfile.compose
      first
      second).maxFrontierWidth = 3 := by
  rfl

theorem composed_charge :
    (ConstitutiveComplexityProfile.compose
      first
      second).representationCharge = 32 := by
  rfl

end ConstitutiveSearch.Tests.ConstitutiveComplexityCompositionRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.ConstitutiveComplexityCompositionRegression.first_bounded
#print axioms ConstitutiveSearch.Tests.ConstitutiveComplexityCompositionRegression.second_bounded
#print axioms ConstitutiveSearch.Tests.ConstitutiveComplexityCompositionRegression.composed_depth
#print axioms ConstitutiveSearch.Tests.ConstitutiveComplexityCompositionRegression.composed_width
#print axioms ConstitutiveSearch.Tests.ConstitutiveComplexityCompositionRegression.composed_charge
/- AXIOM_AUDIT_END -/
