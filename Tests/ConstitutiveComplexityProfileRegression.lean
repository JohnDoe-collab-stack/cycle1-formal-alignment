import ConstitutiveSearch.ConstitutiveComplexityProfile

namespace ConstitutiveSearch.Tests.ConstitutiveComplexityProfileRegression

def events : ComplexityCounts :=
  { syntaxUnits := 4
    frontierSlots := 3
    provenanceUnits := 2
    certificateAtoms := 1
    relationFindCalls := 2
    closurePrimitiveQueries := 0
    closureCompositionCandidates := 0
    terminalChecks := 1 }

def profile : ConstitutiveComplexityProfile :=
  { inputBits := 32
    depth := 2
    maxFrontierWidth := 2
    events := events
    representationCharge := 64 }

theorem profileReflexive :
    profile.BoundedBy profile :=
  ConstitutiveComplexityProfile.BoundedBy.refl
    profile

theorem zeroEventsLeft :
    ComplexityCounts.add
        ComplexityCounts.zero
        events =
      events :=
  ComplexityCounts.zero_add events

theorem zeroEventsRight :
    ComplexityCounts.add
        events
        ComplexityCounts.zero =
      events :=
  ComplexityCounts.add_zero events

end ConstitutiveSearch.Tests.ConstitutiveComplexityProfileRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.ConstitutiveComplexityProfileRegression.profileReflexive
#print axioms ConstitutiveSearch.Tests.ConstitutiveComplexityProfileRegression.zeroEventsLeft
#print axioms ConstitutiveSearch.Tests.ConstitutiveComplexityProfileRegression.zeroEventsRight
/- AXIOM_AUDIT_END -/
