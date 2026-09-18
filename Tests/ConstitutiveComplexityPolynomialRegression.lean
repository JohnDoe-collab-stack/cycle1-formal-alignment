import ConstitutiveSearch.ConstitutiveComplexityPolynomial

namespace ConstitutiveSearch.Tests.ConstitutiveComplexityPolynomialRegression

open ConstitutiveSearch

def variableProfile
    (n : Nat) :
    ConstitutiveComplexityProfile :=
  { inputBits := n
    depth := n
    maxFrontierWidth := n
    events :=
      { syntaxUnits := n
        frontierSlots := n
        provenanceUnits := n
        certificateAtoms := n
        relationFindCalls := n
        closurePrimitiveQueries := n
        closureCompositionCandidates := n
        terminalChecks := n }
    representationCharge := n }

def constantProfile
    (_n : Nat) :
    ConstitutiveComplexityProfile :=
  { inputBits := 1
    depth := 1
    maxFrontierWidth := 1
    events :=
      { syntaxUnits := 1
        frontierSlots := 1
        provenanceUnits := 1
        certificateAtoms := 1
        relationFindCalls := 1
        closurePrimitiveQueries := 1
        closureCompositionCandidates := 1
        terminalChecks := 1 }
    representationCharge := 1 }

theorem variableBounded :
    ConstitutiveProfileFamilyPolynomiallyBounded
      variableProfile :=
  { inputBits := PolynomiallyBounded.input
    depth := PolynomiallyBounded.input
    width := PolynomiallyBounded.input
    syntaxUnits := PolynomiallyBounded.input
    frontierSlots := PolynomiallyBounded.input
    provenance := PolynomiallyBounded.input
    certificates := PolynomiallyBounded.input
    relationFind := PolynomiallyBounded.input
    closurePrimitive := PolynomiallyBounded.input
    closureCandidates := PolynomiallyBounded.input
    terminal := PolynomiallyBounded.input
    representationCharge := PolynomiallyBounded.input }

theorem constantBounded :
    ConstitutiveProfileFamilyPolynomiallyBounded
      constantProfile :=
  { inputBits := PolynomiallyBounded.constant 1
    depth := PolynomiallyBounded.constant 1
    width := PolynomiallyBounded.constant 1
    syntaxUnits := PolynomiallyBounded.constant 1
    frontierSlots := PolynomiallyBounded.constant 1
    provenance := PolynomiallyBounded.constant 1
    certificates := PolynomiallyBounded.constant 1
    relationFind := PolynomiallyBounded.constant 1
    closurePrimitive := PolynomiallyBounded.constant 1
    closureCandidates := PolynomiallyBounded.constant 1
    terminal := PolynomiallyBounded.constant 1
    representationCharge := PolynomiallyBounded.constant 1 }

theorem composedBounded :
    ConstitutiveProfileFamilyPolynomiallyBounded
      (fun n =>
        ConstitutiveComplexityProfile.compose
          (variableProfile n)
          (constantProfile n)) :=
  ConstitutiveProfileFamilyPolynomiallyBounded.compose
    variableBounded
    constantBounded

end ConstitutiveSearch.Tests.ConstitutiveComplexityPolynomialRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.ConstitutiveComplexityPolynomialRegression.variableBounded
#print axioms ConstitutiveSearch.Tests.ConstitutiveComplexityPolynomialRegression.constantBounded
#print axioms ConstitutiveSearch.Tests.ConstitutiveComplexityPolynomialRegression.composedBounded
/- AXIOM_AUDIT_END -/
