import ConstitutiveSearch.ConstitutiveComplexityInputPolynomial

namespace ConstitutiveSearch.Tests.ConstitutiveComplexityInputPolynomialRegression

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

def constantPhase
    (n : Nat) :
    ConstitutiveComplexityProfile :=
  { inputBits := n
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

theorem variableInputBounded :
    ConstitutiveProfileFamilyInputPolynomiallyBounded
      variableProfile :=
  { depth :=
      InputPolynomiallyBounded.self
        (fun n => n)
    width :=
      InputPolynomiallyBounded.self
        (fun n => n)
    syntaxUnits :=
      InputPolynomiallyBounded.self
        (fun n => n)
    frontierSlots :=
      InputPolynomiallyBounded.self
        (fun n => n)
    provenance :=
      InputPolynomiallyBounded.self
        (fun n => n)
    certificates :=
      InputPolynomiallyBounded.self
        (fun n => n)
    relationFind :=
      InputPolynomiallyBounded.self
        (fun n => n)
    closurePrimitive :=
      InputPolynomiallyBounded.self
        (fun n => n)
    closureCandidates :=
      InputPolynomiallyBounded.self
        (fun n => n)
    terminal :=
      InputPolynomiallyBounded.self
        (fun n => n)
    representationCharge :=
      InputPolynomiallyBounded.self
        (fun n => n) }

theorem constantInputBounded :
    ConstitutiveProfileFamilyInputPolynomiallyBounded
      constantPhase :=
  { depth :=
      InputPolynomiallyBounded.constant
        (fun n => n)
        1
    width :=
      InputPolynomiallyBounded.constant
        (fun n => n)
        1
    syntaxUnits :=
      InputPolynomiallyBounded.constant
        (fun n => n)
        1
    frontierSlots :=
      InputPolynomiallyBounded.constant
        (fun n => n)
        1
    provenance :=
      InputPolynomiallyBounded.constant
        (fun n => n)
        1
    certificates :=
      InputPolynomiallyBounded.constant
        (fun n => n)
        1
    relationFind :=
      InputPolynomiallyBounded.constant
        (fun n => n)
        1
    closurePrimitive :=
      InputPolynomiallyBounded.constant
        (fun n => n)
        1
    closureCandidates :=
      InputPolynomiallyBounded.constant
        (fun n => n)
        1
    terminal :=
      InputPolynomiallyBounded.constant
        (fun n => n)
        1
    representationCharge :=
      InputPolynomiallyBounded.constant
        (fun n => n)
        1 }

theorem composedInputBounded :
    ConstitutiveProfileFamilyInputPolynomiallyBounded
      (fun n =>
        ConstitutiveComplexityProfile.compose
          (variableProfile n)
          (constantPhase n)) :=
  ConstitutiveProfileFamilyInputPolynomiallyBounded.compose
    variableInputBounded
    constantInputBounded

end ConstitutiveSearch.Tests.ConstitutiveComplexityInputPolynomialRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.ConstitutiveComplexityInputPolynomialRegression.variableInputBounded
#print axioms ConstitutiveSearch.Tests.ConstitutiveComplexityInputPolynomialRegression.constantInputBounded
#print axioms ConstitutiveSearch.Tests.ConstitutiveComplexityInputPolynomialRegression.composedInputBounded
/- AXIOM_AUDIT_END -/
