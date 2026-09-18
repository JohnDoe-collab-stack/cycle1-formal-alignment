import ConstitutiveSearch.MachineCostPolynomial

namespace ConstitutiveSearch.Tests.MachineCostPolynomialRegression

open ConstitutiveSearch

def inputBits
    (n : Nat) : Nat := n

def counts
    (n : Nat) : ComplexityCounts :=
  { syntaxUnits := n
    frontierSlots := n
    provenanceUnits := n
    certificateAtoms := n
    relationFindCalls := n
    closurePrimitiveQueries := n
    closureCompositionCandidates := n
    terminalChecks := n }

def representation
    (n : Nat) : AtomicCosts :=
  { syntaxUnit := n
    frontierSlot := n
    provenanceUnit := n
    certificateAtom := n
    relationFindCall := n
    closurePrimitiveQuery := n
    closureCompositionCandidate := n
    terminalCheck := n }

theorem countsBounded :
    ComplexityCountsFamilyInputPolynomiallyBounded
      inputBits
      counts :=
  { syntaxUnits := InputPolynomiallyBounded.self inputBits
    frontierSlots := InputPolynomiallyBounded.self inputBits
    provenanceUnits := InputPolynomiallyBounded.self inputBits
    certificateAtoms := InputPolynomiallyBounded.self inputBits
    relationFindCalls := InputPolynomiallyBounded.self inputBits
    closurePrimitiveQueries := InputPolynomiallyBounded.self inputBits
    closureCompositionCandidates := InputPolynomiallyBounded.self inputBits
    terminalChecks := InputPolynomiallyBounded.self inputBits }

theorem representationBounded :
    AtomicCostsFamilyInputPolynomiallyBounded
      inputBits
      representation :=
  { syntaxUnit := InputPolynomiallyBounded.self inputBits
    frontierSlot := InputPolynomiallyBounded.self inputBits
    provenanceUnit := InputPolynomiallyBounded.self inputBits
    certificateAtom := InputPolynomiallyBounded.self inputBits
    relationFindCall := InputPolynomiallyBounded.self inputBits
    closurePrimitiveQuery := InputPolynomiallyBounded.self inputBits
    closureCompositionCandidate := InputPolynomiallyBounded.self inputBits
    terminalCheck := InputPolynomiallyBounded.self inputBits }

theorem calibratedBounded :
    InputPolynomiallyBounded
      inputBits
      (fun n =>
        representationCalibratedMachineBudget
          (counts n)
          (representation n)
          2
          1) :=
  representationCalibratedMachineBudget_inputPolynomiallyBounded
    countsBounded
    representationBounded
    2
    1

end ConstitutiveSearch.Tests.MachineCostPolynomialRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.MachineCostPolynomialRegression.countsBounded
#print axioms ConstitutiveSearch.Tests.MachineCostPolynomialRegression.representationBounded
#print axioms ConstitutiveSearch.Tests.MachineCostPolynomialRegression.calibratedBounded
/- AXIOM_AUDIT_END -/
