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


def profile
    (n : Nat) :
    ConstitutiveComplexityProfile :=
  { inputBits := inputBits n
    depth := n
    maxFrontierWidth := n
    events := counts n
    representationCharge :=
      chargedCost
        (counts n)
        (representation n) }

theorem profileBounded :
    ConstitutiveProfileFamilyInputPolynomiallyBounded
      profile :=
  { depth :=
      InputPolynomiallyBounded.self inputBits
    width :=
      InputPolynomiallyBounded.self inputBits
    syntaxUnits :=
      countsBounded.syntaxUnits
    frontierSlots :=
      countsBounded.frontierSlots
    provenance :=
      countsBounded.provenanceUnits
    certificates :=
      countsBounded.certificateAtoms
    relationFind :=
      countsBounded.relationFindCalls
    closurePrimitive :=
      countsBounded.closurePrimitiveQueries
    closureCandidates :=
      countsBounded.closureCompositionCandidates
    terminal :=
      countsBounded.terminalChecks
    representationCharge := by
      change
        InputPolynomiallyBounded
          inputBits
          (fun n =>
            chargedCost
              (counts n)
              (representation n))
      exact
        chargedCost_inputPolynomiallyBounded
          countsBounded
          representationBounded }

def machine
    (n : Nat) :
    MachineCostModel :=
  { atomic :=
      affineAtomicEnvelope
        (representation n)
        2
        1 }

theorem bridge
    (n : Nat) :
    RepresentationMachineBridge
      (representation n)
      (machine n)
      2
      1 := by
  constructor
  exact
    atomicCostPointwiseLe_refl
      (affineAtomicEnvelope
        (representation n)
        2
        1)

theorem profileMachineBounded :
    InputPolynomiallyBounded
      (fun n =>
        (profile n).inputBits)
      (fun n =>
        machineChargedCost
          (profile n).events
          (machine n)) :=
  constitutiveProfileMachineCost_inputPolynomiallyBounded
    profileBounded
    representationBounded
    2
    1
    bridge

end ConstitutiveSearch.Tests.MachineCostPolynomialRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.MachineCostPolynomialRegression.countsBounded
#print axioms ConstitutiveSearch.Tests.MachineCostPolynomialRegression.representationBounded
#print axioms ConstitutiveSearch.Tests.MachineCostPolynomialRegression.calibratedBounded
#print axioms ConstitutiveSearch.Tests.MachineCostPolynomialRegression.profileBounded
#print axioms ConstitutiveSearch.Tests.MachineCostPolynomialRegression.bridge
#print axioms ConstitutiveSearch.Tests.MachineCostPolynomialRegression.profileMachineBounded
/- AXIOM_AUDIT_END -/
