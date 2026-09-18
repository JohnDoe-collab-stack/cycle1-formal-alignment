import ConstitutiveSearch.ClosureSearchWidthControlled

namespace ConstitutiveSearch.Tests.ClosureSearchWidthControlledRegression

open ConstitutiveSearch

abbrev DemoState (_n : Nat) : Type :=
  Nat

abbrev DemoGenerator
    (n : Nat)
    (_source _target : DemoState n) : Type :=
  Unit

def demoPrimitive
    (n : Nat) :
    RelationSearch (DemoGenerator n) :=
  { find := fun _source _target => none }

def demoProfile
    (inputBits : Nat) :
    ConstitutiveComplexityProfile :=
  { inputBits := inputBits
    depth := 1
    maxFrontierWidth := 2
    events := ComplexityCounts.zero
    representationCharge := 0 }

def demoSchedule :
    WidthControlledClosureSchedule
      DemoState
      demoProfile :=
  { candidates := fun _ => [0, 1]
    fuel := fun _ => 2
    source := fun _ => 0
    target := fun _ => 1
    candidateLeWidth := by
      intro n
      change 2 ≤ 2
      exact Nat.le_refl 2
    fuelLeWidth := by
      intro n
      change 2 ≤ 2
      exact Nat.le_refl 2 }

def demoWidthBound :
    UniformProfileWidthBound
      demoProfile
      2 :=
  { widthLe := by
      intro n
      change 2 ≤ 2
      exact Nat.le_refl 2 }

theorem demoCandidateLengthPolynomial :
    InputPolynomiallyBounded
      (fun n =>
        (demoProfile n).inputBits)
      (fun n =>
        (demoSchedule.candidates n).length) :=
  demoSchedule.candidateLength_inputPolynomiallyBounded
    2
    demoWidthBound

theorem demoFuelBounded :
    ∀ n : Nat,
      demoSchedule.fuel n ≤ 2 :=
  demoSchedule.fuel_uniformlyBounded
    2
    demoWidthBound

theorem demoCountersPolynomial :
    WidthControlledClosureSchedule.InputPolynomialCounters
      demoPrimitive
      demoSchedule :=
  demoSchedule.inputPolynomialCounters_of_uniformWidth
    demoPrimitive
    2
    demoWidthBound

end ConstitutiveSearch.Tests.ClosureSearchWidthControlledRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.ClosureSearchWidthControlledRegression.demoSchedule
#print axioms ConstitutiveSearch.Tests.ClosureSearchWidthControlledRegression.demoWidthBound
#print axioms ConstitutiveSearch.Tests.ClosureSearchWidthControlledRegression.demoCandidateLengthPolynomial
#print axioms ConstitutiveSearch.Tests.ClosureSearchWidthControlledRegression.demoFuelBounded
#print axioms ConstitutiveSearch.Tests.ClosureSearchWidthControlledRegression.demoCountersPolynomial
/- AXIOM_AUDIT_END -/
