import ConstitutiveSearch.WitnessCompleteCompositionCharacterization

namespace ConstitutiveSearch.Tests.WitnessCompleteCompositionCharacterizationRegression

open ConstitutiveSearch

inductive DemoGenerator : Nat → Nat → Type
  | first : DemoGenerator 0 1
  | second : DemoGenerator 1 2

def demoPrimitive :
    RelationSearch DemoGenerator :=
  { find := fun source target =>
      match source, target with
      | 0, 1 =>
          some DemoGenerator.first
      | 1, 2 =>
          some DemoGenerator.second
      | _, _ =>
          none }

theorem demoComplete :
    demoPrimitive.WitnessComplete := by
  intro source target witness
  cases witness with
  | first =>
      simp [demoPrimitive]
  | second =>
      simp [demoPrimitive]

def demoCode :
    TransportClosure
      DemoGenerator
      0
      2 :=
  .compose
    (.atom DemoGenerator.first)
    (.atom DemoGenerator.second)

theorem demoDirectMiss :
    demoPrimitive.find 0 2 = none := by
  rfl

theorem demoCodeSize :
    demoCode.size = 2 := by
  rfl

theorem demoCompositionRequired :
    PrimitiveHitPath.GlobalCompositionRequired
      demoPrimitive
      0
      2 := by
  apply
    (PrimitiveHitPath.globalCompositionRequired_iff_code_of_witnessComplete
      demoPrimitive
      demoComplete
      0
      2).2
  exact
    ⟨demoDirectMiss,
      ⟨demoCode, by
        rw [demoCodeSize]
        exact Nat.le_refl 2⟩⟩

end ConstitutiveSearch.Tests.WitnessCompleteCompositionCharacterizationRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.WitnessCompleteCompositionCharacterizationRegression.demoComplete
#print axioms ConstitutiveSearch.Tests.WitnessCompleteCompositionCharacterizationRegression.demoCode
#print axioms ConstitutiveSearch.Tests.WitnessCompleteCompositionCharacterizationRegression.demoCompositionRequired
/- AXIOM_AUDIT_END -/
