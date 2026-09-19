import ConstitutiveSearch.ConstitutedPrimitivePath

namespace ConstitutiveSearch.Tests.ConstitutedPrimitivePathRegression

open ConstitutiveSearch

inductive DemoGenerator : Nat → Nat → Type
  | first : DemoGenerator 0 1
  | second : DemoGenerator 1 2

def demoPrimitive :
    RelationSearch DemoGenerator :=
  { find := fun source target =>
      match source, target with
      | 0, 1 => some DemoGenerator.first
      | 1, 2 => some DemoGenerator.second
      | _, _ => none }

def demoPath :
    ConstitutedPrimitivePath
      DemoGenerator
      0
      2 :=
  .step
    DemoGenerator.first
    (.atom DemoGenerator.second)

theorem demoLength :
    demoPath.length = 2 := by
  rfl

theorem demoCodeSize :
    demoPath.toTransportCode.size = 2 := by
  rw [demoPath.toTransportCode_size]
  exact demoLength

theorem demoSearchable :
    demoPath.SearchableBy demoPrimitive := by
  change
    demoPrimitive.find 0 1 ≠ none ∧
      demoPrimitive.find 1 2 ≠ none
  constructor <;> simp [demoPrimitive]

theorem demoValidationQueries :
    (validateSearchableCode
      demoPrimitive
      demoPath.toTransportCode).primitiveQueries = 2 := by
  calc
    (validateSearchableCode
      demoPrimitive
      demoPath.toTransportCode).primitiveQueries
        =
      demoPath.length :=
        demoPath.validation_primitiveQueries
          demoPrimitive
    _ = 2 :=
      demoLength

theorem demoEndToEnd :
    ConstitutedPrimitivePath.EndToEndLocalExecution
      demoPrimitive
      demoPath :=
  demoPath.endToEndLocalExecution_of_searchable
    demoPrimitive
    demoSearchable

end ConstitutiveSearch.Tests.ConstitutedPrimitivePathRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.ConstitutedPrimitivePathRegression.demoPath
#print axioms ConstitutiveSearch.Tests.ConstitutedPrimitivePathRegression.demoLength
#print axioms ConstitutiveSearch.Tests.ConstitutedPrimitivePathRegression.demoCodeSize
#print axioms ConstitutiveSearch.Tests.ConstitutedPrimitivePathRegression.demoSearchable
#print axioms ConstitutiveSearch.Tests.ConstitutedPrimitivePathRegression.demoValidationQueries
#print axioms ConstitutiveSearch.Tests.ConstitutedPrimitivePathRegression.demoEndToEnd
/- AXIOM_AUDIT_END -/
