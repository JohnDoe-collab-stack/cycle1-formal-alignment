import ConstitutiveSearch.SearchableTransportCodeValidation

namespace ConstitutiveSearch.Tests.SearchableTransportCodeValidationRegression

open ConstitutiveSearch

inductive DemoGenerator : Nat → Nat → Type
  | first : DemoGenerator 0 1
  | second : DemoGenerator 1 2
  | missing : DemoGenerator 2 3

def demoPrimitive :
    RelationSearch DemoGenerator :=
  { find := fun source target =>
      match source, target with
      | 0, 1 => some DemoGenerator.first
      | 1, 2 => some DemoGenerator.second
      | _, _ => none }

def validCode :
    TransportClosure DemoGenerator 0 2 :=
  .compose
    (.atom DemoGenerator.first)
    (.atom DemoGenerator.second)

def invalidCode :
    TransportClosure DemoGenerator 2 3 :=
  .atom DemoGenerator.missing

theorem validQueries :
    (validateSearchableCode
      demoPrimitive
      validCode).primitiveQueries = 2 := by
  exact
    validateSearchableCode_primitiveQueries
      demoPrimitive
      validCode

theorem validSuccess :
    (validateSearchableCode
      demoPrimitive
      validCode).success = true := by
  apply
    validateSearchableCode_success_of_searchable
  change
    demoPrimitive.find 0 1 ≠ none ∧
      demoPrimitive.find 1 2 ≠ none
  constructor <;> simp [demoPrimitive]

theorem invalidFails :
    (validateSearchableCode
      demoPrimitive
      invalidCode).success = false := by
  rfl

end ConstitutiveSearch.Tests.SearchableTransportCodeValidationRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SearchableTransportCodeValidationRegression.validQueries
#print axioms ConstitutiveSearch.Tests.SearchableTransportCodeValidationRegression.validSuccess
#print axioms ConstitutiveSearch.Tests.SearchableTransportCodeValidationRegression.invalidFails
/- AXIOM_AUDIT_END -/
