import ConstitutiveSearch.LocalSearchableCodeExecution

namespace ConstitutiveSearch.Tests.LocalSearchableCodeExecutionRegression

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

def demoCode :
    TransportClosure DemoGenerator 0 2 :=
  .compose
    (.atom DemoGenerator.first)
    (.atom DemoGenerator.second)

theorem demoSearchable :
    demoCode.SearchableBy demoPrimitive := by
  change
    some DemoGenerator.first ≠ none ∧
      some DemoGenerator.second ≠ none
  constructor
  · intro impossible
    cases impossible
  · intro impossible
    cases impossible

theorem demoLocalExecution :
    TransportCode.LocalSequentialExecution
      demoPrimitive
      demoCode :=
  TransportCode.localSequentialExecution_of_searchable
    demoPrimitive
    demoCode
    demoSearchable

theorem demoGlobalNeedAndLocal :
    TransportCode.GlobalNeedWithLocalExecution
      demoPrimitive
      demoCode := by
  apply
    TransportCode.directMiss_searchableCode_hasLocalExecution
      demoPrimitive
      (by rfl)
      demoCode
      demoSearchable
  change 2 ≤ 2
  exact Nat.le_refl 2

end ConstitutiveSearch.Tests.LocalSearchableCodeExecutionRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.LocalSearchableCodeExecutionRegression.demoCode
#print axioms ConstitutiveSearch.Tests.LocalSearchableCodeExecutionRegression.demoSearchable
#print axioms ConstitutiveSearch.Tests.LocalSearchableCodeExecutionRegression.demoLocalExecution
#print axioms ConstitutiveSearch.Tests.LocalSearchableCodeExecutionRegression.demoGlobalNeedAndLocal
/- AXIOM_AUDIT_END -/
