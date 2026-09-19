import ConstitutiveSearch.SearchableTransportCode

namespace ConstitutiveSearch.Tests.SearchableTransportCodeRegression

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
    TransportClosure
      DemoGenerator
      0
      2 :=
  .compose
    (.atom DemoGenerator.first)
    (.atom DemoGenerator.second)

theorem demoSearchable :
    demoCode.SearchableBy
      demoPrimitive := by
  constructor
  · change
      demoPrimitive.find 0 1 ≠ none
    simp [demoPrimitive]
  · change
      demoPrimitive.find 1 2 ≠ none
    simp [demoPrimitive]

theorem demoRequired :
    PrimitiveHitPath.GlobalCompositionRequired
      demoPrimitive
      0
      2 := by
  apply
    (PrimitiveHitPath.globalCompositionRequired_iff_searchableCode
      demoPrimitive
      0
      2).2
  exact
    ⟨rfl,
      ⟨demoCode,
        demoSearchable,
        by decide⟩⟩

theorem demoSequential :
    ∃ path :
        PrimitiveHitPath
          demoPrimitive
          0
          2,
      path.length = demoCode.size ∧
        (path.sequentialStats [1] 1).primitiveQueries =
          demoCode.size ∧
        (path.sequentialStats [1] 1).compositionCandidates =
          0 :=
  demoCode.hasSequentialExecution_of_searchable
    demoPrimitive
    [1]
    1
    (by decide)
    demoSearchable

end ConstitutiveSearch.Tests.SearchableTransportCodeRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SearchableTransportCodeRegression.demoSearchable
#print axioms ConstitutiveSearch.Tests.SearchableTransportCodeRegression.demoRequired
#print axioms ConstitutiveSearch.Tests.SearchableTransportCodeRegression.demoSequential
/- AXIOM_AUDIT_END -/
