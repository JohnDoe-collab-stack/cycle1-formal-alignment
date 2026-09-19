import ConstitutiveSearch.ClosureSearchSequentialPrimitivePath

namespace ConstitutiveSearch.Tests.ClosureSearchSequentialPrimitivePathRegression

open ConstitutiveSearch

abbrev DemoGenerator
    (_source _target : Nat) : Type :=
  Unit

def demoPrimitive :
    RelationSearch DemoGenerator :=
  { find := fun _source _target =>
      some () }

theorem demoHit
    (source target : Nat) :
    demoPrimitive.find source target ≠ none := by
  intro impossible
  cases impossible

def demoPath :
    PrimitiveHitPath
      demoPrimitive
      0
      2
      2 :=
  .step
    0
    1
    (demoHit 0 1)
    (.step
      1
      2
      (demoHit 1 2)
      (.done 2))

theorem demoPrimitiveQueries :
    (demoPath.sequentialStats
      [10, 20, 30, 40]
      10).primitiveQueries =
      2 :=
  demoPath.sequentialStats_primitiveQueries
    [10, 20, 30, 40]
    10
    (by decide)

theorem demoCompositionCandidates :
    (demoPath.sequentialStats
      [10, 20, 30, 40]
      10).compositionCandidates =
      0 :=
  demoPath.sequentialStats_compositionCandidates
    [10, 20, 30, 40]
    10
    (by decide)

end ConstitutiveSearch.Tests.ClosureSearchSequentialPrimitivePathRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.ClosureSearchSequentialPrimitivePathRegression.demoPrimitive
#print axioms ConstitutiveSearch.Tests.ClosureSearchSequentialPrimitivePathRegression.demoPath
#print axioms ConstitutiveSearch.Tests.ClosureSearchSequentialPrimitivePathRegression.demoPrimitiveQueries
#print axioms ConstitutiveSearch.Tests.ClosureSearchSequentialPrimitivePathRegression.demoCompositionCandidates
/- AXIOM_AUDIT_END -/
