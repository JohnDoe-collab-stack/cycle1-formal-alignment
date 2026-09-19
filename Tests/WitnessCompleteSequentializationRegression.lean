import ConstitutiveSearch.WitnessCompleteSequentialization

namespace ConstitutiveSearch.Tests.WitnessCompleteSequentializationRegression

open ConstitutiveSearch

abbrev DemoState := Nat

abbrev DemoGenerator
    (_source _target : DemoState) : Type :=
  Unit

def demoPrimitive :
    RelationSearch DemoGenerator :=
  { find := fun _source _target =>
      some () }

theorem demoComplete :
    demoPrimitive.WitnessComplete := by
  intro source target witness
  intro impossible
  cases impossible

def demoCode :
    TransportClosure
      DemoGenerator
      0
      2 :=
  TransportClosure.compose
    (Generator := DemoGenerator)
    (source := 0)
    (middle := 1)
    (target := 2)
    (TransportClosure.ofGenerator
      (Generator := DemoGenerator)
      (source := 0)
      (target := 1)
      ())
    (TransportClosure.ofGenerator
      (Generator := DemoGenerator)
      (source := 1)
      (target := 2)
      ())

theorem demoCodeSize :
    demoCode.size = 2 := by
  rfl

theorem demoSequential :
    ∃ path :
        PrimitiveHitPath
          demoPrimitive
          0
          2,
      path.length = demoCode.size ∧
        (path.sequentialStats
            [1]
            1).primitiveQueries =
          demoCode.size ∧
        (path.sequentialStats
            [1]
            1).compositionCandidates =
          0 :=
  demoCode.hasSequentialExecution_of_witnessComplete
    demoPrimitive
    demoComplete
    [1]
    1
    (by decide)

end ConstitutiveSearch.Tests.WitnessCompleteSequentializationRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.WitnessCompleteSequentializationRegression.demoComplete
#print axioms ConstitutiveSearch.Tests.WitnessCompleteSequentializationRegression.demoCode
#print axioms ConstitutiveSearch.Tests.WitnessCompleteSequentializationRegression.demoCodeSize
#print axioms ConstitutiveSearch.Tests.WitnessCompleteSequentializationRegression.demoSequential
/- AXIOM_AUDIT_END -/
