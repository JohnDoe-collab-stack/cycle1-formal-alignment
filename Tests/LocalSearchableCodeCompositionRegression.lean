import ConstitutiveSearch.LocalSearchableCodeComposition

namespace ConstitutiveSearch.Tests.LocalSearchableCodeCompositionRegression

open ConstitutiveSearch

inductive DemoGenerator : Nat → Nat → Nat → Type
  | first (n : Nat) : DemoGenerator n 0 1
  | second (n : Nat) : DemoGenerator n 1 2

abbrev DemoState (_n : Nat) : Type := Nat

def demoPrimitive
    (n : Nat) :
    RelationSearch (DemoGenerator n) :=
  { find := fun source target =>
      match source, target with
      | 0, 1 => some (DemoGenerator.first n)
      | 1, 2 => some (DemoGenerator.second n)
      | _, _ => none }

def demoFirst
    (n : Nat) :
    TransportClosure
      (DemoGenerator n)
      0
      1 :=
  .atom (DemoGenerator.first n)

def demoSecond
    (n : Nat) :
    TransportClosure
      (DemoGenerator n)
      1
      2 :=
  .atom (DemoGenerator.second n)

theorem demoFirstSearchable
    (n : Nat) :
    (demoFirst n).SearchableBy
      (demoPrimitive n) := by
  change some (DemoGenerator.first n) ≠ none
  intro impossible
  cases impossible

theorem demoSecondSearchable
    (n : Nat) :
    (demoSecond n).SearchableBy
      (demoPrimitive n) := by
  change some (DemoGenerator.second n) ≠ none
  intro impossible
  cases impossible

theorem demoComposedSize
    (n : Nat) :
    (composeSearchableCodeFamily
      demoFirst
      demoSecond
      n).size = 2 := by
  rw [composeSearchableCodeFamily_size]
  rfl

end ConstitutiveSearch.Tests.LocalSearchableCodeCompositionRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.LocalSearchableCodeCompositionRegression.demoFirstSearchable
#print axioms ConstitutiveSearch.Tests.LocalSearchableCodeCompositionRegression.demoSecondSearchable
#print axioms ConstitutiveSearch.Tests.LocalSearchableCodeCompositionRegression.demoComposedSize
/- AXIOM_AUDIT_END -/
