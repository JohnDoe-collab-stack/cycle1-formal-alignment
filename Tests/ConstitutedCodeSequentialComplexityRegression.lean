import ConstitutiveSearch.ConstitutedCodeSequentialComplexity

namespace ConstitutiveSearch.Tests.ConstitutedCodeSequentialComplexityRegression

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
  · change demoPrimitive.find 0 1 ≠ none
    simp [demoPrimitive]
  · change demoPrimitive.find 1 2 ≠ none
    simp [demoPrimitive]

def demoInputBits
    (n : Nat) : Nat :=
  n + 1

theorem demoCodeSizeBounded :
    InputPolynomiallyBounded
      demoInputBits
      (fun _n =>
        demoCode.size) :=
  ⟨CostPolynomial.constant 2,
    fun _n => by
      change 2 ≤ 2
      exact Nat.le_refl 2⟩

theorem demoFamilySequential :
    ∃ envelope : CostPolynomial,
      ∀ n : Nat,
        ∃ path :
            PrimitiveHitPath
              demoPrimitive
              0
              2,
          path.length = demoCode.size ∧
            (path.sequentialStats [1] 1).primitiveQueries =
              demoCode.size ∧
            (path.sequentialStats [1] 1).primitiveQueries ≤
              envelope.eval (demoInputBits n) ∧
            (path.sequentialStats [1] 1).compositionCandidates =
              0 :=
  searchableCodeFamily_inputPolynomialSequentialExecution
    (fun _n =>
      demoPrimitive)
    (fun _n =>
      [1])
    (fun _n =>
      1)
    (fun _n =>
      by decide)
    (fun _n =>
      0)
    (fun _n =>
      2)
    (fun _n =>
      demoCode)
    (fun _n =>
      demoSearchable)
    demoCodeSizeBounded

end ConstitutiveSearch.Tests.ConstitutedCodeSequentialComplexityRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.ConstitutedCodeSequentialComplexityRegression.demoCodeSizeBounded
#print axioms ConstitutiveSearch.Tests.ConstitutedCodeSequentialComplexityRegression.demoFamilySequential
/- AXIOM_AUDIT_END -/
