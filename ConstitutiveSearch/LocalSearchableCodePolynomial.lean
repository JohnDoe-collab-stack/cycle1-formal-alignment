import ConstitutiveSearch.LocalSearchableCodeExecution
import ConstitutiveSearch.ConstitutiveComplexityInputPolynomial

/-!
# Input-polynomial local execution of searchable code families

Candidate-free local execution reduces the control-flow cost of a constituted
searchable TransportCode to its number of primitive atoms:
* primitive-query budget = code.size;
* composition-candidate budget = 0.

Therefore a family of searchable constituted codes has input-polynomial local
execution whenever code size itself is input-polynomial.

This criterion is independent of any global ClosureSearch candidate list or
global closure fuel.
-/

namespace ConstitutiveSearch

universe uGenerator

/-- Primitive-query budget of the candidate-free local execution policy. -/
def localSearchableCodePrimitiveBudget
    {State : Nat → Type}
    {Generator :
      (n : Nat) →
        State n → State n → Type uGenerator}
    {source target :
      (n : Nat) →
        State n}
    (code :
      (n : Nat) →
        TransportCode
          (Generator n)
          (source n)
          (target n))
    (n : Nat) : Nat :=
  (code n).size

/-- Composition-candidate budget of the local policy is identically zero. -/
def localSearchableCodeCompositionBudget
    (_n : Nat) : Nat :=
  0

/--
Polynomial local-execution certificate for one family of constituted codes.
-/
structure LocalSearchableCodeFamilyInputPolynomiallyBounded
    {State : Nat → Type}
    {Generator :
      (n : Nat) →
        State n → State n → Type uGenerator}
    (primitive :
      (n : Nat) →
        RelationSearch (Generator n))
    {source target :
      (n : Nat) →
        State n}
    (code :
      (n : Nat) →
        TransportCode
          (Generator n)
          (source n)
          (target n))
    (inputBits : Nat → Nat) : Prop where
  localExecution :
    ∀ n : Nat,
      TransportCode.LocalSequentialExecution
        (primitive n)
        (code n)
  primitiveBudget :
    InputPolynomiallyBounded
      inputBits
      (localSearchableCodePrimitiveBudget
        code)
  compositionBudget :
    InputPolynomiallyBounded
      inputBits
      localSearchableCodeCompositionBudget

/--
Searchability of every code plus an input-polynomial bound on code size is
sufficient for polynomial candidate-free local execution.
-/
theorem localSearchableCodeFamily_inputPolynomiallyBounded
    {State : Nat → Type}
    {Generator :
      (n : Nat) →
        State n → State n → Type uGenerator}
    (primitive :
      (n : Nat) →
        RelationSearch (Generator n))
    {source target :
      (n : Nat) →
        State n}
    (code :
      (n : Nat) →
        TransportCode
          (Generator n)
          (source n)
          (target n))
    (inputBits : Nat → Nat)
    (searchable :
      ∀ n : Nat,
        (code n).SearchableBy
          (primitive n))
    (codeSizeBounded :
      InputPolynomiallyBounded
        inputBits
        (fun n =>
          (code n).size)) :
    LocalSearchableCodeFamilyInputPolynomiallyBounded
      primitive
      code
      inputBits := by
  exact
    { localExecution := fun n =>
        TransportCode.localSequentialExecution_of_searchable
          (primitive n)
          (code n)
          (searchable n)
      primitiveBudget := by
        change
          InputPolynomiallyBounded
            inputBits
            (fun n =>
              (code n).size)
        exact codeSizeBounded
      compositionBudget :=
        InputPolynomiallyBounded.constant
          inputBits
          0 }

/--
The local primitive budget is exactly the constituted code size.
-/
theorem localSearchableCodePrimitiveBudget_eq_size
    {State : Nat → Type}
    {Generator :
      (n : Nat) →
        State n → State n → Type uGenerator}
    {source target :
      (n : Nat) →
        State n}
    (code :
      (n : Nat) →
        TransportCode
          (Generator n)
          (source n)
          (target n))
    (n : Nat) :
    localSearchableCodePrimitiveBudget
        code
        n =
      (code n).size := by
  rfl

/-- The local composition-candidate budget is exactly zero. -/
theorem localSearchableCodeCompositionBudget_eq_zero
    (n : Nat) :
    localSearchableCodeCompositionBudget n =
      0 := by
  rfl

end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.localSearchableCodePrimitiveBudget
#print axioms ConstitutiveSearch.localSearchableCodeCompositionBudget
#print axioms ConstitutiveSearch.LocalSearchableCodeFamilyInputPolynomiallyBounded
#print axioms ConstitutiveSearch.localSearchableCodeFamily_inputPolynomiallyBounded
#print axioms ConstitutiveSearch.localSearchableCodePrimitiveBudget_eq_size
#print axioms ConstitutiveSearch.localSearchableCodeCompositionBudget_eq_zero
/- AXIOM_AUDIT_END -/
