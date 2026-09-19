import ConstitutiveSearch.SearchableTransportCodeValidation
import ConstitutiveSearch.SAT.ComposedLocalCodePolynomial

/-!
# Executable validation of the constituted composed SAT code

The composed SAT benchmark has a directly constituted searchable code of size
two.

This module runs the generic SearchableBy validator on that code and proves:
* validation succeeds;
* exactly two primitive relation-search queries are executed;
* the validation cost is input-polynomial in the concrete binary size of F(n).

This validation phase is distinct from both:
* constructing the proof-relevant code;
* executing the code's transports.
-/

namespace ConstitutiveSearch
namespace SAT

/-- Executable SearchableBy validation run of the constituted composed code. -/
def composedConstitutedCodeValidation
    (count : Nat) :
    SearchableCodeValidationRun :=
  validateSearchableCode
    (composedPrimitiveSearch count)
    (composedConstitutedCode count)

/-- Validation succeeds for every family member. -/
theorem composedConstitutedCodeValidation_success
    (count : Nat) :
    (composedConstitutedCodeValidation
      count).success =
      true := by
  unfold composedConstitutedCodeValidation
  exact
    validateSearchableCode_success_of_searchable
      (composedPrimitiveSearch count)
      (composedConstitutedCode count)
      (composedConstitutedCode_searchable count)

/-- Validation performs exactly two primitive relation-search queries. -/
theorem composedConstitutedCodeValidation_primitiveQueries
    (count : Nat) :
    (composedConstitutedCodeValidation
      count).primitiveQueries =
      2 := by
  unfold composedConstitutedCodeValidation
  calc
    (validateSearchableCode
        (composedPrimitiveSearch count)
        (composedConstitutedCode count)).primitiveQueries
        =
      (composedConstitutedCode count).size :=
        validateSearchableCode_primitiveQueries
          (composedPrimitiveSearch count)
          (composedConstitutedCode count)
    _ =
      2 :=
        composedConstitutedCode_size count

/-- The executable validation-query family is input-polynomial. -/
theorem composedConstitutedCodeValidation_inputPolynomiallyBounded :
    InputPolynomiallyBounded
      explicitFamilyInputBitSize
      (fun count =>
        (composedConstitutedCodeValidation
          count).primitiveQueries) := by
  refine
    ⟨CostPolynomial.constant 2, ?_⟩
  intro count
  change
    (composedConstitutedCodeValidation
      count).primitiveQueries ≤
      2
  rw [
    composedConstitutedCodeValidation_primitiveQueries
  ]
  exact Nat.le_refl 2

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.composedConstitutedCodeValidation
#print axioms ConstitutiveSearch.SAT.composedConstitutedCodeValidation_success
#print axioms ConstitutiveSearch.SAT.composedConstitutedCodeValidation_primitiveQueries
#print axioms ConstitutiveSearch.SAT.composedConstitutedCodeValidation_inputPolynomiallyBounded
/- AXIOM_AUDIT_END -/
