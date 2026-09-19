import ConstitutiveSearch.ConstitutedPrimitivePath
import ConstitutiveSearch.SAT.ComposedSearchableCodeValidation

/-!
# Constituted primitive path for the composed SAT benchmark

The composed SAT benchmark already provides two certified primitive witnesses:
source -> middle and middle -> target.

This module packages them as one ConstitutedPrimitivePath.  No primitive search
and no global closure search is used to construct that path.

The path:
* has length two;
* compiles exactly to composedConstitutedCode;
* is searchable by composedPrimitiveSearch;
* validates successfully with exactly two primitive queries;
* admits candidate-free local execution of the compiled code.
-/

namespace ConstitutiveSearch
namespace SAT

/-- Directly constituted two-edge primitive witness path. -/
def composedConstitutedPrimitivePath
    (count : Nat) :
    ConstitutedPrimitivePath
      (GeneratedStructuralFlipWitness
        (rootFormula :=
          explicitStackedSymmetricFamily count))
      (composedSource count)
      (composedTarget count) :=
  .step
    (composedConstitutedFirstWitness count)
    (.atom
      (composedConstitutedSecondWitness count))

/-- The constituted witness path has exactly two primitive edges. -/
theorem composedConstitutedPrimitivePath_length
    (count : Nat) :
    (composedConstitutedPrimitivePath
      count).length =
      2 := by
  rfl

/-- Compiling the constituted path gives exactly the existing composed code. -/
theorem composedConstitutedPrimitivePath_code
    (count : Nat) :
    (composedConstitutedPrimitivePath
      count).toTransportCode =
      composedConstitutedCode count := by
  rfl

/-- Every constituted edge of the path is searchable by the announced engine. -/
theorem composedConstitutedPrimitivePath_searchable
    (count : Nat) :
    (composedConstitutedPrimitivePath
      count).SearchableBy
        (composedPrimitiveSearch count) := by
  apply
    ((composedConstitutedPrimitivePath
        count).toTransportCode_searchable_iff
      (composedPrimitiveSearch count)).1
  rw [
    composedConstitutedPrimitivePath_code
  ]
  exact
    composedConstitutedCode_searchable
      count

/-- Path validation succeeds. -/
theorem composedConstitutedPrimitivePath_validation_success
    (count : Nat) :
    (validateSearchableCode
        (composedPrimitiveSearch count)
        (composedConstitutedPrimitivePath
          count).toTransportCode).success =
      true := by
  exact
    ((composedConstitutedPrimitivePath
        count).validation_success_iff
      (composedPrimitiveSearch count)).2
      (composedConstitutedPrimitivePath_searchable
        count)

/-- Path validation performs exactly two primitive queries. -/
theorem composedConstitutedPrimitivePath_validation_queries
    (count : Nat) :
    (validateSearchableCode
        (composedPrimitiveSearch count)
        (composedConstitutedPrimitivePath
          count).toTransportCode).primitiveQueries =
      2 := by
  calc
    (validateSearchableCode
        (composedPrimitiveSearch count)
        (composedConstitutedPrimitivePath
          count).toTransportCode).primitiveQueries
        =
      (composedConstitutedPrimitivePath
        count).length :=
          (composedConstitutedPrimitivePath
            count).validation_primitiveQueries
              (composedPrimitiveSearch count)
    _ =
      2 :=
        composedConstitutedPrimitivePath_length
          count

/-- Complete constituted-path validation and local-execution certificate. -/
theorem composedConstitutedPrimitivePath_endToEnd
    (count : Nat) :
    ConstitutedPrimitivePath.EndToEndLocalExecution
      (composedPrimitiveSearch count)
      (composedConstitutedPrimitivePath count) :=
  (composedConstitutedPrimitivePath
    count).endToEndLocalExecution_of_searchable
      (composedPrimitiveSearch count)
      (composedConstitutedPrimitivePath_searchable
        count)

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.composedConstitutedPrimitivePath
#print axioms ConstitutiveSearch.SAT.composedConstitutedPrimitivePath_length
#print axioms ConstitutiveSearch.SAT.composedConstitutedPrimitivePath_code
#print axioms ConstitutiveSearch.SAT.composedConstitutedPrimitivePath_searchable
#print axioms ConstitutiveSearch.SAT.composedConstitutedPrimitivePath_validation_success
#print axioms ConstitutiveSearch.SAT.composedConstitutedPrimitivePath_validation_queries
#print axioms ConstitutiveSearch.SAT.composedConstitutedPrimitivePath_endToEnd
/- AXIOM_AUDIT_END -/
