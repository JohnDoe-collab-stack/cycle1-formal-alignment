import ConstitutiveSearch.LocalSearchableCodeComposition
import ConstitutiveSearch.SAT.ComposedLocalCodePolynomial

/-!
# Compositional construction of the local composed SAT code

The existing composedConstitutedCode is already built from two certified
primitive witnesses.  This module exposes that construction as a composition of
two local searchable code families.

Each local family:
* has one primitive atom;
* is searchable by composedPrimitiveSearch;
* has constant input-polynomial size one.

The generic local composition theorem then reconstructs the two-atom composed
family and its polynomial candidate-free execution.
-/

namespace ConstitutiveSearch
namespace SAT

/-- First locally constituted one-atom code family. -/
def composedFirstLocalCode
    (count : Nat) :
    TransportClosure
      (GeneratedStructuralFlipWitness
        (rootFormula :=
          explicitStackedSymmetricFamily count))
      (composedSource count)
      (composedMiddle count) :=
  TransportClosure.ofGenerator
    (composedConstitutedFirstWitness count)

/-- Second locally constituted one-atom code family. -/
def composedSecondLocalCode
    (count : Nat) :
    TransportClosure
      (GeneratedStructuralFlipWitness
        (rootFormula :=
          explicitStackedSymmetricFamily count))
      (composedMiddle count)
      (composedTarget count) :=
  TransportClosure.ofGenerator
    (composedConstitutedSecondWitness count)

/-- First local code has one primitive atom. -/
theorem composedFirstLocalCode_size
    (count : Nat) :
    (composedFirstLocalCode count).size =
      1 := by
  rfl

/-- Second local code has one primitive atom. -/
theorem composedSecondLocalCode_size
    (count : Nat) :
    (composedSecondLocalCode count).size =
      1 := by
  rfl

/-- First local code is executable by the announced primitive search. -/
theorem composedFirstLocalCode_searchable
    (count : Nat) :
    (composedFirstLocalCode count).SearchableBy
      (composedPrimitiveSearch count) := by
  change
    (composedPrimitiveSearch count).find
        (composedSource count)
        (composedMiddle count) ≠
      none
  rcases
      composedPrimitiveSearch_source_middle_some
        count with
    ⟨witness, exactFind⟩
  rw [exactFind]
  intro impossible
  cases impossible

/-- Second local code is executable by the same primitive search. -/
theorem composedSecondLocalCode_searchable
    (count : Nat) :
    (composedSecondLocalCode count).SearchableBy
      (composedPrimitiveSearch count) := by
  change
    (composedPrimitiveSearch count).find
        (composedMiddle count)
        (composedTarget count) ≠
      none
  rcases
      composedPrimitiveSearch_middle_target_some
        count with
    ⟨witness, exactFind⟩
  rw [exactFind]
  intro impossible
  cases impossible

/-- First local code family has constant input-polynomial size one. -/
theorem composedFirstLocalCode_size_inputPolynomiallyBounded :
    InputPolynomiallyBounded
      explicitFamilyInputBitSize
      (fun count =>
        (composedFirstLocalCode count).size) := by
  refine
    ⟨CostPolynomial.constant 1, ?_⟩
  intro count
  change 1 ≤ 1
  exact Nat.le_refl 1

/-- Second local code family has constant input-polynomial size one. -/
theorem composedSecondLocalCode_size_inputPolynomiallyBounded :
    InputPolynomiallyBounded
      explicitFamilyInputBitSize
      (fun count =>
        (composedSecondLocalCode count).size) := by
  refine
    ⟨CostPolynomial.constant 1, ?_⟩
  intro count
  change 1 ≤ 1
  exact Nat.le_refl 1

/-- Pointwise local composition is exactly the existing constituted code. -/
theorem composedLocalCodeComposition_eq_constituted
    (count : Nat) :
    composeSearchableCodeFamily
        composedFirstLocalCode
        composedSecondLocalCode
        count =
      composedConstitutedCode count := by
  rfl

/--
The composed family is polynomial by closure under local code composition,
rather than by a separate direct size argument.
-/
theorem composedConstitutedCodeFamily_localInputPolynomiallyBounded_byComposition :
    LocalSearchableCodeFamilyInputPolynomiallyBounded
      (fun count =>
        composedPrimitiveSearch count)
      (composeSearchableCodeFamily
        composedFirstLocalCode
        composedSecondLocalCode)
      explicitFamilyInputBitSize :=
  composeSearchableCodeFamily_localInputPolynomiallyBounded
    (fun count =>
      composedPrimitiveSearch count)
    composedFirstLocalCode
    composedSecondLocalCode
    explicitFamilyInputBitSize
    composedFirstLocalCode_searchable
    composedSecondLocalCode_searchable
    composedFirstLocalCode_size_inputPolynomiallyBounded
    composedSecondLocalCode_size_inputPolynomiallyBounded

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.composedFirstLocalCode
#print axioms ConstitutiveSearch.SAT.composedSecondLocalCode
#print axioms ConstitutiveSearch.SAT.composedFirstLocalCode_size
#print axioms ConstitutiveSearch.SAT.composedSecondLocalCode_size
#print axioms ConstitutiveSearch.SAT.composedFirstLocalCode_searchable
#print axioms ConstitutiveSearch.SAT.composedSecondLocalCode_searchable
#print axioms ConstitutiveSearch.SAT.composedFirstLocalCode_size_inputPolynomiallyBounded
#print axioms ConstitutiveSearch.SAT.composedSecondLocalCode_size_inputPolynomiallyBounded
#print axioms ConstitutiveSearch.SAT.composedLocalCodeComposition_eq_constituted
#print axioms ConstitutiveSearch.SAT.composedConstitutedCodeFamily_localInputPolynomiallyBounded_byComposition
/- AXIOM_AUDIT_END -/
