import ConstitutiveSearch.LocalSearchableCodePolynomial
import ConstitutiveSearch.SAT.ComposedLocalCodeExecution
import ConstitutiveSearch.SAT.ExplicitFamilyInputComplexity

/-!
# Input-polynomial local execution of the constituted composed SAT code

The composed SAT benchmark has a directly constituted searchable code of size
two for every family index.

Applying the generic local-code family theorem yields an input-polynomial local
execution relative to the concrete binary input size of F(n):
* primitive budget exactly 2;
* composition-candidate budget exactly 0;
* no global candidate list;
* unit local fuel.
-/

namespace ConstitutiveSearch
namespace SAT

/--
The constituted composed-code family has polynomial candidate-free local
execution in the concrete input size of F(n).
-/
theorem composedConstitutedCodeFamily_localInputPolynomiallyBounded :
    LocalSearchableCodeFamilyInputPolynomiallyBounded
      (fun count =>
        composedPrimitiveSearch count)
      (fun count =>
        composedConstitutedCode count)
      explicitFamilyInputBitSize := by
  apply
    localSearchableCodeFamily_inputPolynomiallyBounded
      (fun count =>
        composedPrimitiveSearch count)
      (fun count =>
        composedConstitutedCode count)
      explicitFamilyInputBitSize
      composedConstitutedCode_searchable
  refine
    ⟨CostPolynomial.constant 2, ?_⟩
  intro count
  change
    (composedConstitutedCode count).size ≤
      2
  rw [composedConstitutedCode_size]
  exact Nat.le_refl 2

/-- Local primitive budget of the composed code is exactly two. -/
theorem composedConstitutedCode_localPrimitiveBudget
    (count : Nat) :
    localSearchableCodePrimitiveBudget
        (fun index =>
          composedConstitutedCode index)
        count =
      2 := by
  change
    (composedConstitutedCode count).size =
      2
  exact
    composedConstitutedCode_size count

/-- Local composition-candidate budget is exactly zero. -/
theorem composedConstitutedCode_localCompositionBudget
    (count : Nat) :
    localSearchableCodeCompositionBudget count =
      0 := by
  rfl

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.composedConstitutedCodeFamily_localInputPolynomiallyBounded
#print axioms ConstitutiveSearch.SAT.composedConstitutedCode_localPrimitiveBudget
#print axioms ConstitutiveSearch.SAT.composedConstitutedCode_localCompositionBudget
/- AXIOM_AUDIT_END -/
