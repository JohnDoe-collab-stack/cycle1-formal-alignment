import ConstitutiveSearch.ClosureSearchGrowingFuelSeparator

namespace ConstitutiveSearch.Tests.ClosureSearchGrowingFuelSeparatorRegression

open ConstitutiveSearch

theorem scaleFour :
    binaryFuelScale 4 = 16 := by
  rfl

theorem primitiveGrowingFuelFour :
    closurePrimitiveQueryBudget 1 4 + 1 =
      binaryFuelScale 4 :=
  closurePrimitiveOneCandidateGrowingFuel_exact 4

theorem primitiveGrowingFuelFourPow :
    closurePrimitiveQueryBudget 1 4 + 1 =
      2 ^ 4 :=
  closurePrimitiveOneCandidateGrowingFuel_eq_two_pow 4

theorem compositionGrowingFuelFour :
    closureCompositionCandidateBudget 1 4 + 1 =
      binaryFuelScale 4 :=
  closureCompositionOneCandidateGrowingFuel_exact 4

theorem compositionGrowingFuelFourPow :
    closureCompositionCandidateBudget 1 4 + 1 =
      2 ^ 4 :=
  closureCompositionOneCandidateGrowingFuel_eq_two_pow 4

theorem primitiveDegreeFour :
    (closurePrimitiveFixedFuelPolynomial 4).degree = 4 :=
  closurePrimitiveFixedFuelPolynomial_degree 4

theorem compositionDegreeFour :
    (closureCompositionFixedFuelPolynomial 4).degree = 4 :=
  closureCompositionFixedFuelPolynomial_degree 4

theorem primitiveIdentityFuelNoUniformDegree :
    ¬
      ∃ degreeCap : Nat,
        ∀ inputBits : Nat,
          (closurePrimitiveFixedFuelPolynomial
            inputBits).degree ≤ degreeCap :=
  closurePrimitiveIdentityFuel_no_uniform_degree

theorem compositionIdentityFuelNoUniformDegree :
    ¬
      ∃ degreeCap : Nat,
        ∀ inputBits : Nat,
          (closureCompositionFixedFuelPolynomial
            inputBits).degree ≤ degreeCap :=
  closureCompositionIdentityFuel_no_uniform_degree

end ConstitutiveSearch.Tests.ClosureSearchGrowingFuelSeparatorRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.ClosureSearchGrowingFuelSeparatorRegression.scaleFour
#print axioms ConstitutiveSearch.Tests.ClosureSearchGrowingFuelSeparatorRegression.primitiveGrowingFuelFour
#print axioms ConstitutiveSearch.Tests.ClosureSearchGrowingFuelSeparatorRegression.primitiveGrowingFuelFourPow
#print axioms ConstitutiveSearch.Tests.ClosureSearchGrowingFuelSeparatorRegression.compositionGrowingFuelFour
#print axioms ConstitutiveSearch.Tests.ClosureSearchGrowingFuelSeparatorRegression.compositionGrowingFuelFourPow
#print axioms ConstitutiveSearch.Tests.ClosureSearchGrowingFuelSeparatorRegression.primitiveDegreeFour
#print axioms ConstitutiveSearch.Tests.ClosureSearchGrowingFuelSeparatorRegression.compositionDegreeFour
#print axioms ConstitutiveSearch.Tests.ClosureSearchGrowingFuelSeparatorRegression.primitiveIdentityFuelNoUniformDegree
#print axioms ConstitutiveSearch.Tests.ClosureSearchGrowingFuelSeparatorRegression.compositionIdentityFuelNoUniformDegree
/- AXIOM_AUDIT_END -/
