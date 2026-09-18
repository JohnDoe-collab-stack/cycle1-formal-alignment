import ConstitutiveSearch.SAT.ExplicitFamilyNormalizationCosts

namespace ConstitutiveSearch.Tests.SATExplicitFamilyNormalizationCostsRegression

open ConstitutiveSearch
open SAT

abbrev formula3 : Cnf :=
  explicitStackedSymmetricFamily 3

abbrev root3 :
    GeneratedStructuralBranchContext formula3 :=
  explicitStackedRoot 3

theorem root3Var2Fresh :
    StructuralDecisionsAvoid
      2
      root3.context.decisions :=
  True.intro

theorem root3FlipSymmetric :
    FlipSymmetricAt root3.context.formula 2 := by
  change
    FlipSymmetricAt
      (stackedSymmetricBlocks 3 3)
      2
  exact
    stackedStage_flipSymmetric
      (PrefixAvoidsBelow.nil 3)
      (Nat.le_refl 3)

theorem genericRootSiblingSearchFound :
    (generatedStructuralFlipAtSearch formula3 2).find
        (GeneratedStructuralBranchContext.child
          root3 2 false root3Var2Fresh)
        (GeneratedStructuralBranchContext.child
          root3 2 true root3Var2Fresh) ≠
      none :=
  generatedStructuralFlipAtSearch_sibling_found
    root3
    2
    root3Var2Fresh
    root3FlipSymmetric

theorem directRootSiblingWidthOne :
    (reduceFlipSymmetricSiblings
      root3
      2
      root3Var2Fresh
      root3FlipSymmetric).width = 1 :=
  reduceFlipSymmetricSiblings_width
    root3
    2
    root3Var2Fresh
    root3FlipSymmetric

theorem genericFindCalls3 :
    (explicitFamilyResourceTrajectory 3).trajectory
        .normalizationFindCallCount =
      6 := by
  exact explicitFamilyNormalizationFindCallCount 3

theorem genericVerificationSurface3 :
    (explicitFamilyResourceTrajectory 3).trajectory
        .normalizationRelationVerificationSurface ≤
      explicitFamilyNormalizationVerificationBudget 3 :=
  explicitFamilyNormalizationVerificationSurface_le 3

end ConstitutiveSearch.Tests.SATExplicitFamilyNormalizationCostsRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyNormalizationCostsRegression.root3FlipSymmetric
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyNormalizationCostsRegression.genericRootSiblingSearchFound
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyNormalizationCostsRegression.directRootSiblingWidthOne
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyNormalizationCostsRegression.genericFindCalls3
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyNormalizationCostsRegression.genericVerificationSurface3
/- AXIOM_AUDIT_END -/
