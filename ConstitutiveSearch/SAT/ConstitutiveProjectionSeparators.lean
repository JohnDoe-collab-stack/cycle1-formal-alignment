import ConstitutiveSearch.ConstitutiveProjectionNonFactorization
import ConstitutiveSearch.SAT.StructuralDynamicRelation
import ConstitutiveSearch.SAT.ParametricSymmetricFamily
import ConstitutiveSearch.SAT.ComposedLocalCodeExecution

/-!
# Constitutive information does not factor through flattened projections

Two existing separators close the information-loss obligation.

1. Dynamic split constitution:
   the frontier is identical before and after recording one exact split
   certificate, while the corresponding structural relation changes from
   unreconstructible to reconstructible.  Relation availability therefore does
   not factor through the frontier projection.

2. Composed SAT benchmark:
   constituted-local execution and the flattened global endpoint query have the
   same source and target.  The local execution realizes zero composition
   candidates, while the actual global ClosureSearch run executes one.
   Composition-search cost therefore does not factor through endpoint projection.

No new search mechanism is introduced here.
-/

namespace ConstitutiveSearch
namespace SAT

/-- Same split frontier without the exact split certificate recorded. -/
def splitFrontierBeforeConstitution
    {rootFormula : Cnf}
    (anchor :
      GeneratedSplitAnchor
        rootFormula) :
    ConstitutiveState
      (generatedStructuralBranchSystem
        rootFormula)
      (GeneratedSplitConstitution
        rootFormula) :=
  { frontier :=
      anchor.frontier
    constitution :=
      none }

/-- Same split frontier after recording the exact split certificate. -/
def splitFrontierAfterConstitution
    {rootFormula : Cnf}
    (anchor :
      GeneratedSplitAnchor
        rootFormula) :
    ConstitutiveState
      (generatedStructuralBranchSystem
        rootFormula)
      (GeneratedSplitConstitution
        rootFormula) :=
  { frontier :=
      anchor.frontier
    constitution :=
      some anchor }

/-- Projection that forgets constituted split data and retains only the frontier. -/
def forgetSplitConstitution
    {rootFormula : Cnf}
    (current :
      ConstitutiveState
        (generatedStructuralBranchSystem
          rootFormula)
        (GeneratedSplitConstitution
          rootFormula)) :
    List
      (GeneratedStructuralBranchContext
        rootFormula) :=
  current.frontier

/-- The projection is exactly unchanged when only the split certificate is added. -/
theorem splitFrontier_projection_same
    {rootFormula : Cnf}
    (anchor :
      GeneratedSplitAnchor
        rootFormula) :
    forgetSplitConstitution
        (splitFrontierBeforeConstitution
          anchor) =
      forgetSplitConstitution
        (splitFrontierAfterConstitution
          anchor) := by
  rfl

/-- Reconstructibility of the anchor sibling relation at one constituted state. -/
def SplitRelationReconstructible
    {rootFormula : Cnf}
    (anchor :
      GeneratedSplitAnchor
        rootFormula)
    (current :
      ConstitutiveState
        (generatedStructuralBranchSystem
          rootFormula)
        (GeneratedSplitConstitution
          rootFormula)) : Prop :=
  (constitutedSplitFlipSearch
      rootFormula).find
      current
      anchor.falseChild
      anchor.trueChild ≠
    none

/-- Without the split certificate, its gated relation is not reconstructible. -/
theorem splitRelation_not_reconstructible_before
    {rootFormula : Cnf}
    (anchor :
      GeneratedSplitAnchor
        rootFormula) :
    ¬
      SplitRelationReconstructible
        anchor
        (splitFrontierBeforeConstitution
          anchor) := by
  intro reconstructible
  exact
    reconstructible
      rfl

/--
For a flip-symmetric constituted split, the exact same frontier reconstructs
the sibling relation after the certificate is recorded.
-/
theorem splitRelation_reconstructible_after
    {rootFormula : Cnf}
    (anchor :
      GeneratedSplitAnchor
        rootFormula)
    (symmetric :
      FlipSymmetricAt
        anchor.parent.context.formula
        anchor.var) :
    SplitRelationReconstructible
      anchor
      (splitFrontierAfterConstitution
        anchor) := by
  let relation :=
    flipSymmetricSiblingRelation
      anchor.parent
      anchor.var
      anchor.fresh
      symmetric
  have formulaExact :
      anchor.trueChild.context.formula =
        Cnf.flipAt
          anchor.var
          anchor.falseChild.context.formula := by
    simpa only [
      GeneratedSplitAnchor.falseChild,
      GeneratedSplitAnchor.trueChild
    ] using
      relation.formulaExact
  have decisionsExact :
      anchor.trueChild.context.decisions =
        flipStructuralDecisionsAt
          anchor.var
          anchor.falseChild.context.decisions := by
    simpa only [
      GeneratedSplitAnchor.falseChild,
      GeneratedSplitAnchor.trueChild
    ] using
      relation.decisionsExact
  have primitiveFound :
      (generatedStructuralFlipAtSearch
        rootFormula
        anchor.var).find
          anchor.falseChild
          anchor.trueChild ≠
        none := by
    dsimp [
      generatedStructuralFlipAtSearch
    ]
    rw [
      dif_pos formulaExact,
      dif_pos decisionsExact
    ]
    intro impossible
    cases impossible
  unfold SplitRelationReconstructible
  simp only [
    splitFrontierAfterConstitution,
    constitutedSplitFlipSearch
  ]
  cases found :
      (generatedStructuralFlipAtSearch
        rootFormula
        anchor.var).find
          anchor.falseChild
          anchor.trueChild with
  | none =>
      exact
        False.elim
          (primitiveFound found)
  | some flip =>
      simp only [found]
      intro impossible
      cases impossible

/--
Relation reconstructibility cannot be recovered from the frontier alone.

The frontier projection forgets constituted information that is computationally
relevant to relation availability.
-/
theorem splitRelationReconstructibility_not_factor_through_frontier
    {rootFormula : Cnf}
    (anchor :
      GeneratedSplitAnchor
        rootFormula)
    (symmetric :
      FlipSymmetricAt
        anchor.parent.context.formula
        anchor.var) :
    ¬
      PredicateFactorsThrough
        forgetSplitConstitution
        (SplitRelationReconstructible
          anchor) := by
  exact
    predicate_not_factors_of_same_projection
      forgetSplitConstitution
      (SplitRelationReconstructible
        anchor)
      (splitFrontierBeforeConstitution
        anchor)
      (splitFrontierAfterConstitution
        anchor)
      (splitFrontier_projection_same
        anchor)
      (splitRelation_not_reconstructible_before
        anchor)
      (splitRelation_reconstructible_after
        anchor
        symmetric)

/--
Two organizations of the same composed SAT endpoint request.

The local branch keeps the constituted two-atom organization.
The global branch forgets that organization and asks ClosureSearch for the
source-to-target relation.
-/
inductive ComposedEndpointOrganization where
  | constitutedLocal
  | flattenedGlobal

/-- Both organizations project to the exact same endpoint pair. -/
def composedEndpointProjection
    (count : Nat)
    (_organization :
      ComposedEndpointOrganization) :
    GeneratedStructuralBranchContext
        (explicitStackedSymmetricFamily
          count) ×
      GeneratedStructuralBranchContext
        (explicitStackedSymmetricFamily
          count) :=
  (composedSource count,
    composedTarget count)

/--
Executed/realized composition-candidate observation for the two organizations.

The local value is realized by the candidate-free constituted execution.
The global value is read directly from the actual bounded ClosureSearch run.
-/
def composedCompositionCandidateObservation
    (count : Nat) :
    ComposedEndpointOrganization →
      Nat
  | .constitutedLocal =>
      0
  | .flattenedGlobal =>
      (composedClosureFuelTwo
        count).stats.compositionCandidates

/-- The constituted-local observation is realized by an actual local path run. -/
theorem composedLocalObservation_realized
    (count : Nat) :
    ∃ path :
        PrimitiveHitPath
          (composedPrimitiveSearch count)
          (composedSource count)
          (composedTarget count),
      (path.sequentialStats
          []
          1).compositionCandidates =
        composedCompositionCandidateObservation
          count
          .constitutedLocal := by
  rcases
      composedConstitutedCode_localStats
        count with
    ⟨path,
      _lengthExact,
      _primitiveExact,
      compositionExact⟩
  exact
    ⟨path,
      compositionExact⟩

/-- The flattened global observation is the actual one-candidate ClosureSearch run. -/
theorem composedGlobalObservation_one
    (count : Nat) :
    composedCompositionCandidateObservation
        count
        .flattenedGlobal =
      1 := by
  exact
    composedClosureFuelTwo_compositionCandidates
      count

/--
Actual composition-search cost does not factor through the endpoint pair.

Forgetting the constituted temporal organization maps both executions to the
same source/target pair while changing the composition-candidate count from
zero to one.
-/
theorem composedExecutionCost_not_factor_through_endpoints
    (count : Nat) :
    ¬
      ValueFactorsThrough
        (composedEndpointProjection
          count)
        (composedCompositionCandidateObservation
          count) := by
  apply
    value_not_factors_of_same_projection
      (composedEndpointProjection
        count)
      (composedCompositionCandidateObservation
        count)
      ComposedEndpointOrganization.constitutedLocal
      ComposedEndpointOrganization.flattenedGlobal
  · rfl
  · change
      0 ≠
        (composedClosureFuelTwo
          count).stats.compositionCandidates
    rw [
      composedClosureFuelTwo_compositionCandidates
    ]
    decide

/--
Minimal closed non-factorization package:
* relation availability does not factor through frontier-only projection;
* execution composition cost does not factor through endpoint-only projection.
-/
structure ConstitutiveProjectionLossClosed : Prop where
  relationLoss :
    ∀ {rootFormula : Cnf}
      (anchor :
        GeneratedSplitAnchor
          rootFormula)
      (symmetric :
        FlipSymmetricAt
          anchor.parent.context.formula
          anchor.var),
      ¬
        PredicateFactorsThrough
          forgetSplitConstitution
          (SplitRelationReconstructible
            anchor)
  organizationCostLoss :
    ∀ count : Nat,
      ¬
        ValueFactorsThrough
          (composedEndpointProjection
            count)
          (composedCompositionCandidateObservation
            count)

/-- The existing separators close the announced projection-loss obligation. -/
theorem constitutiveProjectionLossClosed :
    ConstitutiveProjectionLossClosed :=
  { relationLoss :=
      splitRelationReconstructibility_not_factor_through_frontier
    organizationCostLoss :=
      composedExecutionCost_not_factor_through_endpoints }

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.splitFrontierBeforeConstitution
#print axioms ConstitutiveSearch.SAT.splitFrontierAfterConstitution
#print axioms ConstitutiveSearch.SAT.forgetSplitConstitution
#print axioms ConstitutiveSearch.SAT.SplitRelationReconstructible
#print axioms ConstitutiveSearch.SAT.splitRelation_not_reconstructible_before
#print axioms ConstitutiveSearch.SAT.splitRelation_reconstructible_after
#print axioms ConstitutiveSearch.SAT.splitRelationReconstructibility_not_factor_through_frontier
#print axioms ConstitutiveSearch.SAT.ComposedEndpointOrganization
#print axioms ConstitutiveSearch.SAT.composedEndpointProjection
#print axioms ConstitutiveSearch.SAT.composedCompositionCandidateObservation
#print axioms ConstitutiveSearch.SAT.composedLocalObservation_realized
#print axioms ConstitutiveSearch.SAT.composedGlobalObservation_one
#print axioms ConstitutiveSearch.SAT.composedExecutionCost_not_factor_through_endpoints
#print axioms ConstitutiveSearch.SAT.ConstitutiveProjectionLossClosed
#print axioms ConstitutiveSearch.SAT.constitutiveProjectionLossClosed
/- AXIOM_AUDIT_END -/
