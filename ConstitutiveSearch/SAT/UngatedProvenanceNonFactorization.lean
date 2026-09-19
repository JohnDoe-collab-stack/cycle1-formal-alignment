import ConstitutiveSearch.ConstitutiveProjectionNonFactorization
import ConstitutiveSearch.SAT.WidthSeparators

/-!
# Ungated provenance non-factorization

The pre-audit projection-loss theorem used a dynamic search explicitly gated by
an Option-valued constitution field.  That separator remains useful as an
example of dynamic relation availability, but it is not sufficient as the
central non-factorization result.

This module uses the same ungated generatedStructuralFlipAtSearch on both
sides.

Two generated source/target pairs have exactly the same residual-formula
projection:
* a same-variable false/true sibling pair, whose provenance histories differ
  exactly by the announced polarity flip and are therefore reconstructible;
* two one-step children generated on distinct variables, whose residual formulas
  are still empty but whose provenance histories cannot be related by that same
  flip engine.

The difference is therefore caused by generated history/provenance retained in
the states, not by a gate testing the information erased by the projection.
-/

namespace ConstitutiveSearch
namespace SAT

/-- Two concrete organizations compared by one and the same ungated engine. -/
inductive UngatedProvenanceCase where
  | reconstructible
  | provenanceMismatch

/-- Freshness of variable zero at the empty generated root. -/
theorem ungatedRootZeroFresh :
    StructuralDecisionsAvoid
      0
      isolatedRoot.context.decisions :=
  isolatedRootFresh 0

/-- Empty CNF is flip-symmetric at every variable, in particular at zero. -/
theorem emptyFlipSymmetricZero :
    FlipSymmetricAt
      ([] : Cnf)
      0 := by
  rfl

/-- Positive source: false child of the same generated split at variable zero. -/
def ungatedPositiveSource :
    GeneratedStructuralBranchContext ([] : Cnf) :=
  GeneratedStructuralBranchContext.child
    isolatedRoot
    0
    false
    ungatedRootZeroFresh

/-- Positive target: true child of the same generated split at variable zero. -/
def ungatedPositiveTarget :
    GeneratedStructuralBranchContext ([] : Cnf) :=
  GeneratedStructuralBranchContext.child
    isolatedRoot
    0
    true
    ungatedRootZeroFresh

/-- Exact ungated relation carried by the positive generated sibling pair. -/
def ungatedPositiveRelation :
    GeneratedStructuralFlipAtRelation
      0
      ungatedPositiveSource
      ungatedPositiveTarget :=
  flipSymmetricSiblingRelation
    isolatedRoot
    0
    ungatedRootZeroFresh
    emptyFlipSymmetricZero

/-- The negative pair uses genuinely generated children with distinct provenance variables. -/
def ungatedNegativeSource :
    GeneratedStructuralBranchContext ([] : Cnf) :=
  isolatedChild 1

def ungatedNegativeTarget :
    GeneratedStructuralBranchContext ([] : Cnf) :=
  isolatedChild 2

/-- Select the concrete generated source for each comparison case. -/
def ungatedCaseSource :
    UngatedProvenanceCase →
      GeneratedStructuralBranchContext ([] : Cnf)
  | .reconstructible =>
      ungatedPositiveSource
  | .provenanceMismatch =>
      ungatedNegativeSource

/-- Select the concrete generated target for each comparison case. -/
def ungatedCaseTarget :
    UngatedProvenanceCase →
      GeneratedStructuralBranchContext ([] : Cnf)
  | .reconstructible =>
      ungatedPositiveTarget
  | .provenanceMismatch =>
      ungatedNegativeTarget

/--
Projection erasing generated provenance and retaining only source/target
residual formulas.
-/
def eraseGeneratedProvenance :
    UngatedProvenanceCase →
      Cnf × Cnf
  | kind =>
      ((ungatedCaseSource kind).context.formula,
        (ungatedCaseTarget kind).context.formula)

/-- Both cases have exactly the same residual-formula projection. -/
theorem ungatedProjection_same :
    eraseGeneratedProvenance
        .reconstructible =
      eraseGeneratedProvenance
        .provenanceMismatch := by
  rfl

/-- Reconstructibility under the single fixed ungated flip engine at variable zero. -/
def ActualUngatedRelationReconstructible
    (kind : UngatedProvenanceCase) : Prop :=
  (generatedStructuralFlipAtSearch
      ([] : Cnf)
      0).find
      (ungatedCaseSource kind)
      (ungatedCaseTarget kind) ≠
    none

/-- The positive generated sibling pair is found by the ungated engine. -/
theorem ungatedPositive_reconstructible :
    ActualUngatedRelationReconstructible
      .reconstructible := by
  unfold ActualUngatedRelationReconstructible
  dsimp [
    ungatedCaseSource,
    ungatedCaseTarget
  ]
  dsimp [generatedStructuralFlipAtSearch]
  rw [
    dif_pos
      ungatedPositiveRelation.formulaExact,
    dif_pos
      ungatedPositiveRelation.decisionsExact
  ]
  intro impossible
  cases impossible

/-- The same ungated engine fails on the distinct-provenance generated pair. -/
theorem ungatedNegative_not_reconstructible :
    ¬
      ActualUngatedRelationReconstructible
        .provenanceMismatch := by
  unfold ActualUngatedRelationReconstructible
  dsimp [
    ungatedCaseSource,
    ungatedCaseTarget,
    ungatedNegativeSource,
    ungatedNegativeTarget
  ]
  rw [
    isolatedChild_flipSearch_none
      0
      (by decide : (1 : Nat) ≠ 2)
  ]
  intro impossible
  exact impossible rfl

/--
Actual relation reconstructibility does not factor through residual formulas.

No dynamic constitution gate exists in this statement: both cases are queried
by the exact same generatedStructuralFlipAtSearch [] 0.
-/
theorem actualUngatedRelationReconstructibility_not_factor_through_residuals :
    ¬
      PredicateFactorsThrough
        eraseGeneratedProvenance
        ActualUngatedRelationReconstructible := by
  exact
    predicate_not_factors_of_same_projection
      eraseGeneratedProvenance
      ActualUngatedRelationReconstructible
      UngatedProvenanceCase.provenanceMismatch
      UngatedProvenanceCase.reconstructible
      ungatedProjection_same.symm
      ungatedNegative_not_reconstructible
      ungatedPositive_reconstructible

/-- Frontier associated with one ungated comparison case. -/
def ungatedCaseFrontier
    (kind : UngatedProvenanceCase) :
    List
      (GeneratedStructuralBranchContext ([] : Cnf)) :=
  [ungatedCaseSource kind,
    ungatedCaseTarget kind]

/-- Normalize both cases with the same ungated relation search and action. -/
def ungatedCaseReduction
    (kind : UngatedProvenanceCase) :=
  normalizeGeneratedStructuralFrontierByFlip
    ([] : Cnf)
    0
    (ungatedCaseFrontier kind)

/-- The reconstructible sibling pair reduces to width one. -/
theorem ungatedPositive_width :
    (ungatedCaseReduction
      .reconstructible).width =
      1 := by
  rfl

/-- The distinct-provenance pair remains width two under the same engine. -/
theorem ungatedNegative_width :
    (ungatedCaseReduction
      .provenanceMismatch).width =
      2 := by
  rfl

/-- Executed normalization width observation for each case. -/
def ungatedWidthObservation
    (kind : UngatedProvenanceCase) : Nat :=
  (ungatedCaseReduction kind).width

/--
The operational reduction width also fails to factor through the same
provenance-erasing residual-formula projection.
-/
theorem ungatedWidth_not_factor_through_residuals :
    ¬
      ValueFactorsThrough
        eraseGeneratedProvenance
        ungatedWidthObservation := by
  apply
    value_not_factors_of_same_projection
      eraseGeneratedProvenance
      ungatedWidthObservation
      UngatedProvenanceCase.reconstructible
      UngatedProvenanceCase.provenanceMismatch
      ungatedProjection_same
  rw [
    show
      ungatedWidthObservation
          .reconstructible =
        1 from
      ungatedPositive_width,
    show
      ungatedWidthObservation
          .provenanceMismatch =
        2 from
      ungatedNegative_width
  ]
  decide

/-- Minimal ungated projection-loss package used by the post-audit closure. -/
structure UngatedConstitutiveProjectionLoss : Prop where
  relationLoss :
    ¬
      PredicateFactorsThrough
        eraseGeneratedProvenance
        ActualUngatedRelationReconstructible
  widthLoss :
    ¬
      ValueFactorsThrough
        eraseGeneratedProvenance
        ungatedWidthObservation

theorem ungatedConstitutiveProjectionLoss :
    UngatedConstitutiveProjectionLoss :=
  { relationLoss :=
      actualUngatedRelationReconstructibility_not_factor_through_residuals
    widthLoss :=
      ungatedWidth_not_factor_through_residuals }

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.UngatedProvenanceCase
#print axioms ConstitutiveSearch.SAT.eraseGeneratedProvenance
#print axioms ConstitutiveSearch.SAT.ungatedProjection_same
#print axioms ConstitutiveSearch.SAT.ActualUngatedRelationReconstructible
#print axioms ConstitutiveSearch.SAT.ungatedPositive_reconstructible
#print axioms ConstitutiveSearch.SAT.ungatedNegative_not_reconstructible
#print axioms ConstitutiveSearch.SAT.actualUngatedRelationReconstructibility_not_factor_through_residuals
#print axioms ConstitutiveSearch.SAT.ungatedCaseReduction
#print axioms ConstitutiveSearch.SAT.ungatedPositive_width
#print axioms ConstitutiveSearch.SAT.ungatedNegative_width
#print axioms ConstitutiveSearch.SAT.ungatedWidth_not_factor_through_residuals
#print axioms ConstitutiveSearch.SAT.UngatedConstitutiveProjectionLoss
#print axioms ConstitutiveSearch.SAT.ungatedConstitutiveProjectionLoss
/- AXIOM_AUDIT_END -/
