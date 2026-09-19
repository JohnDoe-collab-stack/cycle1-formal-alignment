import ConstitutiveSearch.ConstitutiveProjectionNonFactorization
import ConstitutiveSearch.SAT.ParametricComposedFamily

/-!
# Parametric ungated provenance non-factorization

The first ungated separator used two states over the empty residual formula.
This module removes both sources of degeneracy.  It constructs an infinite
family of nonempty residual formulas whose provenance-erasing projections vary
with the family index.  At every index, the same ungated flip engine sees:

* a sibling pair generated at its selected variable, which it reconstructs;
* a pair generated at two different variables, which it rejects because their
  constituted histories do not match the selected flip.

The positive and negative cases at one index have identical nonempty residual
formula projections.  Across consecutive indices those projections differ.
Thus the failure of factorization is neither a dynamic gate, nor a constant
projection on a two-point domain, nor an artifact of empty residual syntax.
-/

namespace ConstitutiveSearch
namespace SAT

/-- Family index tagged by the two provenance organizations being compared. -/
inductive ParametricProvenanceCase where
  | reconstructible (index : Nat)
  | provenanceMismatch (index : Nat)

/-- Variable selected by the common ungated engine at one family index. -/
def parametricEngineVar (_index : Nat) : Var :=
  0

/-- First variable used only by the mismatched provenance organization. -/
def parametricMismatchSourceVar (_index : Nat) : Var :=
  1

/-- Second variable used only by the mismatched provenance organization. -/
def parametricMismatchTargetVar (_index : Nat) : Var :=
  2

/-- Variable retained in the nonempty residual formula. -/
def parametricResidualVar (index : Nat) : Var :=
  index + 3

/-- A nonempty root and residual formula varying with the family index. -/
def parametricResidualFormula (index : Nat) : Cnf :=
  [[Literal.positive (parametricResidualVar index)]]

/-- Generated root for the indexed residual formula. -/
def parametricProvenanceRoot
    (index : Nat) :
    GeneratedStructuralBranchContext
      (parametricResidualFormula index) :=
  GeneratedStructuralBranchContext.root
    (parametricResidualFormula index)

/-- Every candidate variable is fresh at the indexed root. -/
theorem parametricRootFresh
    (index : Nat)
    (var : Var) :
    StructuralDecisionsAvoid
      var
      (parametricProvenanceRoot index).context.decisions :=
  True.intro

/-- The retained residual literal differs from the engine variable. -/
theorem parametricResidualVar_ne_engine
    (index : Nat) :
    parametricResidualVar index ≠ parametricEngineVar index := by
  unfold parametricResidualVar parametricEngineVar
  intro impossible
  exact Nat.noConfusion impossible

/-- The retained residual literal differs from the first mismatch variable. -/
theorem parametricResidualVar_ne_mismatchSource
    (index : Nat) :
    parametricResidualVar index ≠
      parametricMismatchSourceVar index := by
  unfold parametricResidualVar parametricMismatchSourceVar
  intro impossible
  have reduced := Nat.succ.inj impossible
  exact Nat.noConfusion reduced

/-- The retained residual literal differs from the second mismatch variable. -/
theorem parametricResidualVar_ne_mismatchTarget
    (index : Nat) :
    parametricResidualVar index ≠
      parametricMismatchTargetVar index := by
  unfold parametricResidualVar parametricMismatchTargetVar
  intro impossible
  have reducedOnce := Nat.succ.inj impossible
  have reducedTwice := Nat.succ.inj reducedOnce
  exact Nat.noConfusion reducedTwice

/-- The indexed formula avoids the first mismatch variable. -/
theorem parametricResidualFormula_avoids_mismatchSource
    (index : Nat) :
    Cnf.AvoidsVar
      (parametricMismatchSourceVar index)
      (parametricResidualFormula index) :=
  ⟨⟨parametricResidualVar_ne_mismatchSource index, True.intro⟩,
    True.intro⟩

/-- The indexed formula avoids the second mismatch variable. -/
theorem parametricResidualFormula_avoids_mismatchTarget
    (index : Nat) :
    Cnf.AvoidsVar
      (parametricMismatchTargetVar index)
      (parametricResidualFormula index) :=
  ⟨⟨parametricResidualVar_ne_mismatchTarget index, True.intro⟩,
    True.intro⟩

/-- The indexed nonempty formula avoids the engine variable. -/
theorem parametricResidualFormula_avoids_engine
    (index : Nat) :
    Cnf.AvoidsVar
      (parametricEngineVar index)
      (parametricResidualFormula index) := by
  exact
    ⟨⟨parametricResidualVar_ne_engine index, True.intro⟩,
      True.intro⟩

/-- Avoiding the engine variable makes the indexed root flip-symmetric. -/
theorem parametricResidualFormula_flipSymmetric
    (index : Nat) :
    FlipSymmetricAt
      (parametricResidualFormula index)
      (parametricEngineVar index) := by
  unfold FlipSymmetricAt
  rw [
    Cnf.branchResidual_eq_self
      (parametricResidualFormula_avoids_engine index)
      true,
    Cnf.branchResidual_eq_self
      (parametricResidualFormula_avoids_engine index)
      false,
    Cnf.flipAt_eq_self
      (parametricResidualFormula_avoids_engine index)
  ]

/-- Positive source: false child at the variable selected by the engine. -/
def parametricPositiveSource
    (index : Nat) :
    GeneratedStructuralBranchContext
      (parametricResidualFormula index) :=
  GeneratedStructuralBranchContext.child
    (parametricProvenanceRoot index)
    (parametricEngineVar index)
    false
    (parametricRootFresh index (parametricEngineVar index))

/-- Positive target: true sibling at the variable selected by the engine. -/
def parametricPositiveTarget
    (index : Nat) :
    GeneratedStructuralBranchContext
      (parametricResidualFormula index) :=
  GeneratedStructuralBranchContext.child
    (parametricProvenanceRoot index)
    (parametricEngineVar index)
    true
    (parametricRootFresh index (parametricEngineVar index))

/-- Certified positive relation for every index. -/
def parametricPositiveRelation
    (index : Nat) :
    GeneratedStructuralFlipAtRelation
      (parametricEngineVar index)
      (parametricPositiveSource index)
      (parametricPositiveTarget index) :=
  flipSymmetricSiblingRelation
    (parametricProvenanceRoot index)
    (parametricEngineVar index)
    (parametricRootFresh index (parametricEngineVar index))
    (parametricResidualFormula_flipSymmetric index)

/-- Negative source generated at a variable distinct from the engine variable. -/
def parametricNegativeSource
    (index : Nat) :
    GeneratedStructuralBranchContext
      (parametricResidualFormula index) :=
  GeneratedStructuralBranchContext.child
    (parametricProvenanceRoot index)
    (parametricMismatchSourceVar index)
    false
    (parametricRootFresh index (parametricMismatchSourceVar index))

/-- Negative target generated at a second distinct variable. -/
def parametricNegativeTarget
    (index : Nat) :
    GeneratedStructuralBranchContext
      (parametricResidualFormula index) :=
  GeneratedStructuralBranchContext.child
    (parametricProvenanceRoot index)
    (parametricMismatchTargetVar index)
    true
    (parametricRootFresh index (parametricMismatchTargetVar index))

/-- One dependent package lets the family vary its root formula with the index. -/
structure ParametricProvenanceConfiguration where
  rootFormula : Cnf
  engineVar : Var
  source : GeneratedStructuralBranchContext rootFormula
  target : GeneratedStructuralBranchContext rootFormula

/-- Configuration selected by an indexed positive or negative case. -/
def parametricProvenanceConfiguration :
    ParametricProvenanceCase → ParametricProvenanceConfiguration
  | .reconstructible index =>
      { rootFormula := parametricResidualFormula index
        engineVar := parametricEngineVar index
        source := parametricPositiveSource index
        target := parametricPositiveTarget index }
  | .provenanceMismatch index =>
      { rootFormula := parametricResidualFormula index
        engineVar := parametricEngineVar index
        source := parametricNegativeSource index
        target := parametricNegativeTarget index }

/-- Projection erasing provenance but retaining both residual formulas. -/
def eraseParametricProvenance
    (kind : ParametricProvenanceCase) : Cnf × Cnf :=
  let configuration := parametricProvenanceConfiguration kind
  (configuration.source.context.formula,
    configuration.target.context.formula)

/-- Reconstructibility by the exact ungated engine stored in the configuration. -/
def ParametricRelationReconstructible
    (kind : ParametricProvenanceCase) : Prop :=
  let configuration := parametricProvenanceConfiguration kind
  (generatedStructuralFlipAtSearch
      configuration.rootFormula
      configuration.engineVar).find
      configuration.source
      configuration.target ≠ none

/-- The common projected formula pair is explicitly nonempty. -/
theorem parametricProjection_positive_exact
    (index : Nat) :
    eraseParametricProvenance (.reconstructible index) =
      (parametricResidualFormula index,
        parametricResidualFormula index) := by
  unfold eraseParametricProvenance parametricProvenanceConfiguration
  simp only [parametricPositiveSource, parametricPositiveTarget]
  change
    (branchResidual
        (parametricResidualFormula index)
        (parametricEngineVar index)
        false,
      branchResidual
        (parametricResidualFormula index)
        (parametricEngineVar index)
        true) =
      (parametricResidualFormula index,
        parametricResidualFormula index)
  rw [
    Cnf.branchResidual_eq_self
      (parametricResidualFormula_avoids_engine index)
      false,
    Cnf.branchResidual_eq_self
      (parametricResidualFormula_avoids_engine index)
      true
  ]

/--
The negative organization has the same nonempty residual projection.  Its
branch variables are absent from the retained singleton formula.
-/
theorem parametricProjection_negative_exact
    (index : Nat) :
    eraseParametricProvenance (.provenanceMismatch index) =
      (parametricResidualFormula index,
        parametricResidualFormula index) := by
  unfold eraseParametricProvenance parametricProvenanceConfiguration
  simp only [parametricNegativeSource, parametricNegativeTarget]
  change
    (branchResidual
        (parametricResidualFormula index)
        (parametricMismatchSourceVar index)
        false,
      branchResidual
        (parametricResidualFormula index)
        (parametricMismatchTargetVar index)
        true) =
      (parametricResidualFormula index,
        parametricResidualFormula index)
  rw [
    Cnf.branchResidual_eq_self
      (parametricResidualFormula_avoids_mismatchSource index)
      false,
    Cnf.branchResidual_eq_self
      (parametricResidualFormula_avoids_mismatchTarget index)
      true
  ]

/-- Positive and negative organizations coincide after provenance erasure. -/
theorem parametricProjection_same
    (index : Nat) :
    eraseParametricProvenance (.reconstructible index) =
      eraseParametricProvenance (.provenanceMismatch index) := by
  rw [
    parametricProjection_positive_exact,
    parametricProjection_negative_exact
  ]

/-- No member of the positive family has the old empty residual projection. -/
theorem parametricProjection_nonempty
    (index : Nat) :
    eraseParametricProvenance (.reconstructible index) ≠
      (([] : Cnf), ([] : Cnf)) := by
  intro collapsed
  have pairCollapsed :
      (parametricResidualFormula index,
          parametricResidualFormula index) =
        (([] : Cnf), ([] : Cnf)) :=
    Eq.trans
      (parametricProjection_positive_exact index).symm
      collapsed
  have formulaCollapsed := congrArg Prod.fst pairCollapsed
  change
    [[Literal.positive (parametricResidualVar index)]] = []
      at formulaCollapsed
  cases formulaCollapsed

/-- Constructive successor separation used without imported arithmetic axioms. -/
theorem parametricIndex_ne_next :
    ∀ index : Nat, index ≠ index + 1
  | 0 => by
      intro impossible
      cases impossible
  | index + 1 => by
      intro impossible
      exact
        parametricIndex_ne_next index
          (Nat.succ.inj impossible)

/-- The retained variable changes strictly with the family index. -/
theorem parametricResidualVar_strict
    (index : Nat) :
    parametricResidualVar index ≠
      parametricResidualVar (index + 1) := by
  unfold parametricResidualVar
  intro same
  have reducedOnce := Nat.succ.inj same
  have reducedTwice := Nat.succ.inj reducedOnce
  have reducedThreeTimes := Nat.succ.inj reducedTwice
  exact parametricIndex_ne_next index reducedThreeTimes

/-- Consequently the complete nonempty residual syntax changes with the index. -/
theorem parametricResidualFormula_strict
    (index : Nat) :
    parametricResidualFormula index ≠
      parametricResidualFormula (index + 1) := by
  intro formulaSame
  change
    [[Literal.positive (index + 3)]] =
      [[Literal.positive ((index + 1) + 3)]] at formulaSame
  have clauseSame := (List.cons.inj formulaSame).1
  have literalSame := (List.cons.inj clauseSame).1
  exact
    parametricResidualVar_strict index
      (Literal.positive.inj literalSame)

/-- Consecutive family indices do not collapse to one constant projection. -/
theorem parametricProjection_strict
    (index : Nat) :
    eraseParametricProvenance (.reconstructible index) ≠
      eraseParametricProvenance (.reconstructible (index + 1)) := by
  intro sameProjection
  have same :
      (parametricResidualFormula index,
          parametricResidualFormula index) =
        (parametricResidualFormula (index + 1),
          parametricResidualFormula (index + 1)) :=
    Eq.trans
      (parametricProjection_positive_exact index).symm
      (Eq.trans
        sameProjection
        (parametricProjection_positive_exact (index + 1)))
  have formulaSame := congrArg Prod.fst same
  exact parametricResidualFormula_strict index formulaSame

/-- The positive sibling organization is found at every family index. -/
theorem parametricPositive_reconstructible
    (index : Nat) :
    ParametricRelationReconstructible (.reconstructible index) := by
  unfold ParametricRelationReconstructible
  dsimp [parametricProvenanceConfiguration]
  exact
    generatedStructuralFlipAtSearch_found_of_relation
      (parametricPositiveRelation index)

/--
The negative pair passes the engine's formula test.  Its rejection is therefore
caused by the constituted-history mismatch proved below.
-/
theorem parametricNegative_formula_matches_engine
    (index : Nat) :
    (parametricNegativeTarget index).context.formula =
      Cnf.flipAt
        (parametricEngineVar index)
        (parametricNegativeSource index).context.formula := by
  change
    branchResidual
        (parametricResidualFormula index)
        (parametricMismatchTargetVar index)
        true =
      Cnf.flipAt
        (parametricEngineVar index)
        (branchResidual
          (parametricResidualFormula index)
          (parametricMismatchSourceVar index)
          false)
  rw [
    Cnf.branchResidual_eq_self
      (parametricResidualFormula_avoids_mismatchTarget index)
      true,
    Cnf.branchResidual_eq_self
      (parametricResidualFormula_avoids_mismatchSource index)
      false,
    Cnf.flipAt_eq_self
      (parametricResidualFormula_avoids_engine index)
  ]

/-- The mismatched histories cannot equal a flip at the engine variable. -/
theorem parametricNegative_decisions_mismatch
    (index : Nat) :
    (parametricNegativeTarget index).context.decisions ≠
      flipStructuralDecisionsAt
        (parametricEngineVar index)
        (parametricNegativeSource index).context.decisions := by
  intro same
  change
    [{ var := 2, value := true }] =
      flipStructuralDecisionsAt
        0
        [{ var := 1, value := false }] at same
  simp only [flipStructuralDecisionsAt, StructuralBranchDecision.flipAt] at same
  rw [if_neg (by decide : (1 : Nat) ≠ 0)] at same
  exact
    (by decide :
      ([{ var := 2, value := true }] :
          List StructuralBranchDecision) ≠
        [{ var := 1, value := false }])
      same

/-- The same ungated engine rejects the provenance-mismatched organization. -/
theorem parametricNegative_not_reconstructible
    (index : Nat) :
    ¬ ParametricRelationReconstructible (.provenanceMismatch index) := by
  unfold ParametricRelationReconstructible
  dsimp [parametricProvenanceConfiguration]
  dsimp [generatedStructuralFlipAtSearch]
  rw [
    dif_pos (parametricNegative_formula_matches_engine index),
    dif_neg (parametricNegative_decisions_mismatch index)
  ]
  intro impossible
  exact impossible rfl

/--
On the infinite, nonconstant, nonempty-residual family, relation
reconstructibility still cannot factor through residual syntax alone.
-/
theorem parametricRelationReconstructibility_not_factor_through_residuals :
    ¬ PredicateFactorsThrough
        eraseParametricProvenance
        ParametricRelationReconstructible := by
  exact
    predicate_not_factors_of_same_projection
      eraseParametricProvenance
      ParametricRelationReconstructible
      (.provenanceMismatch 0)
      (.reconstructible 0)
      (parametricProjection_same 0).symm
      (parametricNegative_not_reconstructible 0)
      (parametricPositive_reconstructible 0)

/-- Exact strengthened projection-loss package prepared for adversarial audit. -/
structure ParametricProvenanceProjectionLoss : Prop where
  sameAtEveryIndex :
    ∀ index,
      eraseParametricProvenance (.reconstructible index) =
        eraseParametricProvenance (.provenanceMismatch index)
  residualsNonempty :
    ∀ index,
      eraseParametricProvenance (.reconstructible index) ≠
        (([] : Cnf), ([] : Cnf))
  projectionChangesWithIndex :
    ∀ index,
      eraseParametricProvenance (.reconstructible index) ≠
        eraseParametricProvenance (.reconstructible (index + 1))
  positiveFound :
    ∀ index,
      ParametricRelationReconstructible (.reconstructible index)
  negativeMissing :
    ∀ index,
      ¬ ParametricRelationReconstructible (.provenanceMismatch index)
  relationLoss :
    ¬ PredicateFactorsThrough
        eraseParametricProvenance
        ParametricRelationReconstructible

theorem parametricProvenanceProjectionLoss :
    ParametricProvenanceProjectionLoss :=
  { sameAtEveryIndex := parametricProjection_same
    residualsNonempty := parametricProjection_nonempty
    projectionChangesWithIndex := parametricProjection_strict
    positiveFound := parametricPositive_reconstructible
    negativeMissing := parametricNegative_not_reconstructible
    relationLoss :=
      parametricRelationReconstructibility_not_factor_through_residuals }

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.ParametricProvenanceCase
#print axioms ConstitutiveSearch.SAT.parametricProvenanceConfiguration
#print axioms ConstitutiveSearch.SAT.eraseParametricProvenance
#print axioms ConstitutiveSearch.SAT.ParametricRelationReconstructible
#print axioms ConstitutiveSearch.SAT.parametricProjection_positive_exact
#print axioms ConstitutiveSearch.SAT.parametricProjection_negative_exact
#print axioms ConstitutiveSearch.SAT.parametricProjection_same
#print axioms ConstitutiveSearch.SAT.parametricProjection_nonempty
#print axioms ConstitutiveSearch.SAT.parametricIndex_ne_next
#print axioms ConstitutiveSearch.SAT.parametricResidualVar_strict
#print axioms ConstitutiveSearch.SAT.parametricResidualFormula_strict
#print axioms ConstitutiveSearch.SAT.parametricProjection_strict
#print axioms ConstitutiveSearch.SAT.parametricPositive_reconstructible
#print axioms ConstitutiveSearch.SAT.parametricNegative_formula_matches_engine
#print axioms ConstitutiveSearch.SAT.parametricNegative_not_reconstructible
#print axioms ConstitutiveSearch.SAT.parametricRelationReconstructibility_not_factor_through_residuals
#print axioms ConstitutiveSearch.SAT.ParametricProvenanceProjectionLoss
#print axioms ConstitutiveSearch.SAT.parametricProvenanceProjectionLoss
/- AXIOM_AUDIT_END -/
