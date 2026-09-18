import ConstitutiveSearch.SAT.ParametricComposedClosure

/-!
# Direct-versus-composed width on the parametric SAT composition family

The primitive engine cannot relate the diagonal source/target pair in either
direction, so that pair is search-irreducible at width two.

The same announced primitive generators admit an explicit two-atom closure code
through the generated middle state.  The bounded closure engine with that
single candidate and fuel two also finds a source-to-target code.  Interpreting
the explicit composed code gives an acceptance-preserving reduction of the same
pair to a singleton.

This is a separator for the declared primitive/closure interfaces.  It is not
an intrinsic SAT-hardness claim.
-/

namespace ConstitutiveSearch
namespace SAT

/-- Flipping the first fresh variable from target reaches the alternate state. -/
def composedTargetAlternateRelation
    (count : Nat) :
    GeneratedStructuralFlipAtRelation
      (composedFirstVar count)
      (composedTarget count)
      (composedAlternate count) :=
  composedFlipFirstRelation
    count
    true
    true

/-- Flipping the second fresh variable from target reaches the middle state. -/
def composedTargetMiddleRelation
    (count : Nat) :
    GeneratedStructuralFlipAtRelation
      (composedSecondVar count)
      (composedTarget count)
      (composedMiddle count) :=
  composedFlipSecondRelation
    count
    true
    true

/-- Target and source cannot be related by the first announced primitive flip. -/
theorem composedTargetSource_not_first
    (count : Nat) :
    (composedSource count).context.decisions ≠
      flipStructuralDecisionsAt
        (composedFirstVar count)
        (composedTarget count).context.decisions := by
  intro exactHistory
  have sourceAlternate :
      (composedSource count).context.decisions =
        (composedAlternate count).context.decisions :=
    Eq.trans
      exactHistory
      (composedTargetAlternateRelation count).decisionsExact.symm
  change
    ({ var := composedSecondVar count, value := false } ::
      { var := composedFirstVar count, value := false } ::
      (composedFamilyParent count).context.decisions) =
    ({ var := composedSecondVar count, value := true } ::
      { var := composedFirstVar count, value := false } ::
      (composedFamilyParent count).context.decisions) at sourceAlternate
  injection sourceAlternate with headEqual tailEqual
  have valueEqual :
      false = true :=
    congrArg
      StructuralBranchDecision.value
      headEqual
  cases valueEqual

/-- Target and source cannot be related by the second announced primitive flip. -/
theorem composedTargetSource_not_second
    (count : Nat) :
    (composedSource count).context.decisions ≠
      flipStructuralDecisionsAt
        (composedSecondVar count)
        (composedTarget count).context.decisions := by
  intro exactHistory
  have sourceMiddle :
      (composedSource count).context.decisions =
        (composedMiddle count).context.decisions :=
    Eq.trans
      exactHistory
      (composedTargetMiddleRelation count).decisionsExact.symm
  change
    ({ var := composedSecondVar count, value := false } ::
      { var := composedFirstVar count, value := false } ::
      (composedFamilyParent count).context.decisions) =
    ({ var := composedSecondVar count, value := false } ::
      { var := composedFirstVar count, value := true } ::
      (composedFamilyParent count).context.decisions) at sourceMiddle
  injection sourceMiddle with headEqual tailEqual
  injection tailEqual with firstEqual restEqual
  have valueEqual :
      false = true :=
    congrArg
      StructuralBranchDecision.value
      firstEqual
  cases valueEqual

/-- No announced primitive relation directly connects target back to source. -/
theorem composedPrimitiveSearch_target_source_none
    (count : Nat) :
    (composedPrimitiveSearch count).find
        (composedTarget count)
        (composedSource count) =
      none := by
  dsimp [composedPrimitiveSearch]
  rw [
    generatedStructuralFlipAtSearch_none_of_decisions_ne
      (composedTargetSource_not_first count)
  ]
  rw [
    generatedStructuralFlipAtSearch_none_of_decisions_ne
      (composedTargetSource_not_second count)
  ]

/-- The direct two-state SAT frontier. -/
def composedDirectFrontier
    (count : Nat) :
    List
      (GeneratedStructuralBranchContext
        (explicitStackedSymmetricFamily count)) :=
  [composedSource count, composedTarget count]

/-- Direct primitive search leaves the diagonal pair irreducible. -/
theorem composedDirectFrontier_irreducible
    (count : Nat) :
    SearchIrreducible
      (composedPrimitiveSearch count)
      (composedDirectFrontier count) := by
  unfold composedDirectFrontier
  exact
    SearchIrreducible.pair
      (composedPrimitiveSearch count)
      (composedSource count)
      (composedTarget count)
      (composedPrimitiveSearch_source_target_none count)
      (composedPrimitiveSearch_target_source_none count)

/-- Direct primitive width is exactly two. -/
theorem composedDirectFrontier_width
    (count : Nat) :
    (composedDirectFrontier count).length = 2 := by
  rfl

/-- Packaged first primitive witness used by the closure code. -/
def composedSourceMiddleWitness
    (count : Nat) :
    GeneratedStructuralFlipWitness
      (composedSource count)
      (composedMiddle count) :=
  { var := composedFirstVar count
    relation := composedSourceMiddleRelation count }

/-- Packaged second primitive witness used by the closure code. -/
def composedMiddleTargetWitness
    (count : Nat) :
    GeneratedStructuralFlipWitness
      (composedMiddle count)
      (composedTarget count) :=
  { var := composedSecondVar count
    relation := composedMiddleTargetRelation count }

/-- Explicit two-atom source-to-target code in the free transport closure. -/
def composedSourceTargetCode
    (count : Nat) :
    TransportClosure
      (GeneratedStructuralFlipWitness
        (rootFormula :=
          explicitStackedSymmetricFamily count))
      (composedSource count)
      (composedTarget count) :=
  TransportClosure.compose
    (TransportClosure.ofGenerator
      (composedSourceMiddleWitness count))
    (TransportClosure.ofGenerator
      (composedMiddleTargetWitness count))

/-- The explicit closure certificate has exactly two primitive atoms. -/
theorem composedSourceTargetCode_size
    (count : Nat) :
    (composedSourceTargetCode count).size = 2 := by
  rfl

/-- Executable closure search used for the composed width comparison. -/
def composedBoundedClosureSearch
    (count : Nat) :
    RelationSearch
      (TransportClosure
        (GeneratedStructuralFlipWitness
          (rootFormula :=
            explicitStackedSymmetricFamily count))) :=
  boundedTransportClosureSearch
    (composedPrimitiveSearch count)
    [composedMiddle count]
    2

/-- The bounded closure engine finds a source-to-target code on this family. -/
theorem composedBoundedClosureSearch_source_target_present
    (count : Nat) :
    (composedBoundedClosureSearch count).find
        (composedSource count)
        (composedTarget count) ≠
      none := by
  change
    (composedClosureFuelTwo count).code? ≠
      none
  exact
    composedClosureFuelTwo_found count

/-- Hardened closure action generated by the same primitive flip witnesses. -/
def composedClosureAction
    (count : Nat) :
    AcceptedRelationalAction
      (generatedStructuralBranchSystem
        (explicitStackedSymmetricFamily count))
      (TransportClosure
        (GeneratedStructuralFlipWitness
          (rootFormula :=
            explicitStackedSymmetricFamily count))) :=
  transportClosureAction
    (generatedStructuralFlipWitnessAction
      (explicitStackedSymmetricFamily count))

/--
The explicit composed code safely absorbs source into target while preserving
frontier viability in both directions.
-/
def composedClosurePreservation
    (count : Nat) :
    AcceptedFrontierPreservation
      (generatedStructuralBranchSystem
        (explicitStackedSymmetricFamily count))
      [composedSource count, composedTarget count]
      [composedTarget count] :=
  (composedClosureAction count).absorbFirstIntoSecond
    (composedSourceTargetCode count)

/--
Certified singleton reduction under the same bounded closure search that is
proved above to find a source-to-target code.
-/
def composedClosureReduction
    (count : Nat) :
    AcceptedIrreducibleFrontierReduction
      (system :=
        generatedStructuralBranchSystem
          (explicitStackedSymmetricFamily count))
      (composedBoundedClosureSearch count)
      [composedSource count, composedTarget count] :=
  { retained := [composedTarget count]
    preservation :=
      composedClosurePreservation count
    irreducible :=
      SearchIrreducible.singleton
        (composedBoundedClosureSearch count)
        (composedTarget count) }

/-- Closure-certified width is exactly one. -/
theorem composedClosureReduction_width
    (count : Nat) :
    (composedClosureReduction count).width = 1 := by
  rfl

/-- The composed reduction strictly improves the direct primitive width. -/
theorem composedClosure_width_strictly_smaller
    (count : Nat) :
    (composedClosureReduction count).width <
      (composedDirectFrontier count).length := by
  rw [
    composedClosureReduction_width,
    composedDirectFrontier_width
  ]
  exact Nat.lt_succ_self 1

/-- The closure reduction preserves frontier viability exactly. -/
theorem composedClosureReduction_viable_iff
    (count : Nat) :
    FrontierViable
        (generatedStructuralBranchSystem
          (explicitStackedSymmetricFamily count))
        [composedSource count, composedTarget count] ↔
      FrontierViable
        (generatedStructuralBranchSystem
          (explicitStackedSymmetricFamily count))
        [composedTarget count] :=
  (composedClosureReduction count).viable_iff

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.composedTargetAlternateRelation
#print axioms ConstitutiveSearch.SAT.composedTargetMiddleRelation
#print axioms ConstitutiveSearch.SAT.composedPrimitiveSearch_target_source_none
#print axioms ConstitutiveSearch.SAT.composedDirectFrontier
#print axioms ConstitutiveSearch.SAT.composedDirectFrontier_irreducible
#print axioms ConstitutiveSearch.SAT.composedDirectFrontier_width
#print axioms ConstitutiveSearch.SAT.composedSourceMiddleWitness
#print axioms ConstitutiveSearch.SAT.composedMiddleTargetWitness
#print axioms ConstitutiveSearch.SAT.composedSourceTargetCode
#print axioms ConstitutiveSearch.SAT.composedSourceTargetCode_size
#print axioms ConstitutiveSearch.SAT.composedBoundedClosureSearch
#print axioms ConstitutiveSearch.SAT.composedBoundedClosureSearch_source_target_present
#print axioms ConstitutiveSearch.SAT.composedClosureAction
#print axioms ConstitutiveSearch.SAT.composedClosurePreservation
#print axioms ConstitutiveSearch.SAT.composedClosureReduction
#print axioms ConstitutiveSearch.SAT.composedClosureReduction_width
#print axioms ConstitutiveSearch.SAT.composedClosure_width_strictly_smaller
#print axioms ConstitutiveSearch.SAT.composedClosureReduction_viable_iff
/- AXIOM_AUDIT_END -/
