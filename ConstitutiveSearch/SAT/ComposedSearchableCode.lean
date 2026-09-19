import ConstitutiveSearch.SearchableTransportCode
import ConstitutiveSearch.SAT.SequentialComposedExecutionSeparator

/-!
# Direct constituted code for the composed SAT benchmark

The composed SAT benchmark already contains two certified primitive structural
relations:

  source -> middle
  middle -> target.

This module packages them directly as one TransportCode, without invoking
global ClosureSearch.

The code is searchable by the announced composedPrimitiveSearch on exactly its
two atoms.  Therefore:
* the global source-to-target composition requirement is certified from the
  direct miss plus this constituted code;
* the code can be executed sequentially with exactly two primitive queries and
  zero composition-candidate inspections;
* no global closure search is needed to discover the code before obtaining that
  sequential execution.
-/

namespace ConstitutiveSearch
namespace SAT

/-- First certified generator witness of the constituted two-edge code. -/
def composedConstitutedFirstWitness
    (count : Nat) :
    GeneratedStructuralFlipWitness
      (rootFormula :=
        explicitStackedSymmetricFamily count)
      (composedSource count)
      (composedMiddle count) :=
  { var := composedFirstVar count
    relation :=
      composedSourceMiddleRelation count }

/-- Second certified generator witness of the constituted two-edge code. -/
def composedConstitutedSecondWitness
    (count : Nat) :
    GeneratedStructuralFlipWitness
      (rootFormula :=
        explicitStackedSymmetricFamily count)
      (composedMiddle count)
      (composedTarget count) :=
  { var := composedSecondVar count
    relation :=
      composedMiddleTargetRelation count }

/--
The composed endpoint transport code is built directly from the two certified
primitive witnesses.
-/
def composedConstitutedCode
    (count : Nat) :
    TransportClosure
      (GeneratedStructuralFlipWitness
        (rootFormula :=
          explicitStackedSymmetricFamily count))
      (composedSource count)
      (composedTarget count) :=
  TransportClosure.compose
    (TransportClosure.ofGenerator
      (composedConstitutedFirstWitness count))
    (TransportClosure.ofGenerator
      (composedConstitutedSecondWitness count))

/-- The directly constituted code has exactly two primitive atoms. -/
theorem composedConstitutedCode_size
    (count : Nat) :
    (composedConstitutedCode count).size =
      2 := by
  rfl

/--
Each atom of the directly constituted code is executable by the announced
primitive search.
-/
theorem composedConstitutedCode_searchable
    (count : Nat) :
    (composedConstitutedCode count).SearchableBy
      (composedPrimitiveSearch count) := by
  unfold composedConstitutedCode
  change
    (composedPrimitiveSearch count).find
          (composedSource count)
          (composedMiddle count) ≠
        none ∧
      (composedPrimitiveSearch count).find
          (composedMiddle count)
          (composedTarget count) ≠
        none
  constructor
  · rcases
      composedPrimitiveSearch_source_middle_some
        count with
      ⟨witness, exactFind⟩
    rw [exactFind]
    intro impossible
    cases impossible
  · rcases
      composedPrimitiveSearch_middle_target_some
        count with
      ⟨witness, exactFind⟩
    rw [exactFind]
    intro impossible
    cases impossible

/--
The global composition requirement is certified directly from the constituted
code and the direct primitive miss, with no global closure run.
-/
theorem composedGlobalCompositionRequired_fromConstitutedCode
    (count : Nat) :
    PrimitiveHitPath.GlobalCompositionRequired
      (composedPrimitiveSearch count)
      (composedSource count)
      (composedTarget count) := by
  apply
    (PrimitiveHitPath.globalCompositionRequired_iff_searchableCode
      (composedPrimitiveSearch count)
      (composedSource count)
      (composedTarget count)).2
  exact
    ⟨composedPrimitiveSearch_source_target_none count,
      ⟨composedConstitutedCode count,
        composedConstitutedCode_searchable count,
        by
          rw [composedConstitutedCode_size]
          exact Nat.le_refl 2⟩⟩

/--
The directly constituted code has a sequential execution with exactly two
primitive queries and zero composition-candidate inspections.
-/
theorem composedConstitutedCode_sequentialExecution
    (count : Nat) :
    ∃ path :
        PrimitiveHitPath
          (composedPrimitiveSearch count)
          (composedSource count)
          (composedTarget count),
      path.length =
          (composedConstitutedCode count).size ∧
        (path.sequentialStats
            [composedMiddle count]
            2).primitiveQueries =
          (composedConstitutedCode count).size ∧
        (path.sequentialStats
            [composedMiddle count]
            2).compositionCandidates =
          0 :=
  (composedConstitutedCode count).hasSequentialExecution_of_searchable
    (composedPrimitiveSearch count)
    [composedMiddle count]
    2
    (by decide)
    (composedConstitutedCode_searchable count)

/--
The directly constituted sequential execution is strictly cheaper in the two
recorded control-flow coordinates than the global closure query.
-/
theorem composedConstitutedCode_executionGap
    (count : Nat) :
    ∃ path :
        PrimitiveHitPath
          (composedPrimitiveSearch count)
          (composedSource count)
          (composedTarget count),
      path.length = 2 ∧
        (path.sequentialStats
            [composedMiddle count]
            2).primitiveQueries <
          (composedClosureFuelTwo count).stats.primitiveQueries ∧
        (path.sequentialStats
            [composedMiddle count]
            2).compositionCandidates <
          (composedClosureFuelTwo count).stats.compositionCandidates := by
  rcases
      composedConstitutedCode_sequentialExecution
        count with
    ⟨path,
      pathLength,
      primitiveExact,
      compositionExact⟩
  have codeSize :=
    composedConstitutedCode_size count
  refine
    ⟨path, ?_, ?_, ?_⟩
  · rw [pathLength, codeSize]
  · rw [
      primitiveExact,
      codeSize,
      composedClosureFuelTwo_primitiveQueries
    ]
    decide
  · rw [
      compositionExact,
      composedClosureFuelTwo_compositionCandidates
    ]
    decide

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.composedConstitutedFirstWitness
#print axioms ConstitutiveSearch.SAT.composedConstitutedSecondWitness
#print axioms ConstitutiveSearch.SAT.composedConstitutedCode
#print axioms ConstitutiveSearch.SAT.composedConstitutedCode_size
#print axioms ConstitutiveSearch.SAT.composedConstitutedCode_searchable
#print axioms ConstitutiveSearch.SAT.composedGlobalCompositionRequired_fromConstitutedCode
#print axioms ConstitutiveSearch.SAT.composedConstitutedCode_sequentialExecution
#print axioms ConstitutiveSearch.SAT.composedConstitutedCode_executionGap
/- AXIOM_AUDIT_END -/
