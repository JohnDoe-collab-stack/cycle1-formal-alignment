import ConstitutiveSearch.LocalSearchableCodeExecution
import ConstitutiveSearch.SAT.ComposedSearchableCode

/-!
# Candidate-free local execution of the constituted composed SAT code

The composed SAT benchmark already has a directly constituted two-atom code:
source -> middle -> target.

The generic local execution theorem removes the remaining global control data.
The code executes with:
* no candidate list;
* fuel one per primitive atom;
* exactly two primitive queries;
* zero composition-candidate inspections.

The endpoint direct primitive query still misses, so the same relation is a
genuine global composition requirement while remaining locally executable from
the constituted code.
-/

namespace ConstitutiveSearch
namespace SAT

/--
The directly constituted composed SAT code admits candidate-free local
sequential execution.
-/
theorem composedConstitutedCode_localSequentialExecution
    (count : Nat) :
    TransportCode.LocalSequentialExecution
      (composedPrimitiveSearch count)
      (composedConstitutedCode count) :=
  TransportCode.localSequentialExecution_of_searchable
    (composedPrimitiveSearch count)
    (composedConstitutedCode count)
    (composedConstitutedCode_searchable count)

/--
The direct endpoint miss and the constituted code jointly certify both global
composition need and candidate-free local execution.
-/
theorem composedConstitutedCode_globalNeed_and_localExecution
    (count : Nat) :
    TransportCode.GlobalNeedWithLocalExecution
      (composedPrimitiveSearch count)
      (composedConstitutedCode count) := by
  exact
    TransportCode.directMiss_searchableCode_hasLocalExecution
      (composedPrimitiveSearch count)
      (composedPrimitiveSearch_source_target_none count)
      (composedConstitutedCode count)
      (composedConstitutedCode_searchable count)
      (by
        rw [composedConstitutedCode_size]
        exact Nat.le_refl 2)

/--
The local execution has exactly two primitive queries and no composition
candidate, with no candidate list and unit fuel.
-/
theorem composedConstitutedCode_localStats
    (count : Nat) :
    ∃ path :
        PrimitiveHitPath
          (composedPrimitiveSearch count)
          (composedSource count)
          (composedTarget count),
      path.length = 2 ∧
        (path.sequentialStats
            []
            1).primitiveQueries = 2 ∧
        (path.sequentialStats
            []
            1).compositionCandidates = 0 := by
  rcases
      composedConstitutedCode_localSequentialExecution
        count with
    ⟨path,
      pathLength,
      primitiveExact,
      compositionExact⟩
  refine
    ⟨path, ?_, ?_, compositionExact⟩
  · calc
      path.length
          =
        (composedConstitutedCode count).size :=
          pathLength
      _ =
        2 :=
          composedConstitutedCode_size count
  · calc
      (path.sequentialStats
          []
          1).primitiveQueries
          =
        (composedConstitutedCode count).size :=
          primitiveExact
      _ =
        2 :=
          composedConstitutedCode_size count

/--
Compared with the global source-to-target closure query, the candidate-free
local execution is strictly cheaper in both recorded control-flow coordinates.
-/
theorem composedConstitutedCode_localGlobalGap
    (count : Nat) :
    ∃ path :
        PrimitiveHitPath
          (composedPrimitiveSearch count)
          (composedSource count)
          (composedTarget count),
      path.length = 2 ∧
        (path.sequentialStats
            []
            1).primitiveQueries <
          (composedClosureFuelTwo count).stats.primitiveQueries ∧
        (path.sequentialStats
            []
            1).compositionCandidates <
          (composedClosureFuelTwo count).stats.compositionCandidates := by
  rcases
      composedConstitutedCode_localStats
        count with
    ⟨path,
      lengthExact,
      primitiveExact,
      compositionExact⟩
  refine
    ⟨path,
      lengthExact,
      ?_,
      ?_⟩
  · rw [
      primitiveExact,
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
#print axioms ConstitutiveSearch.SAT.composedConstitutedCode_localSequentialExecution
#print axioms ConstitutiveSearch.SAT.composedConstitutedCode_globalNeed_and_localExecution
#print axioms ConstitutiveSearch.SAT.composedConstitutedCode_localStats
#print axioms ConstitutiveSearch.SAT.composedConstitutedCode_localGlobalGap
/- AXIOM_AUDIT_END -/
