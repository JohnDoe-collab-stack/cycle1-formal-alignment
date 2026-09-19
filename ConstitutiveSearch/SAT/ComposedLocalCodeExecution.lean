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
    PrimitiveHitPath.GlobalCompositionRequired
        (composedPrimitiveSearch count)
        (composedSource count)
        (composedTarget count) ∧
      TransportCode.LocalSequentialExecution
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
    let execution :=
      composedConstitutedCode_localSequentialExecution
        count
    (execution.path.sequentialStats
        []
        1).primitiveQueries = 2 ∧
      (execution.path.sequentialStats
        []
        1).compositionCandidates = 0 := by
  dsimp only
  have execution :=
    composedConstitutedCode_localSequentialExecution
      count
  constructor
  · calc
      (execution.path.sequentialStats
          []
          1).primitiveQueries
          =
        (composedConstitutedCode count).size :=
          execution.primitiveQueries
      _ =
        2 :=
          composedConstitutedCode_size count
  · exact execution.compositionCandidates

/--
Compared with the global source-to-target closure query, the candidate-free
local execution is strictly cheaper in both recorded control-flow coordinates.
-/
theorem composedConstitutedCode_localGlobalGap
    (count : Nat) :
    let execution :=
      composedConstitutedCode_localSequentialExecution
        count
    (execution.path.sequentialStats
        []
        1).primitiveQueries <
        (composedClosureFuelTwo count).stats.primitiveQueries ∧
      (execution.path.sequentialStats
        []
        1).compositionCandidates <
        (composedClosureFuelTwo count).stats.compositionCandidates := by
  dsimp only
  have localStats :=
    composedConstitutedCode_localStats count
  constructor
  · rw [
      localStats.1,
      composedClosureFuelTwo_primitiveQueries
    ]
    decide
  · rw [
      localStats.2,
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
