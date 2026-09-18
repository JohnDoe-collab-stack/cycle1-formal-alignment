import ConstitutiveSearch.ClosureSearchCosts
import ConstitutiveSearch.SAT.ParametricComposedFamily

/-!
# Executable bounded closure on the parametric composed SAT family

For every n, direct primitive search from source to target fails, while the
announced two-edge path source -> middle -> target exists.  This module connects
that separator to the executable bounded closure engine and its cost counters.
-/

namespace ConstitutiveSearch
namespace SAT

theorem composedPrimitiveSearch_source_middle_some
    (count : Nat) :
    ∃ witness,
      (composedPrimitiveSearch count).find
          (composedSource count)
          (composedMiddle count) =
        some witness := by
  cases found :
      (composedPrimitiveSearch count).find
        (composedSource count)
        (composedMiddle count) with
  | none =>
      exact False.elim
        ((composedPrimitiveSearch_source_middle_present count) found)
  | some witness =>
      exact ⟨witness, found⟩

theorem composedPrimitiveSearch_middle_target_some
    (count : Nat) :
    ∃ witness,
      (composedPrimitiveSearch count).find
          (composedMiddle count)
          (composedTarget count) =
        some witness := by
  cases found :
      (composedPrimitiveSearch count).find
        (composedMiddle count)
        (composedTarget count) with
  | none =>
      exact False.elim
        ((composedPrimitiveSearch_middle_target_present count) found)
  | some witness =>
      exact ⟨witness, found⟩

def composedClosureFuelOne
    (count : Nat) :=
  searchTransportClosureBounded
    (composedPrimitiveSearch count)
    [composedMiddle count]
    1
    (composedSource count)
    (composedTarget count)

def composedClosureFuelTwo
    (count : Nat) :=
  searchTransportClosureBounded
    (composedPrimitiveSearch count)
    [composedMiddle count]
    2
    (composedSource count)
    (composedTarget count)

theorem composedClosureFuelOne_not_found
    (count : Nat) :
    (composedClosureFuelOne count).code? = none := by
  simp [
    composedClosureFuelOne,
    searchTransportClosureBounded,
    searchClosureViaCandidates,
    composedPrimitiveSearch_source_target_none
  ]

theorem composedClosureFuelTwo_found
    (count : Nat) :
    (composedClosureFuelTwo count).code? ≠ none := by
  rcases composedPrimitiveSearch_source_middle_some count with
    ⟨firstWitness, firstExact⟩
  rcases composedPrimitiveSearch_middle_target_some count with
    ⟨secondWitness, secondExact⟩
  simp [
    composedClosureFuelTwo,
    searchTransportClosureBounded,
    searchClosureViaCandidates,
    composedPrimitiveSearch_source_target_none,
    firstExact,
    secondExact
  ]

theorem composedClosureFuelTwo_code_size
    (count : Nat) :
    match (composedClosureFuelTwo count).code? with
    | some code => code.size = 2
    | none => False := by
  rcases composedPrimitiveSearch_source_middle_some count with
    ⟨firstWitness, firstExact⟩
  rcases composedPrimitiveSearch_middle_target_some count with
    ⟨secondWitness, secondExact⟩
  simp [
    composedClosureFuelTwo,
    searchTransportClosureBounded,
    searchClosureViaCandidates,
    composedPrimitiveSearch_source_target_none,
    firstExact,
    secondExact,
    TransportClosure.ofGenerator,
    TransportClosure.compose,
    TransportCode.size
  ]

theorem composedClosureFuelTwo_primitiveQueries
    (count : Nat) :
    (composedClosureFuelTwo count).stats.primitiveQueries = 3 := by
  rcases composedPrimitiveSearch_source_middle_some count with
    ⟨firstWitness, firstExact⟩
  rcases composedPrimitiveSearch_middle_target_some count with
    ⟨secondWitness, secondExact⟩
  simp [
    composedClosureFuelTwo,
    searchTransportClosureBounded,
    searchClosureViaCandidates,
    composedPrimitiveSearch_source_target_none,
    firstExact,
    secondExact,
    ClosureSearchStats.zero,
    ClosureSearchStats.combine,
    ClosureSearchStats.withPrimitiveQuery,
    ClosureSearchStats.withCompositionCandidate
  ]

theorem composedClosureFuelTwo_compositionCandidates
    (count : Nat) :
    (composedClosureFuelTwo count).stats.compositionCandidates = 1 := by
  rcases composedPrimitiveSearch_source_middle_some count with
    ⟨firstWitness, firstExact⟩
  rcases composedPrimitiveSearch_middle_target_some count with
    ⟨secondWitness, secondExact⟩
  simp [
    composedClosureFuelTwo,
    searchTransportClosureBounded,
    searchClosureViaCandidates,
    composedPrimitiveSearch_source_target_none,
    firstExact,
    secondExact,
    ClosureSearchStats.zero,
    ClosureSearchStats.combine,
    ClosureSearchStats.withPrimitiveQuery,
    ClosureSearchStats.withCompositionCandidate
  ]

theorem composedClosureFuelTwo_primitiveQueries_le_budget
    (count : Nat) :
    (composedClosureFuelTwo count).stats.primitiveQueries ≤
      closurePrimitiveQueryBudget 1 2 := by
  simpa [composedClosureFuelTwo] using
    searchTransportClosureBounded_primitiveQueries_le
      (composedPrimitiveSearch count)
      [composedMiddle count]
      2
      (composedSource count)
      (composedTarget count)

theorem composedClosureFuelTwo_compositionCandidates_le_budget
    (count : Nat) :
    (composedClosureFuelTwo count).stats.compositionCandidates ≤
      closureCompositionCandidateBudget 1 2 := by
  simpa [composedClosureFuelTwo] using
    searchTransportClosureBounded_compositionCandidates_le
      (composedPrimitiveSearch count)
      [composedMiddle count]
      2
      (composedSource count)
      (composedTarget count)

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.composedPrimitiveSearch_source_middle_some
#print axioms ConstitutiveSearch.SAT.composedPrimitiveSearch_middle_target_some
#print axioms ConstitutiveSearch.SAT.composedClosureFuelOne
#print axioms ConstitutiveSearch.SAT.composedClosureFuelTwo
#print axioms ConstitutiveSearch.SAT.composedClosureFuelOne_not_found
#print axioms ConstitutiveSearch.SAT.composedClosureFuelTwo_found
#print axioms ConstitutiveSearch.SAT.composedClosureFuelTwo_code_size
#print axioms ConstitutiveSearch.SAT.composedClosureFuelTwo_primitiveQueries
#print axioms ConstitutiveSearch.SAT.composedClosureFuelTwo_compositionCandidates
#print axioms ConstitutiveSearch.SAT.composedClosureFuelTwo_primitiveQueries_le_budget
#print axioms ConstitutiveSearch.SAT.composedClosureFuelTwo_compositionCandidates_le_budget
/- AXIOM_AUDIT_END -/
