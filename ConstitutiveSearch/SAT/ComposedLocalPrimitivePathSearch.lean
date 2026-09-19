import ConstitutiveSearch.PrimitiveStateChainSearch
import ConstitutiveSearch.SAT.ComposedPrimitiveHitPath

/-!
# Local primitive-path reconstruction on the composed SAT benchmark

The composed SAT benchmark already constitutes the ordered states

  source -> middle -> target.

Instead of asking global ClosureSearch to discover a composition through an
unordered candidate list, this module searches only the two adjacent pairs of
that constituted state chain.

The local search reconstructs the same two primitive witnesses with:
* exactly two primitive queries;
* zero composition-candidate queries;
* a compiled transport code of size two.

The corresponding global source-to-target closure query uses three primitive
queries and one composition-candidate query.
-/

namespace ConstitutiveSearch
namespace SAT

/-- Ordered constituted state chain of the two-flip composition benchmark. -/
def composedPrimitiveStateChain
    (count : Nat) :
    PrimitiveStateChain
      (GeneratedStructuralBranchContext
        (explicitStackedSymmetricFamily count))
      (composedSource count)
      (composedTarget count) :=
  .step
    (composedMiddle count)
    (.step
      (composedTarget count)
      (.identity
        (composedTarget count)))

/-- The constituted chain has exactly two adjacent edges. -/
theorem composedPrimitiveStateChain_length
    (count : Nat) :
    (composedPrimitiveStateChain count).length =
      2 := by
  rfl

/-- Executable local adjacency search on the constituted chain. -/
def composedLocalPrimitivePathRun
    (count : Nat) :=
  searchPrimitiveStateChain
    (composedPrimitiveSearch count)
    (composedPrimitiveStateChain count)

/-- Both adjacent primitive searches succeed, so the local path is found. -/
theorem composedLocalPrimitivePathRun_found
    (count : Nat) :
    (composedLocalPrimitivePathRun count).path? ≠
      none := by
  rcases
      composedPrimitiveSearch_source_middle_some
        count with
    ⟨firstWitness, firstExact⟩
  rcases
      composedPrimitiveSearch_middle_target_some
        count with
    ⟨secondWitness, secondExact⟩
  unfold
    composedLocalPrimitivePathRun
    composedPrimitiveStateChain
  simp only [searchPrimitiveStateChain]
  rw [
    firstExact,
    secondExact
  ]
  intro impossible
  cases impossible

/-- Local path discovery executes exactly two primitive queries. -/
theorem composedLocalPrimitivePathRun_primitiveQueries
    (count : Nat) :
    (composedLocalPrimitivePathRun count).stats.primitiveQueries =
      2 := by
  cases found :
      (composedLocalPrimitivePathRun count).path? with
  | none =>
      exact
        False.elim
          ((composedLocalPrimitivePathRun_found
            count)
            found)
  | some path =>
      calc
        (composedLocalPrimitivePathRun count).stats.primitiveQueries
            =
          (composedPrimitiveStateChain count).length :=
            searchPrimitiveStateChain_found_primitiveQueries
              (composedPrimitiveSearch count)
              (composedPrimitiveStateChain count)
              found
        _ =
          2 :=
            composedPrimitiveStateChain_length count

/-- Local path discovery never enters composition-candidate search. -/
theorem composedLocalPrimitivePathRun_compositionCandidates
    (count : Nat) :
    (composedLocalPrimitivePathRun count).stats.compositionCandidates =
      0 :=
  searchPrimitiveStateChain_compositionCandidates_zero
    (composedPrimitiveSearch count)
    (composedPrimitiveStateChain count)

/-- The locally reconstructed path compiles to a transport code of size two. -/
theorem composedLocalPrimitivePathRun_codeSize
    (count : Nat) :
    match
      (composedLocalPrimitivePathRun count).path? with
    | none =>
        False
    | some path =>
        path.toTransportCode.size = 2 := by
  cases found :
      (composedLocalPrimitivePathRun count).path? with
  | none =>
      exact
        False.elim
          ((composedLocalPrimitivePathRun_found
            count)
            found)
  | some path =>
      calc
        path.toTransportCode.size
            =
          (composedPrimitiveStateChain count).length :=
            searchPrimitiveStateChain_found_code_size
              (composedPrimitiveSearch count)
              (composedPrimitiveStateChain count)
              found
        _ =
          2 :=
            composedPrimitiveStateChain_length count

/-- Local constituted-chain discovery uses fewer primitive queries than global closure. -/
theorem composedLocalPrimitivePathRun_primitiveQueries_lt_global
    (count : Nat) :
    (composedLocalPrimitivePathRun count).stats.primitiveQueries <
      (composedClosureFuelTwo count).stats.primitiveQueries := by
  rw [
    composedLocalPrimitivePathRun_primitiveQueries,
    composedClosureFuelTwo_primitiveQueries
  ]
  decide

/-- Local constituted-chain discovery avoids the composition candidate used globally. -/
theorem composedLocalPrimitivePathRun_compositionCandidates_lt_global
    (count : Nat) :
    (composedLocalPrimitivePathRun count).stats.compositionCandidates <
      (composedClosureFuelTwo count).stats.compositionCandidates := by
  rw [
    composedLocalPrimitivePathRun_compositionCandidates,
    composedClosureFuelTwo_compositionCandidates
  ]
  decide

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.composedPrimitiveStateChain
#print axioms ConstitutiveSearch.SAT.composedPrimitiveStateChain_length
#print axioms ConstitutiveSearch.SAT.composedLocalPrimitivePathRun
#print axioms ConstitutiveSearch.SAT.composedLocalPrimitivePathRun_found
#print axioms ConstitutiveSearch.SAT.composedLocalPrimitivePathRun_primitiveQueries
#print axioms ConstitutiveSearch.SAT.composedLocalPrimitivePathRun_compositionCandidates
#print axioms ConstitutiveSearch.SAT.composedLocalPrimitivePathRun_codeSize
#print axioms ConstitutiveSearch.SAT.composedLocalPrimitivePathRun_primitiveQueries_lt_global
#print axioms ConstitutiveSearch.SAT.composedLocalPrimitivePathRun_compositionCandidates_lt_global
/- AXIOM_AUDIT_END -/
