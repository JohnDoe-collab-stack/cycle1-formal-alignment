import Init.Omega
import ConstitutiveSearch.SAT.ExplicitFamilyInputPolynomialProfile
import ConstitutiveSearch.SAT.TrajectoryDerivedClosureComplexity

/-!
# Sequential versus globally flattened closure accounting on F(n)

The explicit SAT family F(n) now supports two different ways of accounting for
the same certified trajectory.

Sequential constitutive execution:
* uses the direct sibling relation available at each constituted split;
* has exactly 2n direct relation-search calls;
* performs no TransportClosure search;
* has a complete input-polynomial constitutive profile.

Global trajectory-derived closure:
* reconstructs primitive generators, all split-state candidates and fuel from
  the same proof-relevant trajectory;
* therefore uses exactly 2n candidates and fuel n;
* its canonical recursive ClosureSearch primitive/composition budgets are not
  InputPolynomiallyBounded in the actual encoded size of F(n).

This is an accounting/search-regime separator.  The negative statements concern
the canonical recursive upper envelopes of the globally flattened closure
engine.  They are not lower bounds on the actual counters of every concrete
closure run.
-/

namespace ConstitutiveSearch

universe uGenerator

/--
If a positive-fuel closure query is already solved by the primitive relation
search, the bounded closure engine short-circuits immediately: exactly one
primitive query and no composition candidate are charged, independently of the
global candidate list and fuel magnitude.
-/
theorem searchTransportClosureBounded_primitiveHit_stats
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator)
    (candidates : List State)
    (fuel : Nat)
    (source target : State)
    (fuelPositive : 0 < fuel)
    (primitiveHit :
      primitive.find source target ≠ none) :
    let run :=
      searchTransportClosureBounded
        primitive
        candidates
        fuel
        source
        target
    run.stats.primitiveQueries = 1 ∧
      run.stats.compositionCandidates = 0 := by
  cases fuel with
  | zero =>
      omega
  | succ fuel =>
      cases h :
          primitive.find source target with
      | none =>
          exact False.elim (primitiveHit h)
      | some witness =>
          simp only [
            searchTransportClosureBounded,
            h,
            ClosureSearchStats.withPrimitiveQuery,
            ClosureSearchStats.zero
          ]

namespace SAT

/--
Evidence that the same certified F(n) trajectory has polynomial sequential
constitutive accounting but non-polynomial canonical budgets after global
closure flattening.
-/
structure SequentialGlobalClosureAccountingSeparator : Prop where
  sequentialProfilePolynomial :
    ConstitutiveProfileFamilyInputPolynomiallyBounded
      explicitFamilyConstitutiveProfile
  sequentialRelationFindExact :
    ∀ count : Nat,
      (explicitFamilyComplexityCounts count).relationFindCalls =
        2 * count
  sequentialClosurePrimitiveZero :
    ∀ count : Nat,
      (explicitFamilyComplexityCounts count).closurePrimitiveQueries =
        0
  sequentialClosureCandidatesZero :
    ∀ count : Nat,
      (explicitFamilyComplexityCounts count).closureCompositionCandidates =
        0
  globalCandidateCountExact :
    ∀ count : Nat,
      (explicitFamilyTrajectoryClosureCandidates count).length =
        2 * count
  globalFuelExact :
    ∀ count : Nat,
      explicitFamilyTrajectoryClosureFuel count =
        count
  globalPrimitiveBudgetNotInputPolynomial :
    ¬
      InputPolynomiallyBounded
        explicitFamilyInputBitSize
        explicitFamilyTrajectoryPrimitiveClosureBudget
  globalCompositionBudgetNotInputPolynomial :
    ¬
      InputPolynomiallyBounded
        explicitFamilyInputBitSize
        explicitFamilyTrajectoryCompositionClosureBudget

/-- The sequential/global accounting separator is realized by every F(n). -/
theorem explicitFamilySequentialGlobalClosureAccountingSeparator :
    SequentialGlobalClosureAccountingSeparator :=
  { sequentialProfilePolynomial :=
      explicitFamilyConstitutiveProfile_inputPolynomiallyBounded
    sequentialRelationFindExact := by
      intro count
      rfl
    sequentialClosurePrimitiveZero := by
      intro count
      rfl
    sequentialClosureCandidatesZero := by
      intro count
      rfl
    globalCandidateCountExact :=
      explicitFamilyTrajectoryClosureCandidates_length
    globalFuelExact :=
      explicitFamilyTrajectoryClosureFuel_eq
    globalPrimitiveBudgetNotInputPolynomial :=
      explicitFamilyTrajectoryPrimitiveClosureBudget_not_inputPolynomiallyBounded
    globalCompositionBudgetNotInputPolynomial :=
      explicitFamilyTrajectoryCompositionClosureBudget_not_inputPolynomiallyBounded }

/--
The sequential and global regimes are built from exactly the same certified
trajectory object; only the accounting/search organization changes.

The globally flattened candidate list and fuel are definitionally extracted
from that trajectory's splitCandidates and closureFuel.
-/
theorem explicitFamilySequentialGlobal_sameTrajectory
    (count : Nat) :
    explicitFamilyTrajectoryClosureCandidates count =
        (explicitFamilyResourceTrajectory count).trajectory.splitCandidates ∧
      explicitFamilyTrajectoryClosureFuel count =
        (explicitFamilyResourceTrajectory count).trajectory.closureFuel := by
  exact ⟨rfl, rfl⟩


/--
For every nonempty certified flip-symmetric trajectory, the closure query
corresponding to its first actual sibling split is a primitive hit.  Therefore
the globally available candidate list and fuel do not force exploration on
that constitutive query: the run charges one primitive query and zero
composition candidates.
-/
theorem trajectoryDerivedClosure_firstSibling_shortCircuit
    {rootFormula : Cnf}
    {parent finish :
      GeneratedStructuralBranchContext rootFormula}
    {length : Nat}
    (var : Var)
    (fresh :
      StructuralDecisionsAvoid
        var
        parent.context.decisions)
    (symmetric :
      FlipSymmetricAt
        parent.context.formula
        var)
    (tail :
      FlipSymmetricTrajectory
        (GeneratedStructuralBranchContext.child
          parent
          var
          true
          fresh)
        finish
        length) :
    let trajectory :=
      FlipSymmetricTrajectory.step
        var
        fresh
        symmetric
        tail
    let source :=
      GeneratedStructuralBranchContext.child
        parent
        var
        false
        fresh
    let target :=
      GeneratedStructuralBranchContext.child
        parent
        var
        true
        fresh
    let run :=
      searchTransportClosureBounded
        trajectory.primitiveSearch
        trajectory.splitCandidates
        trajectory.closureFuel
        source
        target
    run.stats.primitiveQueries = 1 ∧
      run.stats.compositionCandidates = 0 := by
  dsimp only
  apply
    searchTransportClosureBounded_primitiveHit_stats
  · change
      0 <
        Nat.succ
          tail.decisionVars.length
    exact Nat.zero_lt_succ _
  · exact
      FlipSymmetricTrajectory.primitiveSearch_finds_firstSibling
        var
        fresh
        symmetric
        tail

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.searchTransportClosureBounded_primitiveHit_stats
#print axioms ConstitutiveSearch.SAT.SequentialGlobalClosureAccountingSeparator
#print axioms ConstitutiveSearch.SAT.explicitFamilySequentialGlobalClosureAccountingSeparator
#print axioms ConstitutiveSearch.SAT.explicitFamilySequentialGlobal_sameTrajectory
#print axioms ConstitutiveSearch.SAT.trajectoryDerivedClosure_firstSibling_shortCircuit
/- AXIOM_AUDIT_END -/
