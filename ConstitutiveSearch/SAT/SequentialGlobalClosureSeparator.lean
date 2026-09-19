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
-/
theorem explicitFamilySequentialGlobal_sameTrajectory
    (count : Nat) :
    explicitFamilyTrajectoryClosureFuel count =
        (explicitFamilyResourceTrajectory count).trajectory.length ∧
      (explicitFamilyTrajectoryClosureCandidates count).length =
        2 *
          (explicitFamilyResourceTrajectory count).trajectory.length := by
  constructor
  · calc
      explicitFamilyTrajectoryClosureFuel count
          =
        count :=
          explicitFamilyTrajectoryClosureFuel_eq count
      _ =
        (explicitFamilyResourceTrajectory count).trajectory.length := by
          symm
          exact
            (explicitFamilyResourceTrajectory count).trajectory_length
  · calc
      (explicitFamilyTrajectoryClosureCandidates count).length
          =
        2 * count :=
          explicitFamilyTrajectoryClosureCandidates_length count
      _ =
        2 *
          (explicitFamilyResourceTrajectory count).trajectory.length := by
            rw [
              (explicitFamilyResourceTrajectory count).trajectory_length
            ]

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.SequentialGlobalClosureAccountingSeparator
#print axioms ConstitutiveSearch.SAT.explicitFamilySequentialGlobalClosureAccountingSeparator
#print axioms ConstitutiveSearch.SAT.explicitFamilySequentialGlobal_sameTrajectory
/- AXIOM_AUDIT_END -/
