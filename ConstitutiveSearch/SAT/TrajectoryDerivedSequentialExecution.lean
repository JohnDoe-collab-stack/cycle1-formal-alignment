import ConstitutiveSearch.SAT.SequentialGlobalClosureSeparator

/-!
# Sequential execution of trajectory-derived closure queries

The globally flattened trajectory-derived closure schedule has a
non-input-polynomial canonical recursive budget on F(n).  That budget is only
an upper envelope.

This module measures a different object: the closure runs actually issued by
the constitutive trajectory when, at each nonterminal step, it queries the
certified sibling relation produced by that step.

For each suffix trajectory:
* primitive variables, candidates and fuel are reconstructed from that suffix;
* the current sibling query is a primitive hit;
* ClosureSearch therefore charges exactly one primitive query and zero
  composition candidates.

Summing these actual runs along a trajectory of length n gives exactly:
* n primitive queries;
* 0 composition candidates.

On F(n), these counters are input-polynomial in the concrete encoded input
size.  This formally separates the executed sequential constitutive schedule
from the non-polynomial recursive envelope of one globally flattened closure
domain.
-/

namespace ConstitutiveSearch
namespace SAT

namespace FlipSymmetricTrajectory

/--
Stats of the actual closure run used to query the first sibling relation of one
nonempty certified trajectory.
-/
def firstSiblingClosureStats
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
    ClosureSearchStats :=
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
  (searchTransportClosureBounded
    trajectory.primitiveSearch
    trajectory.splitCandidates
    trajectory.closureFuel
    source
    target).stats

/-- Every first-sibling closure run is exactly a 1/0 short circuit. -/
theorem firstSiblingClosureStats_exact
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
    (firstSiblingClosureStats
        var
        fresh
        symmetric
        tail).primitiveQueries = 1 ∧
      (firstSiblingClosureStats
        var
        fresh
        symmetric
        tail).compositionCandidates = 0 := by
  simpa only [
    firstSiblingClosureStats
  ] using
    trajectoryDerivedClosure_firstSibling_shortCircuit
      var
      fresh
      symmetric
      tail

/--
Aggregate the actually executed first-sibling closure runs along the complete
trajectory.  Each recursive suffix reconstructs its own remaining provenance,
candidate list and fuel.
-/
def sequentialDerivedClosureStats
    {rootFormula : Cnf}
    {start finish :
      GeneratedStructuralBranchContext rootFormula}
    {length : Nat}
    (trajectory :
      FlipSymmetricTrajectory start finish length) :
    ClosureSearchStats :=
  match trajectory with
  | .done _ =>
      ClosureSearchStats.zero
  | .step var fresh symmetric tail =>
      ClosureSearchStats.combine
        (firstSiblingClosureStats
          var
          fresh
          symmetric
          tail)
        tail.sequentialDerivedClosureStats

/-- Exactly one primitive closure query is executed per constitutive step. -/
theorem sequentialDerivedClosureStats_primitiveQueries
    {rootFormula : Cnf}
    {start finish :
      GeneratedStructuralBranchContext rootFormula}
    {length : Nat}
    (trajectory :
      FlipSymmetricTrajectory start finish length) :
    trajectory.sequentialDerivedClosureStats.primitiveQueries =
      length := by
  induction trajectory with
  | done state =>
      rfl
  | step var fresh symmetric tail inductionHypothesis =>
      have stepStats :=
        firstSiblingClosureStats_exact
          var
          fresh
          symmetric
          tail
      change
        (firstSiblingClosureStats
            var
            fresh
            symmetric
            tail).primitiveQueries +
            tail.sequentialDerivedClosureStats.primitiveQueries =
          _ + 1
      rw [
        stepStats.1,
        inductionHypothesis
      ]
      exact Nat.add_comm 1 _

/-- No composition candidate is inspected by the executed sibling-query sequence. -/
theorem sequentialDerivedClosureStats_compositionCandidates
    {rootFormula : Cnf}
    {start finish :
      GeneratedStructuralBranchContext rootFormula}
    {length : Nat}
    (trajectory :
      FlipSymmetricTrajectory start finish length) :
    trajectory.sequentialDerivedClosureStats.compositionCandidates =
      0 := by
  induction trajectory with
  | done state =>
      rfl
  | step var fresh symmetric tail inductionHypothesis =>
      have stepStats :=
        firstSiblingClosureStats_exact
          var
          fresh
          symmetric
          tail
      change
        (firstSiblingClosureStats
            var
            fresh
            symmetric
            tail).compositionCandidates +
            tail.sequentialDerivedClosureStats.compositionCandidates =
          0
      rw [
        stepStats.2,
        inductionHypothesis
      ]

end FlipSymmetricTrajectory

/-- Actual sequential trajectory-derived closure stats for F(n). -/
def explicitFamilySequentialDerivedClosureStats
    (count : Nat) :
    ClosureSearchStats :=
  (explicitFamilyResourceTrajectory count).trajectory.sequentialDerivedClosureStats

/-- F(n) executes exactly n primitive sibling closure queries. -/
theorem explicitFamilySequentialDerivedClosureStats_primitiveQueries
    (count : Nat) :
    (explicitFamilySequentialDerivedClosureStats count).primitiveQueries =
      count :=
  FlipSymmetricTrajectory.sequentialDerivedClosureStats_primitiveQueries
    (explicitFamilyResourceTrajectory count).trajectory

/-- F(n) executes no composition candidate in this sequential schedule. -/
theorem explicitFamilySequentialDerivedClosureStats_compositionCandidates
    (count : Nat) :
    (explicitFamilySequentialDerivedClosureStats count).compositionCandidates =
      0 :=
  FlipSymmetricTrajectory.sequentialDerivedClosureStats_compositionCandidates
    (explicitFamilyResourceTrajectory count).trajectory

/--
The actually executed primitive-query counter of the sequential derived
schedule is input-polynomial in the real binary size of F(n).
-/
theorem explicitFamilySequentialDerivedClosurePrimitive_inputPolynomiallyBounded :
    InputPolynomiallyBounded
      explicitFamilyInputBitSize
      (fun count =>
        (explicitFamilySequentialDerivedClosureStats count).primitiveQueries) := by
  refine
    ⟨CostPolynomial.input, ?_⟩
  intro count
  change
    (explicitFamilySequentialDerivedClosureStats count).primitiveQueries ≤
      explicitFamilyInputBitSize count
  rw [
    explicitFamilySequentialDerivedClosureStats_primitiveQueries
  ]
  exact
    explicitFamilyIndex_le_inputBitSize
      count

/--
The actually executed composition-candidate counter is identically zero and
therefore input-polynomial.
-/
theorem explicitFamilySequentialDerivedClosureComposition_inputPolynomiallyBounded :
    InputPolynomiallyBounded
      explicitFamilyInputBitSize
      (fun count =>
        (explicitFamilySequentialDerivedClosureStats count).compositionCandidates) := by
  refine
    ⟨CostPolynomial.constant 0, ?_⟩
  intro count
  change
    (explicitFamilySequentialDerivedClosureStats count).compositionCandidates ≤
      0
  rw [
    explicitFamilySequentialDerivedClosureStats_compositionCandidates
  ]
  exact Nat.le_refl 0

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.firstSiblingClosureStats
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.firstSiblingClosureStats_exact
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.sequentialDerivedClosureStats
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.sequentialDerivedClosureStats_primitiveQueries
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.sequentialDerivedClosureStats_compositionCandidates
#print axioms ConstitutiveSearch.SAT.explicitFamilySequentialDerivedClosureStats
#print axioms ConstitutiveSearch.SAT.explicitFamilySequentialDerivedClosureStats_primitiveQueries
#print axioms ConstitutiveSearch.SAT.explicitFamilySequentialDerivedClosureStats_compositionCandidates
#print axioms ConstitutiveSearch.SAT.explicitFamilySequentialDerivedClosurePrimitive_inputPolynomiallyBounded
#print axioms ConstitutiveSearch.SAT.explicitFamilySequentialDerivedClosureComposition_inputPolynomiallyBounded
/- AXIOM_AUDIT_END -/
