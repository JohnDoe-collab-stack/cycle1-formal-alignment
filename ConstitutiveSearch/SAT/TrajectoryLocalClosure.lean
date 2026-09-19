import ConstitutiveSearch.ConstitutiveComplexityInputPolynomial
import ConstitutiveSearch.SAT.ExplicitFamilyInputComplexity
import ConstitutiveSearch.SAT.TrajectoryDerivedClosure

/-!
# Local closure audit along constituted SAT trajectories

TrajectoryDerivedClosure reconstructs a finite global closure domain from an
entire FlipSymmetricTrajectory.  That global pool is intentionally exhaustive:
it contains the children of every split.

The operational trajectory itself is more local.  At each constitutive step,
the current variable already certifies the exact false-sibling -> true-sibling
flip.  This module makes that distinction executable.

For every local step:
* primitive generators are derived from the singleton provenance [var];
* no intermediate candidate is needed;
* fuel is exactly one;
* the bounded closure search succeeds on the primitive query;
* it performs exactly one primitive query and zero composition candidates.

Aggregating those actual local runs along a trajectory of length n gives exactly
n primitive queries and zero composition candidates.  On the closed SAT family
F(n), this local control-flow count is input-polynomial in the concrete binary
input size.

This does not assert completeness of the global closure engine.  It records the
cost of the already-certified local absorptions that constitute this particular
trajectory.
-/

namespace ConstitutiveSearch
namespace SAT

/--
Executable fuel-one closure run for the exact sibling relation constituted by
one FlipSymmetricTrajectory step.
-/
def localSiblingClosureRun
    {rootFormula : Cnf}
    (parent :
      GeneratedStructuralBranchContext rootFormula)
    (var : Var)
    (fresh :
      StructuralDecisionsAvoid
        var
        parent.context.decisions)
    (symmetric :
      FlipSymmetricAt
        parent.context.formula
        var) :
    ClosureSearchRun
      (ProvenanceStructuralFlipWitness
        (rootFormula := rootFormula)
        [var])
      (GeneratedStructuralBranchContext.child
        parent
        var
        false
        fresh)
      (GeneratedStructuralBranchContext.child
        parent
        var
        true
        fresh) :=
  searchTransportClosureBounded
    (provenanceStructuralFlipSearch
      rootFormula
      [var])
    []
    1
    (GeneratedStructuralBranchContext.child
      parent
      var
      false
      fresh)
    (GeneratedStructuralBranchContext.child
      parent
      var
      true
      fresh)

/-- The local derived closure run always reconstructs a transport code. -/
theorem localSiblingClosureRun_code_found
    {rootFormula : Cnf}
    (parent :
      GeneratedStructuralBranchContext rootFormula)
    (var : Var)
    (fresh :
      StructuralDecisionsAvoid
        var
        parent.context.decisions)
    (symmetric :
      FlipSymmetricAt
        parent.context.formula
        var) :
    (localSiblingClosureRun
      parent
      var
      fresh
      symmetric).code? ≠
        none := by
  unfold localSiblingClosureRun
  dsimp [
    searchTransportClosureBounded,
    provenanceStructuralFlipSearch
  ]
  let relation :=
    flipSymmetricSiblingRelation
      parent
      var
      fresh
      symmetric
  dsimp [generatedStructuralFlipAtSearch]
  rw [
    dif_pos relation.formulaExact,
    dif_pos relation.decisionsExact
  ]
  intro impossible
  cases impossible

/-- The successful local run performs exactly one primitive relation query. -/
theorem localSiblingClosureRun_primitiveQueries
    {rootFormula : Cnf}
    (parent :
      GeneratedStructuralBranchContext rootFormula)
    (var : Var)
    (fresh :
      StructuralDecisionsAvoid
        var
        parent.context.decisions)
    (symmetric :
      FlipSymmetricAt
        parent.context.formula
        var) :
    (localSiblingClosureRun
      parent
      var
      fresh
      symmetric).stats.primitiveQueries =
        1 := by
  unfold localSiblingClosureRun
  dsimp [
    searchTransportClosureBounded,
    provenanceStructuralFlipSearch
  ]
  let relation :=
    flipSymmetricSiblingRelation
      parent
      var
      fresh
      symmetric
  dsimp [generatedStructuralFlipAtSearch]
  rw [
    dif_pos relation.formulaExact,
    dif_pos relation.decisionsExact
  ]
  rfl

/-- No composition candidate is inspected because the primitive query succeeds. -/
theorem localSiblingClosureRun_compositionCandidates
    {rootFormula : Cnf}
    (parent :
      GeneratedStructuralBranchContext rootFormula)
    (var : Var)
    (fresh :
      StructuralDecisionsAvoid
        var
        parent.context.decisions)
    (symmetric :
      FlipSymmetricAt
        parent.context.formula
        var) :
    (localSiblingClosureRun
      parent
      var
      fresh
      symmetric).stats.compositionCandidates =
        0 := by
  unfold localSiblingClosureRun
  dsimp [
    searchTransportClosureBounded,
    provenanceStructuralFlipSearch
  ]
  let relation :=
    flipSymmetricSiblingRelation
      parent
      var
      fresh
      symmetric
  dsimp [generatedStructuralFlipAtSearch]
  rw [
    dif_pos relation.formulaExact,
    dif_pos relation.decisionsExact
  ]
  rfl

namespace FlipSymmetricTrajectory

/--
Aggregate the stats of the actual local sibling-closure run at every step.
-/
def localClosureStats
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
        (localSiblingClosureRun
          start
          var
          fresh
          symmetric).stats
        tail.localClosureStats

/-- Exactly one successful primitive query is charged per constitutive step. -/
theorem localClosureStats_primitiveQueries
    {rootFormula : Cnf}
    {start finish :
      GeneratedStructuralBranchContext rootFormula}
    {length : Nat}
    (trajectory :
      FlipSymmetricTrajectory start finish length) :
    trajectory.localClosureStats.primitiveQueries =
      length := by
  induction trajectory with
  | done state =>
      rfl
  | step var fresh symmetric tail inductionHypothesis =>
      change
        (localSiblingClosureRun
            _
            var
            fresh
            symmetric).stats.primitiveQueries +
            tail.localClosureStats.primitiveQueries =
          _ + 1
      rw [
        localSiblingClosureRun_primitiveQueries,
        inductionHypothesis
      ]
      exact Nat.add_comm 1 _

/-- Local certified absorptions never enter composition-candidate search. -/
theorem localClosureStats_compositionCandidates
    {rootFormula : Cnf}
    {start finish :
      GeneratedStructuralBranchContext rootFormula}
    {length : Nat}
    (trajectory :
      FlipSymmetricTrajectory start finish length) :
    trajectory.localClosureStats.compositionCandidates =
      0 := by
  induction trajectory with
  | done state =>
      rfl
  | step var fresh symmetric tail inductionHypothesis =>
      change
        (localSiblingClosureRun
            _
            var
            fresh
            symmetric).stats.compositionCandidates +
            tail.localClosureStats.compositionCandidates =
          0
      rw [
        localSiblingClosureRun_compositionCandidates,
        inductionHypothesis
      ]

end FlipSymmetricTrajectory

/-! ## Closed explicit family -/

/-- Aggregate local closure stats of the actual resource-aligned F(n) path. -/
def explicitFamilyTrajectoryLocalClosureStats
    (count : Nat) :
    ClosureSearchStats :=
  (explicitFamilyResourceTrajectory count).trajectory.localClosureStats

/-- F(n) performs exactly n local primitive queries on its certified path. -/
theorem explicitFamilyTrajectoryLocalClosureStats_primitiveQueries
    (count : Nat) :
    (explicitFamilyTrajectoryLocalClosureStats count).primitiveQueries =
      count :=
  (explicitFamilyResourceTrajectory count).trajectory.localClosureStats_primitiveQueries

/-- No local step of F(n) needs a composition candidate. -/
theorem explicitFamilyTrajectoryLocalClosureStats_compositionCandidates
    (count : Nat) :
    (explicitFamilyTrajectoryLocalClosureStats count).compositionCandidates =
      0 :=
  (explicitFamilyResourceTrajectory count).trajectory.localClosureStats_compositionCandidates

/--
The exact local primitive-query count is polynomial in the concrete binary
input size of F(n).
-/
theorem explicitFamilyTrajectoryLocalPrimitiveQueries_inputPolynomiallyBounded :
    InputPolynomiallyBounded
      explicitFamilyInputBitSize
      (fun count =>
        (explicitFamilyTrajectoryLocalClosureStats count).primitiveQueries) :=
  ⟨CostPolynomial.input,
    fun count => by
      change
        (explicitFamilyTrajectoryLocalClosureStats count).primitiveQueries ≤
          explicitFamilyInputBitSize count
      rw [
        explicitFamilyTrajectoryLocalClosureStats_primitiveQueries
      ]
      exact
        explicitFamilyIndex_le_inputBitSize
          count⟩

/-- The exact local composition-candidate count is constantly zero. -/
theorem explicitFamilyTrajectoryLocalCompositionCandidates_inputPolynomiallyBounded :
    InputPolynomiallyBounded
      explicitFamilyInputBitSize
      (fun count =>
        (explicitFamilyTrajectoryLocalClosureStats count).compositionCandidates) :=
  ⟨CostPolynomial.constant 0,
    fun count => by
      change
        (explicitFamilyTrajectoryLocalClosureStats count).compositionCandidates ≤
          0
      rw [
        explicitFamilyTrajectoryLocalClosureStats_compositionCandidates
      ]⟩

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.localSiblingClosureRun
#print axioms ConstitutiveSearch.SAT.localSiblingClosureRun_code_found
#print axioms ConstitutiveSearch.SAT.localSiblingClosureRun_primitiveQueries
#print axioms ConstitutiveSearch.SAT.localSiblingClosureRun_compositionCandidates
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.localClosureStats
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.localClosureStats_primitiveQueries
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.localClosureStats_compositionCandidates
#print axioms ConstitutiveSearch.SAT.explicitFamilyTrajectoryLocalClosureStats
#print axioms ConstitutiveSearch.SAT.explicitFamilyTrajectoryLocalClosureStats_primitiveQueries
#print axioms ConstitutiveSearch.SAT.explicitFamilyTrajectoryLocalClosureStats_compositionCandidates
#print axioms ConstitutiveSearch.SAT.explicitFamilyTrajectoryLocalPrimitiveQueries_inputPolynomiallyBounded
#print axioms ConstitutiveSearch.SAT.explicitFamilyTrajectoryLocalCompositionCandidates_inputPolynomiallyBounded
/- AXIOM_AUDIT_END -/
