import Init.Omega
import ConstitutiveSearch.ConstitutedPrimitivePath
import ConstitutiveSearch.SAT.TrajectoryConstitutedLocalSchedule

/-!
# Endpoint composability of constituted local schedules

A trajectory-derived local schedule is a sequence of sibling reductions.
Such a sequence must not be confused with one endpoint-to-endpoint transport.

This module isolates the exact condition under which a list of local witnesses
can be composed as one transport code: the target of every entry must be the
source of the next entry.

When that adjacency condition holds, the schedule compiles constructively to a
TransportCode over the packaged GeneratedStructuralFlipWitness generator and
the atom count is exactly the schedule length.

For FlipSymmetricTrajectory, two consecutive schedule entries are not adjacent:
the first target is the retained true child, while the next source is a fresh
false child generated one level later.  Their generation depths differ by one.
Therefore every trajectory-derived schedule of length at least two must remain
a schedule of local reductions rather than an endpoint-to-endpoint flip path.
-/

namespace ConstitutiveSearch
namespace SAT

namespace ConstitutedLocalWitness

/-- Package a step-local variable and exact relation into the uniform flip generator. -/
def packaged
    {rootFormula : Cnf}
    (entry :
      ConstitutedLocalWitness rootFormula) :
    GeneratedStructuralFlipWitness
      entry.source
      entry.target :=
  { var := entry.var
    relation := entry.relation }

end ConstitutedLocalWitness

namespace ConstitutedLocalSchedule

universe uGenerator

/-- Transport a closure code along equality of its source endpoint. -/
def castTransportSource
    {State : Type}
    {Generator : State → State → Type uGenerator}
    {source source' target : State}
    (sourceExact : source = source')
    (code : TransportClosure Generator source target) :
    TransportClosure Generator source' target :=
  sourceExact ▸ code

/-- Source transport does not change transport-code atom count. -/
theorem castTransportSource_size
    {State : Type}
    {Generator : State → State → Type uGenerator}
    {source source' target : State}
    (sourceExact : source = source')
    (code : TransportClosure Generator source target) :
    (castTransportSource sourceExact code).size = code.size := by
  cases sourceExact
  rfl

/--
Exact endpoint-adjacency condition for a local schedule.

The empty schedule has no determined endpoint transport.
A singleton is composable.
A longer schedule is composable exactly when the first target is the second
source and the remaining suffix is itself composable.
-/
def EndpointComposable
    {rootFormula : Cnf} :
    List (ConstitutedLocalWitness rootFormula) →
      Prop
  | [] =>
      False
  | [_entry] =>
      True
  | first :: second :: rest =>
      first.target = second.source ∧
        EndpointComposable (second :: rest)

/-- Empty schedules do not determine an endpoint-to-endpoint transport. -/
theorem endpointComposable_nil
    {rootFormula : Cnf} :
    ¬
      EndpointComposable
        ([] :
          List
            (ConstitutedLocalWitness
              rootFormula)) := by
  intro impossible
  exact impossible

/-- Every single local transport is endpoint-composable. -/
theorem endpointComposable_single
    {rootFormula : Cnf}
    (entry :
      ConstitutedLocalWitness rootFormula) :
    EndpointComposable [entry] := by
  exact True.intro

/-- Exact recursive characterization for schedules of length at least two. -/
theorem endpointComposable_cons_cons_iff
    {rootFormula : Cnf}
    (first second :
      ConstitutedLocalWitness rootFormula)
    (rest :
      List (ConstitutedLocalWitness rootFormula)) :
    EndpointComposable
        (first :: second :: rest) ↔
      first.target = second.source ∧
        EndpointComposable
          (second :: rest) := by
  rfl

/--
An endpoint-composable nonempty schedule compiles to one transport code whose
atom count is exactly the schedule length.

The proof uses precisely the packaged witness of each schedule entry.
-/
theorem endpointComposable_hasTransportCode
    {rootFormula : Cnf} :
    ∀ (first :
        ConstitutedLocalWitness rootFormula)
      (rest :
        List (ConstitutedLocalWitness rootFormula)),
      EndpointComposable
          (first :: rest) →
        ∃ target :
            GeneratedStructuralBranchContext
              rootFormula,
          ∃ code :
              TransportClosure
                (GeneratedStructuralFlipWitness
                  (rootFormula := rootFormula))
                first.source
                target,
            code.size =
              (first :: rest).length
  | first, [], _composable => by
      refine
        ⟨first.target,
          TransportClosure.ofGenerator
            first.packaged,
          ?_⟩
      rfl
  | first, second :: rest, composable => by
      rcases composable with
        ⟨linked, tailComposable⟩
      rcases
          endpointComposable_hasTransportCode
            second
            rest
            tailComposable with
        ⟨target, tailCode, tailSize⟩
      let alignedTailCode :
          TransportClosure
            (GeneratedStructuralFlipWitness
              (rootFormula := rootFormula))
            first.target
            target :=
        castTransportSource
          linked.symm
          tailCode
      refine
        ⟨target,
          TransportClosure.compose
            (TransportClosure.ofGenerator
              first.packaged)
            alignedTailCode,
          ?_⟩
      change
        1 + alignedTailCode.size =
          Nat.succ
            (second :: rest).length
      rw [
        show alignedTailCode.size = tailCode.size by
          exact
            castTransportSource_size
              linked.symm
              tailCode,
        tailSize
      ]
      exact
        Nat.add_comm
          1
          (second :: rest).length

/-- A mismatch at the first adjacency forces the whole schedule to stay local. -/
theorem not_endpointComposable_of_first_gap
    {rootFormula : Cnf}
    (first second :
      ConstitutedLocalWitness rootFormula)
    (rest :
      List (ConstitutedLocalWitness rootFormula))
    (gap :
      first.target ≠ second.source) :
    ¬
      EndpointComposable
        (first :: second :: rest) := by
  intro composable
  exact
    gap
      ((endpointComposable_cons_cons_iff
        first
        second
        rest).1
        composable).1

end ConstitutedLocalSchedule

namespace FlipSymmetricTrajectory

/-- Two successive trajectory steps produce non-adjacent sibling transports. -/
theorem step_step_constitutedLocalWitnesses_not_endpointComposable
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
    (nextVar : Var)
    (nextFresh :
      StructuralDecisionsAvoid
        nextVar
        (GeneratedStructuralBranchContext.child
          parent
          var
          true
          fresh).context.decisions)
    (nextSymmetric :
      FlipSymmetricAt
        (GeneratedStructuralBranchContext.child
          parent
          var
          true
          fresh).context.formula
        nextVar)
    (nextTail :
      FlipSymmetricTrajectory
        (GeneratedStructuralBranchContext.child
          (GeneratedStructuralBranchContext.child
            parent
            var
            true
            fresh)
          nextVar
          true
          nextFresh)
        finish
        length) :
    ¬
      ConstitutedLocalSchedule.EndpointComposable
        (FlipSymmetricTrajectory.step
          var
          fresh
          symmetric
          (FlipSymmetricTrajectory.step
            nextVar
            nextFresh
            nextSymmetric
            nextTail)).constitutedLocalWitnesses := by
  have gap :
      (GeneratedStructuralBranchContext.child
        parent
        var
        true
        fresh) ≠
      (GeneratedStructuralBranchContext.child
        (GeneratedStructuralBranchContext.child
          parent
          var
          true
          fresh)
        nextVar
        false
        nextFresh) := by
    intro equalEndpoints
    have depthEqual :=
      congrArg
        GeneratedStructuralBranchContext.depth
        equalEndpoints
    rw [
      GeneratedStructuralBranchContext.child_depth,
      GeneratedStructuralBranchContext.child_depth,
      GeneratedStructuralBranchContext.child_depth
    ] at depthEqual
    omega
  exact
    ConstitutedLocalSchedule.not_endpointComposable_of_first_gap
      _
      _
      _
      gap

/--
Every flip-symmetric trajectory-derived schedule with at least two local
reductions is not endpoint-composable.
-/
theorem constitutedLocalWitnesses_not_endpointComposable_of_two_le
    {rootFormula : Cnf}
    {start finish :
      GeneratedStructuralBranchContext rootFormula}
    {length : Nat}
    (trajectory :
      FlipSymmetricTrajectory
        start
        finish
        length)
    (twoLe : 2 ≤ length) :
    ¬
      ConstitutedLocalSchedule.EndpointComposable
        trajectory.constitutedLocalWitnesses := by
  cases trajectory with
  | done state =>
      omega
  | step var fresh symmetric tail =>
      cases tail with
      | done child =>
          omega
      | step nextVar nextFresh nextSymmetric nextTail =>
          exact
            step_step_constitutedLocalWitnesses_not_endpointComposable
              var
              fresh
              symmetric
              nextVar
              nextFresh
              nextSymmetric
              nextTail

end FlipSymmetricTrajectory

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.ConstitutedLocalWitness.packaged
#print axioms ConstitutiveSearch.SAT.ConstitutedLocalSchedule.EndpointComposable
#print axioms ConstitutiveSearch.SAT.ConstitutedLocalSchedule.endpointComposable_nil
#print axioms ConstitutiveSearch.SAT.ConstitutedLocalSchedule.endpointComposable_single
#print axioms ConstitutiveSearch.SAT.ConstitutedLocalSchedule.endpointComposable_cons_cons_iff
#print axioms ConstitutiveSearch.SAT.ConstitutedLocalSchedule.endpointComposable_hasTransportCode
#print axioms ConstitutiveSearch.SAT.ConstitutedLocalSchedule.not_endpointComposable_of_first_gap
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.constitutedLocalWitnesses_not_endpointComposable_of_two_le
/- AXIOM_AUDIT_END -/
