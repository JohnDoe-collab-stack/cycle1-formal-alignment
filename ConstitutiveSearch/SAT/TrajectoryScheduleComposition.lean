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
      cases linked
      refine
        ⟨target,
          TransportClosure.compose
            (TransportClosure.ofGenerator
              first.packaged)
            tailCode,
          ?_⟩
      change
        1 + tailCode.size =
          Nat.succ
            (second :: rest).length
      rw [tailSize]
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

/--
Every flip-symmetric trajectory-derived schedule with at least two local
reductions is not endpoint-composable.

It must therefore remain a schedule of local sibling reductions.
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
    (twoLe :
      2 ≤ length) :
    ¬
      ConstitutedLocalSchedule.EndpointComposable
        trajectory.constitutedLocalWitnesses := by
  cases trajectory with
  | done state =>
      omega
  | @step parent finish tailLength var fresh symmetric tail =>
      cases tail with
      | done child =>
          omega
      | @step nextParent nextFinish nextLength nextVar nextFresh nextSymmetric nextTail =>
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
            have depthEqual :
                (GeneratedStructuralBranchContext.child
                  parent
                  var
                  true
                  fresh).depth =
                (GeneratedStructuralBranchContext.child
                  (GeneratedStructuralBranchContext.child
                    parent
                    var
                    true
                    fresh)
                  nextVar
                  false
                  nextFresh).depth :=
              congrArg
                GeneratedStructuralBranchContext.depth
                equalEndpoints
            rw [
              GeneratedStructuralBranchContext.child_depth,
              GeneratedStructuralBranchContext.child_depth,
              GeneratedStructuralBranchContext.child_depth
            ] at depthEqual
            omega
          change
            ¬
              ConstitutedLocalSchedule.EndpointComposable
                ({ var := var
                   source :=
                     GeneratedStructuralBranchContext.child
                       parent
                       var
                       false
                       fresh
                   target :=
                     GeneratedStructuralBranchContext.child
                       parent
                       var
                       true
                       fresh
                   relation :=
                     flipSymmetricSiblingRelation
                       parent
                       var
                       fresh
                       symmetric } ::
                 { var := nextVar
                   source :=
                     GeneratedStructuralBranchContext.child
                       (GeneratedStructuralBranchContext.child
                         parent
                         var
                         true
                         fresh)
                       nextVar
                       false
                       nextFresh
                   target :=
                     GeneratedStructuralBranchContext.child
                       (GeneratedStructuralBranchContext.child
                         parent
                         var
                         true
                         fresh)
                       nextVar
                       true
                       nextFresh
                   relation :=
                     flipSymmetricSiblingRelation
                       (GeneratedStructuralBranchContext.child
                         parent
                         var
                         true
                         fresh)
                       nextVar
                       nextFresh
                       nextSymmetric } ::
                 nextTail.constitutedLocalWitnesses)
          exact
            ConstitutedLocalSchedule.not_endpointComposable_of_first_gap
              _
              _
              _
              gap

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
