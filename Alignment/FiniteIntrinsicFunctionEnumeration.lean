import Alignment.FiniteIntrinsicRelationalSearch

/-!
# Finite intrinsic function enumeration

This module removes one more supplied search object from finite intrinsic
alignment.  Starting only from complete finite listings of two already
constituted carriers, it constructs a finite family extensionally containing
every function between them.

No cross-system pairing, anchor family, mediator, transport, or permutation is
provided.  The enumeration first generates all target-valued tables of the
source-list length, then interprets each table as a total function.  Completeness
of the local source listing guarantees that the fallback branch is never
semantically relevant.  Empty target and empty source cases are handled
constructively rather than by an inhabitedness or choice assumption.

This is the combinatorial precursor to generating all exact transports: exact
transports can be obtained by pairing enumerated forward and backward functions
and retaining exactly those pairs whose two round trips hold.
-/

namespace Alignment
namespace GenesisReconstruction
namespace FiniteIntrinsicFunctionEnumeration

open FiniteAnchoredMatchSearch

universe uSource uTarget

/--
A finite family of functions complete up to pointwise equality.
-/
structure FiniteFunctionListing
    (Source : Type uSource)
    (Target : Type uTarget) where
  values : List (Source → Target)
  complete :
    (function : Source → Target) →
      { listed : Source → Target //
        listed ∈ values ∧
          ((source : Source) → listed source = function source) }

/--
All target-valued tables of one requested length.  Repetition is intentional:
round-trip filtering, not table generation, will later isolate bijections.
-/
def allTables
    {Target : Type uTarget}
    (targets : List Target) : Nat → List (List Target)
  | 0 => [[]]
  | depth + 1 =>
      targets.flatMap fun target =>
        (allTables targets depth).map fun rest => target :: rest

/--
Any list whose entries all come from `targets` appears among the generated
tables of its own length.
-/
theorem mem_allTables_of_forall_mem
    {Target : Type uTarget}
    (values targets : List Target)
    (contained : (value : Target) → value ∈ values → value ∈ targets) :
    values ∈ allTables targets values.length := by
  induction values with
  | nil =>
      rfl
  | cons head tail ih =>
      have headMember : head ∈ targets :=
        contained head (List.Mem.head tail)
      have tailContained :
          (value : Target) → value ∈ tail → value ∈ targets := by
        intro value member
        exact contained value (List.Mem.tail head member)
      have tailMember : tail ∈ allTables targets tail.length :=
        ih tailContained
      change
        head :: tail ∈
          targets.flatMap
            (fun target =>
              (allTables targets tail.length).map
                (fun rest => target :: rest))
      rw [List.mem_flatMap]
      refine ⟨head, headMember, ?_⟩
      exact List.mem_map.mpr ⟨tail, tailMember, rfl⟩

/--
Interpret a table against a source listing.  A fallback is needed only to make
the function total syntactically; completeness will prove it is unreachable on
actual source identities whenever the source/table lengths agree by construction.
-/
def functionOfTable
    {Source : Type uSource}
    {Target : Type uTarget}
    [DecidableEq Source]
    (fallback : Target) : List Source → List Target → Source → Target
  | [], _, _ => fallback
  | _ :: _, [], _ => fallback
  | source :: sources, target :: targets, identity =>
      if identity = source then
        target
      else
        functionOfTable fallback sources targets identity

/--
The table obtained by mapping a function over the complete source list
reconstructs that function pointwise.
-/
theorem functionOfTable_map_eq
    {Source : Type uSource}
    {Target : Type uTarget}
    [DecidableEq Source]
    (fallback : Target)
    (sources : List Source)
    (function : Source → Target)
    (identity : Source)
    (member : identity ∈ sources) :
    functionOfTable fallback sources (sources.map function) identity =
      function identity := by
  induction sources with
  | nil =>
      cases member
  | cons source rest ih =>
      simp only [List.map_cons, functionOfTable]
      by_cases same : identity = source
      · rw [if_pos same]
        exact congrArg function same.symm
      · rw [if_neg same]
        cases member with
        | head =>
            exact (same rfl).elim
        | tail _ tailMember =>
            exact ih tailMember

/--
For a nonempty target listing, generated tables give a complete finite function
listing directly.
-/
def ofFallback
    {Source : Type uSource}
    {Target : Type uTarget}
    [DecidableEq Source]
    (sources : FiniteListing Source)
    (targets : FiniteListing Target)
    (fallback : Target) :
    FiniteFunctionListing Source Target :=
  { values :=
      (allTables targets.values sources.values.length).map
        (functionOfTable fallback sources.values)
    complete := by
      intro function
      let table := sources.values.map function
      have tableContained :
          (value : Target) → value ∈ table → value ∈ targets.values := by
        intro value member
        rw [List.mem_map] at member
        obtain ⟨source, _, equality⟩ := member
        cases equality
        exact targets.complete (function source)
      have tableMember :
          table ∈ allTables targets.values sources.values.length := by
        have generated :=
          mem_allTables_of_forall_mem table targets.values tableContained
        simpa [table] using generated
      let listed := functionOfTable fallback sources.values table
      refine ⟨listed, ?_, ?_⟩
      · apply List.mem_map.mpr
        exact ⟨table, tableMember, rfl⟩
      · intro source
        exact
          functionOfTable_map_eq
            fallback sources.values function source (sources.complete source) }

/-- An empty complete source listing has no inhabitants. -/
theorem false_of_empty_complete_source
    {Source : Type uSource}
    (sources : FiniteListing Source)
    (empty : sources.values = [])
    (source : Source) : False := by
  have member := sources.complete source
  rw [empty] at member
  cases member

/--
Complete finite function enumeration from local carrier listings alone.

If the target list is nonempty, its first local identity supplies the purely
syntactic fallback used by `functionOfTable`.  If it is empty, either the source
list is empty as well, giving the unique empty-domain function extensionally, or
any alleged function would manufacture a target inhabitant and contradict target
completeness.
-/
def enumerateFunctions
    {Source : Type uSource}
    {Target : Type uTarget}
    [DecidableEq Source]
    (sources : FiniteListing Source)
    (targets : FiniteListing Target) :
    FiniteFunctionListing Source Target := by
  cases targetValues : targets.values with
  | nil =>
      cases sourceValues : sources.values with
      | nil =>
          let emptyFunction : Source → Target := fun source =>
            (false_of_empty_complete_source sources sourceValues source).elim
          exact
            { values := [emptyFunction]
              complete := by
                intro function
                refine ⟨emptyFunction, List.Mem.head [], ?_⟩
                intro source
                exact
                  (false_of_empty_complete_source
                    sources sourceValues source).elim }
      | cons source rest =>
          exact
            { values := []
              complete := by
                intro function
                have targetMember := targets.complete (function source)
                rw [targetValues] at targetMember
                cases targetMember }
  | cons target rest =>
      exact ofFallback sources targets target

end FiniteIntrinsicFunctionEnumeration
end GenesisReconstruction
end Alignment

/- AXIOM_AUDIT_BEGIN -/
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicFunctionEnumeration.FiniteFunctionListing
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicFunctionEnumeration.allTables
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicFunctionEnumeration.mem_allTables_of_forall_mem
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicFunctionEnumeration.functionOfTable
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicFunctionEnumeration.functionOfTable_map_eq
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicFunctionEnumeration.ofFallback
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicFunctionEnumeration.false_of_empty_complete_source
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicFunctionEnumeration.enumerateFunctions
/- AXIOM_AUDIT_END -/
