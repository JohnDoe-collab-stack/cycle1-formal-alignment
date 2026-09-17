import Alignment.FiniteAnchoredMatchSearch

/-!
# Finite intrinsic function enumeration

This module removes one more supplied search object from finite intrinsic
alignment. Starting only from complete finite listings of two already
constituted carriers, it constructs a finite family extensionally containing
every function between them.

No cross-system pairing, anchor family, mediator, transport, or permutation is
provided. The enumeration first generates all target-valued tables of the
source-list length, then interprets each table as a total function. Completeness
of the local source listing guarantees that the fallback branch is never
semantically relevant. Empty target and empty source cases are handled
constructively rather than by an inhabitedness or choice assumption.

This is the combinatorial precursor to generating all exact transports: exact
transports can be obtained by pairing enumerated forward and backward functions
and retaining exactly those pairs whose two round trips hold.
-/

namespace Alignment
namespace GenesisReconstruction
namespace FiniteIntrinsicFunctionEnumeration

open FiniteAnchoredMatchSearch

universe uSource uTarget uAux

/-- A finite family of functions complete up to pointwise equality. -/
structure FiniteFunctionListing
    (Source : Type uSource)
    (Target : Type uTarget) where
  values : List (Source → Target)
  complete :
    (function : Source → Target) →
      { listed : Source → Target //
        listed ∈ values ∧
          ((source : Source) → listed source = function source) }

/-- Constructive left injection of list membership through append. -/
theorem mem_append_left
    {α : Type uAux}
    {value : α}
    {left right : List α}
    (member : value ∈ left) :
    value ∈ left ++ right := by
  induction left with
  | nil => cases member
  | cons head tail ih =>
      cases member with
      | head => exact List.Mem.head (tail ++ right)
      | tail _ tailMember =>
          exact List.Mem.tail head (ih tailMember)

/-- Constructive right injection of list membership through append. -/
theorem mem_append_right
    {α : Type uAux}
    {value : α}
    (left : List α)
    {right : List α}
    (member : value ∈ right) :
    value ∈ left ++ right := by
  induction left with
  | nil => exact member
  | cons head tail ih =>
      exact List.Mem.tail head ih

/-- Constructive map of list membership, avoiding extensional membership rewrites. -/
theorem mem_map_of_mem
    {α : Type uSource}
    {β : Type uTarget}
    {value : α}
    {values : List α}
    (function : α → β)
    (member : value ∈ values) :
    function value ∈ values.map function := by
  induction values with
  | nil => cases member
  | cons head tail ih =>
      cases member with
      | head => exact List.Mem.head (tail.map function)
      | tail _ tailMember =>
          exact List.Mem.tail (function head) (ih tailMember)

/-- Constructive membership introduction for `flatMap`. -/
theorem mem_flatMap_of_mem_of_mem
    {α : Type uSource}
    {β : Type uTarget}
    {source : α}
    {target : β}
    {sources : List α}
    (function : α → List β)
    (sourceMember : source ∈ sources)
    (targetMember : target ∈ function source) :
    target ∈ sources.flatMap function := by
  induction sources with
  | nil => cases sourceMember
  | cons head tail ih =>
      cases sourceMember with
      | head =>
          exact mem_append_left targetMember
      | tail _ tailMember =>
          exact
            mem_append_right (function head)
              (ih tailMember)

/-- All target-valued tables of one requested length. -/
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
      change [] ∈ ([[]] : List (List Target))
      exact List.Mem.head []
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
      apply mem_flatMap_of_mem_of_mem
        (fun target =>
          (allTables targets tail.length).map
            (fun rest => target :: rest))
        headMember
      exact mem_map_of_mem (fun rest => head :: rest) tailMember

/--
A function table built directly from a source list is generated at exactly the
source-list depth. This direct induction avoids any propositional rewriting of
`List.length_map` in the completeness proof.
-/
theorem mappedTable_mem_allTables
    {Source : Type uSource}
    {Target : Type uTarget}
    (sources : List Source)
    (targets : FiniteListing Target)
    (function : Source → Target) :
    sources.map function ∈ allTables targets.values sources.length := by
  induction sources with
  | nil =>
      change [] ∈ ([[]] : List (List Target))
      exact List.Mem.head []
  | cons source rest ih =>
      change
        function source :: rest.map function ∈
          targets.values.flatMap
            (fun target =>
              (allTables targets.values rest.length).map
                (fun values => target :: values))
      apply mem_flatMap_of_mem_of_mem
        (fun target =>
          (allTables targets.values rest.length).map
            (fun values => target :: values))
        (targets.complete (function source))
      exact
        mem_map_of_mem
          (fun values => function source :: values)
          ih

/--
Interpret a table against a source listing. A fallback is needed only to make
the function total syntactically; completeness proves it unreachable on actual
source identities for the tables used by the completeness proof.
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
      change
        (if identity = source then
          function source
        else
          functionOfTable fallback rest (rest.map function) identity) =
        function identity
      by_cases same : identity = source
      · rw [if_pos same]
        cases same
        rfl
      · rw [if_neg same]
        cases member with
        | head =>
            exact (same rfl).elim
        | tail _ tailMember =>
            exact ih tailMember

/-- Every member of a mapped table lies in a complete target listing. -/
theorem codomain_mem_of_mem_map
    {Source : Type uSource}
    {Target : Type uTarget}
    (targets : FiniteListing Target)
    (function : Source → Target)
    (sources : List Source)
    (value : Target)
    (member : value ∈ sources.map function) :
    value ∈ targets.values := by
  induction sources with
  | nil => cases member
  | cons source rest ih =>
      cases member with
      | head => exact targets.complete (function source)
      | tail _ tailMember => exact ih tailMember

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
      have tableMember :
          sources.values.map function ∈
            allTables targets.values sources.values.length :=
        mappedTable_mem_allTables sources.values targets function
      let listed :=
        functionOfTable fallback sources.values (sources.values.map function)
      refine ⟨listed, ?_, ?_⟩
      · change
          functionOfTable fallback sources.values (sources.values.map function) ∈
            (allTables targets.values sources.values.length).map
              (functionOfTable fallback sources.values)
        exact
          mem_map_of_mem
            (functionOfTable fallback sources.values)
            tableMember
      · intro source
        change
          functionOfTable fallback sources.values
              (sources.values.map function) source =
            function source
        exact
          functionOfTable_map_eq
            fallback sources.values function source (sources.complete source) }

/-- An empty complete listing has no inhabitants. -/
theorem false_of_empty_complete_listing
    {Carrier : Type uAux}
    (listing : FiniteListing Carrier)
    (empty : listing.values = [])
    (identity : Carrier) : False := by
  have member := listing.complete identity
  rw [empty] at member
  cases member

/--
Complete finite function enumeration from local carrier listings alone.

If the target list is nonempty, its first local identity supplies the purely
syntactic fallback used by `functionOfTable`. If it is empty, either the source
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
            (false_of_empty_complete_listing sources sourceValues source).elim
          exact
            { values := [emptyFunction]
              complete := by
                intro function
                refine ⟨emptyFunction, List.Mem.head [], ?_⟩
                intro source
                exact
                  (false_of_empty_complete_listing
                    sources sourceValues source).elim }
      | cons source rest =>
          exact
            { values := []
              complete := by
                intro function
                exact
                  (false_of_empty_complete_listing
                    targets targetValues (function source)).elim }
  | cons target rest =>
      exact ofFallback sources targets target

end FiniteIntrinsicFunctionEnumeration
end GenesisReconstruction
end Alignment

/- AXIOM_AUDIT_BEGIN -/
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicFunctionEnumeration.FiniteFunctionListing
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicFunctionEnumeration.mem_append_left
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicFunctionEnumeration.mem_append_right
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicFunctionEnumeration.mem_map_of_mem
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicFunctionEnumeration.mem_flatMap_of_mem_of_mem
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicFunctionEnumeration.allTables
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicFunctionEnumeration.mem_allTables_of_forall_mem
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicFunctionEnumeration.mappedTable_mem_allTables
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicFunctionEnumeration.functionOfTable
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicFunctionEnumeration.functionOfTable_map_eq
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicFunctionEnumeration.codomain_mem_of_mem_map
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicFunctionEnumeration.ofFallback
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicFunctionEnumeration.false_of_empty_complete_listing
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicFunctionEnumeration.enumerateFunctions
/- AXIOM_AUDIT_END -/
