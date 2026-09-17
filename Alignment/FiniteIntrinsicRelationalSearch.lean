import Alignment.IntrinsicRelationalEquivalence
import Alignment.FiniteAnchoredMatchSearch

/-!
# Finite intrinsic relational search

This module gives an executable decision layer that no longer requires a common
anchor family. It operates directly on complete local source relations and a
finite explicit family of exact carrier transports.

A `FiniteTransportListing` is positive data containing candidate exact
transports and a constructive completeness witness: every exact transport has a
listed representative with the same forward map. Since exact backward maps are
pointwise determined by their forward maps, this is the relevant extensional
notion of completeness for the search.

The search checks the complete source relation matrix. A successful Boolean
check constructs `IntrinsicCompatibleExactAlignment`. If the candidate listing
is complete, failure constructively refutes every compatible exact relational
alignment.

This still does not generate the complete transport listing from arbitrary
finite carriers. It isolates that remaining combinatorial problem without
reintroducing anchors or a supplied mediator.
-/

namespace Alignment
namespace GenesisReconstruction
namespace FiniteIntrinsicRelationalSearch

open FiniteAnchoredMatchSearch

universe uSource uTarget uValue

/--
A finite candidate family complete up to pointwise equality of exact forward
maps.
-/
structure FiniteTransportListing
    (Source : Type uSource)
    (Target : Type uTarget) where
  values : List (ExactTypeTransport Source Target)
  complete :
    (transport : ExactTypeTransport Source Target) →
      { listed : ExactTypeTransport Source Target //
        listed ∈ values ∧
          ((source : Source) →
            listed.forward source = transport.forward source) }

/-- Check one source row of the intrinsic relation matrix. -/
def rowPreservesOn
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : IntrinsicRelationalContext Source Target Value)
    (transport : ExactTypeTransport Source Target)
    (first : Source) : List Source → Bool
  | [] => true
  | second :: rest =>
      if context.targetRelation
            (transport.forward first)
            (transport.forward second) =
          context.sourceRelation first second then
        rowPreservesOn context transport first rest
      else
        false

/-- A successful row check proves every checked matrix entry. -/
theorem rowEquality_of_mem_of_true
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : IntrinsicRelationalContext Source Target Value)
    (transport : ExactTypeTransport Source Target)
    (first second : Source)
    (sources : List Source)
    (member : second ∈ sources)
    (checked : rowPreservesOn context transport first sources = true) :
    context.targetRelation
        (transport.forward first)
        (transport.forward second) =
      context.sourceRelation first second := by
  induction sources with
  | nil =>
      cases member
  | cons head tail ih =>
      by_cases headExact :
          context.targetRelation
              (transport.forward first)
              (transport.forward head) =
            context.sourceRelation first head
      · have tailChecked :
            rowPreservesOn context transport first tail = true := by
          change
            (if context.targetRelation
                  (transport.forward first)
                  (transport.forward head) =
                context.sourceRelation first head then
              rowPreservesOn context transport first tail
            else
              false) = true at checked
          rw [if_pos headExact] at checked
          exact checked
        cases member with
        | head => exact headExact
        | tail _ tailMember => exact ih tailMember tailChecked
      · change
          (if context.targetRelation
                (transport.forward first)
                (transport.forward head) =
              context.sourceRelation first head then
            rowPreservesOn context transport first tail
          else
            false) = true at checked
        rw [if_neg headExact] at checked
        cases checked

/-- Check all requested rows against one fixed complete column list. -/
def rowsPreserveOn
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : IntrinsicRelationalContext Source Target Value)
    (transport : ExactTypeTransport Source Target)
    (allSources : List Source) : List Source → Bool
  | [] => true
  | first :: rest =>
      match rowPreservesOn context transport first allSources with
      | true => rowsPreserveOn context transport allSources rest
      | false => false

/-- Successful matrix checking proves any entry whose row and column were listed. -/
theorem relationEquality_of_mem_of_mem_of_rows_true
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : IntrinsicRelationalContext Source Target Value)
    (transport : ExactTypeTransport Source Target)
    (allSources rows : List Source)
    (first second : Source)
    (firstMember : first ∈ rows)
    (secondMember : second ∈ allSources)
    (checked : rowsPreserveOn context transport allSources rows = true) :
    context.targetRelation
        (transport.forward first)
        (transport.forward second) =
      context.sourceRelation first second := by
  induction rows with
  | nil =>
      cases firstMember
  | cons head tail ih =>
      cases rowCheck : rowPreservesOn context transport head allSources with
      | false =>
          change
            (match rowPreservesOn context transport head allSources with
            | true => rowsPreserveOn context transport allSources tail
            | false => false) = true at checked
          rw [rowCheck] at checked
          cases checked
      | true =>
          have tailChecked :
              rowsPreserveOn context transport allSources tail = true := by
            change
              (match rowPreservesOn context transport head allSources with
              | true => rowsPreserveOn context transport allSources tail
              | false => false) = true at checked
            rw [rowCheck] at checked
            exact checked
          cases firstMember with
          | head =>
              exact rowEquality_of_mem_of_true
                context transport head second allSources
                secondMember rowCheck
          | tail _ tailMember =>
              exact ih tailMember secondMember tailChecked

/-- Boolean preservation test for the complete listed relation matrix. -/
def preservesRelationOn
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : IntrinsicRelationalContext Source Target Value)
    (sources : List Source)
    (transport : ExactTypeTransport Source Target) : Bool :=
  rowsPreserveOn context transport sources sources

/-- Complete source enumeration upgrades matrix success to full relation preservation. -/
theorem preservesRelation_of_true
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : IntrinsicRelationalContext Source Target Value)
    (sources : FiniteListing Source)
    (transport : ExactTypeTransport Source Target)
    (checked : preservesRelationOn context sources.values transport = true) :
    (first second : Source) →
      context.targetRelation
          (transport.forward first)
          (transport.forward second) =
        context.sourceRelation first second := by
  intro first second
  exact relationEquality_of_mem_of_mem_of_rows_true
    context transport sources.values sources.values first second
    (sources.complete first) (sources.complete second) checked

/-- A genuinely relation-preserving transport passes every explicit row check. -/
theorem rowPreservesOn_true_of_preserves
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : IntrinsicRelationalContext Source Target Value)
    (transport : ExactTypeTransport Source Target)
    (preserves :
      (first second : Source) →
        context.targetRelation
            (transport.forward first)
            (transport.forward second) =
          context.sourceRelation first second)
    (first : Source)
    (sources : List Source) :
    rowPreservesOn context transport first sources = true := by
  induction sources with
  | nil => rfl
  | cons second rest ih =>
      change
        (if context.targetRelation
              (transport.forward first)
              (transport.forward second) =
            context.sourceRelation first second then
          rowPreservesOn context transport first rest
        else
          false) = true
      rw [if_pos (preserves first second)]
      exact ih

/-- Full relation preservation passes every finite matrix check. -/
theorem rowsPreserveOn_true_of_preserves
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : IntrinsicRelationalContext Source Target Value)
    (transport : ExactTypeTransport Source Target)
    (preserves :
      (first second : Source) →
        context.targetRelation
            (transport.forward first)
            (transport.forward second) =
          context.sourceRelation first second)
    (allSources rows : List Source) :
    rowsPreserveOn context transport allSources rows = true := by
  induction rows with
  | nil => rfl
  | cons first rest ih =>
      have rowChecked :=
        rowPreservesOn_true_of_preserves
          context transport preserves first allSources
      change
        (match rowPreservesOn context transport first allSources with
        | true => rowsPreserveOn context transport allSources rest
        | false => false) = true
      rw [rowChecked]
      exact ih

/-- Any relation-preserving transport passes the complete matrix checker. -/
theorem preservesRelationOn_true_of_preserves
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : IntrinsicRelationalContext Source Target Value)
    (sources : List Source)
    (transport : ExactTypeTransport Source Target)
    (preserves :
      (first second : Source) →
        context.targetRelation
            (transport.forward first)
            (transport.forward second) =
          context.sourceRelation first second) :
    preservesRelationOn context sources transport = true :=
  rowsPreserveOn_true_of_preserves
    context transport preserves sources sources

/--
Pointwise forward agreement with a compatible exact alignment is enough for a
listed exact transport to pass the same matrix check.
-/
theorem preservesRelationOn_true_of_forwardAgreement
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : IntrinsicRelationalContext Source Target Value)
    (sources : List Source)
    (alignment : IntrinsicCompatibleExactAlignment context)
    (transport : ExactTypeTransport Source Target)
    (agreement :
      (source : Source) →
        transport.forward source = alignment.transport.forward source) :
    preservesRelationOn context sources transport = true := by
  apply preservesRelationOn_true_of_preserves
  intro first second
  calc
    context.targetRelation
        (transport.forward first)
        (transport.forward second) =
      context.targetRelation
        (alignment.transport.forward first)
        (alignment.transport.forward second) := by
      rw [agreement first, agreement second]
    _ = context.sourceRelation first second :=
      alignment.preservesRelation first second

/-- Search the candidate family for the first transport passing the full matrix check. -/
def findCompatibleTransport
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : IntrinsicRelationalContext Source Target Value)
    (sources : List Source) :
    List (ExactTypeTransport Source Target) →
      Option { transport : ExactTypeTransport Source Target //
        preservesRelationOn context sources transport = true }
  | [] => none
  | candidate :: rest =>
      match checked : preservesRelationOn context sources candidate with
      | true => some ⟨candidate, checked⟩
      | false => findCompatibleTransport context sources rest

/-- A listed passing candidate prevents the finite search from returning `none`. -/
theorem findCompatibleTransport_ne_none_of_mem_of_true
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : IntrinsicRelationalContext Source Target Value)
    (sources : List Source)
    (candidates : List (ExactTypeTransport Source Target))
    (transport : ExactTypeTransport Source Target)
    (member : transport ∈ candidates)
    (checked : preservesRelationOn context sources transport = true) :
    findCompatibleTransport context sources candidates ≠ none := by
  induction candidates with
  | nil =>
      cases member
  | cons candidate rest ih =>
      cases candidateCheck : preservesRelationOn context sources candidate with
      | true =>
          intro impossible
          change some _ = none at impossible
          cases impossible
      | false =>
          cases member with
          | head =>
              rw [checked] at candidateCheck
              cases candidateCheck
          | tail _ tailMember =>
              change
                findCompatibleTransport context sources rest ≠ none
              exact ih tailMember checked

/-- Convert a successful checked transport into the intrinsic compatible alignment. -/
def alignmentOfCheckedTransport
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : IntrinsicRelationalContext Source Target Value)
    (sources : FiniteListing Source)
    (checked :
      { transport : ExactTypeTransport Source Target //
        preservesRelationOn context sources.values transport = true }) :
    IntrinsicCompatibleExactAlignment context :=
  { transport := checked.1
    preservesRelation :=
      preservesRelation_of_true context sources checked.1 checked.2 }

/-- End-to-end finite search without a common anchor family. -/
def searchAlignment?
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : IntrinsicRelationalContext Source Target Value)
    (sources : FiniteListing Source)
    (candidates : FiniteTransportListing Source Target) :
    Option (IntrinsicCompatibleExactAlignment context) :=
  match findCompatibleTransport context sources.values candidates.values with
  | none => none
  | some checked => some (alignmentOfCheckedTransport context sources checked)

/-- Completeness of the candidate family makes intrinsic search complete for existence. -/
theorem searchAlignment_ne_none_of_alignment
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : IntrinsicRelationalContext Source Target Value)
    (sources : FiniteListing Source)
    (candidates : FiniteTransportListing Source Target)
    (alignment : IntrinsicCompatibleExactAlignment context) :
    searchAlignment? context sources candidates ≠ none := by
  let listed := candidates.complete alignment.transport
  have checked :
      preservesRelationOn context sources.values listed.1 = true :=
    preservesRelationOn_true_of_forwardAgreement
      context sources.values alignment listed.1 listed.2.2
  have foundNe :
      findCompatibleTransport context sources.values candidates.values ≠ none :=
    findCompatibleTransport_ne_none_of_mem_of_true
      context sources.values candidates.values listed.1 listed.2.1 checked
  unfold searchAlignment?
  cases found : findCompatibleTransport context sources.values candidates.values with
  | none =>
      exact (foundNe found).elim
  | some result =>
      intro impossible
      change some _ = none at impossible
      cases impossible

/-- A `none` result is a constructive non-existence certificate relative to a complete transport listing. -/
theorem noAlignment_of_search_none
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : IntrinsicRelationalContext Source Target Value)
    (sources : FiniteListing Source)
    (candidates : FiniteTransportListing Source Target)
    (failed : searchAlignment? context sources candidates = none)
    (alignment : IntrinsicCompatibleExactAlignment context) : False :=
  searchAlignment_ne_none_of_alignment
    context sources candidates alignment failed

end FiniteIntrinsicRelationalSearch
end GenesisReconstruction
end Alignment

/- AXIOM_AUDIT_BEGIN -/
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicRelationalSearch.FiniteTransportListing
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicRelationalSearch.rowPreservesOn
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicRelationalSearch.rowEquality_of_mem_of_true
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicRelationalSearch.rowsPreserveOn
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicRelationalSearch.relationEquality_of_mem_of_mem_of_rows_true
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicRelationalSearch.preservesRelationOn
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicRelationalSearch.preservesRelation_of_true
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicRelationalSearch.preservesRelationOn_true_of_forwardAgreement
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicRelationalSearch.findCompatibleTransport
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicRelationalSearch.findCompatibleTransport_ne_none_of_mem_of_true
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicRelationalSearch.alignmentOfCheckedTransport
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicRelationalSearch.searchAlignment?
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicRelationalSearch.searchAlignment_ne_none_of_alignment
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicRelationalSearch.noAlignment_of_search_none
/- AXIOM_AUDIT_END -/