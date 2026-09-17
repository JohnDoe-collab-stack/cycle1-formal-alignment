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

The search checks the complete source relation matrix. The executable finder
returns only raw transport data. A separate soundness theorem then reconstructs
the proof that a found transport preserves the complete relation. This
separation keeps computation independent from its certificate and avoids a
dependent search result whose recursive reduction would obscure constructivity.

A successful search constructs `IntrinsicCompatibleExactAlignment`. With a
complete candidate listing, `none` from the raw finder constructively refutes
every compatible exact relational alignment.

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
  | cons current rest ih =>
      cases rowCheck : rowPreservesOn context transport current allSources with
      | false =>
          change
            (match rowPreservesOn context transport current allSources with
            | true => rowsPreserveOn context transport allSources rest
            | false => false) = true at checked
          rw [rowCheck] at checked
          cases checked
      | true =>
          have tailChecked :
              rowsPreserveOn context transport allSources rest = true := by
            change
              (match rowPreservesOn context transport current allSources with
              | true => rowsPreserveOn context transport allSources rest
              | false => false) = true at checked
            rw [rowCheck] at checked
            exact checked
          cases firstMember with
          | head =>
              exact rowEquality_of_mem_of_true
                context transport first second allSources
                secondMember rowCheck
          | tail _ tailMember =>
              exact ih tailMember tailChecked

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

/--
Search the candidate family for the first transport passing the full matrix
check. The executable result contains only the transport. Its preservation proof
is reconstructed separately by `findCompatibleTransport_sound`.
-/
def findCompatibleTransport
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : IntrinsicRelationalContext Source Target Value)
    (sources : List Source) :
    List (ExactTypeTransport Source Target) →
      Option (ExactTypeTransport Source Target)
  | [] => none
  | candidate :: rest =>
      match preservesRelationOn context sources candidate with
      | true => some candidate
      | false => findCompatibleTransport context sources rest

/-- A listed passing candidate prevents the raw finite search from returning `none`. -/
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
      cases member with
      | head =>
          change
            (match preservesRelationOn context sources transport with
            | true => some transport
            | false => findCompatibleTransport context sources rest) ≠ none
          rw [checked]
          intro impossible
          cases impossible
      | tail _ tailMember =>
          cases candidateCheck : preservesRelationOn context sources candidate with
          | true =>
              change
                (match preservesRelationOn context sources candidate with
                | true => some candidate
                | false => findCompatibleTransport context sources rest) ≠ none
              rw [candidateCheck]
              intro impossible
              cases impossible
          | false =>
              change
                (match preservesRelationOn context sources candidate with
                | true => some candidate
                | false => findCompatibleTransport context sources rest) ≠ none
              rw [candidateCheck]
              exact ih tailMember

/-- Every transport returned by the raw finder passes the matrix check. -/
theorem findCompatibleTransport_sound
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : IntrinsicRelationalContext Source Target Value)
    (sources : List Source)
    (candidates : List (ExactTypeTransport Source Target))
    (transport : ExactTypeTransport Source Target)
    (found :
      findCompatibleTransport context sources candidates = some transport) :
    preservesRelationOn context sources transport = true := by
  induction candidates with
  | nil =>
      change none = some transport at found
      cases found
  | cons candidate rest ih =>
      cases candidateCheck : preservesRelationOn context sources candidate with
      | true =>
          change
            (match preservesRelationOn context sources candidate with
            | true => some candidate
            | false => findCompatibleTransport context sources rest) =
              some transport at found
          rw [candidateCheck] at found
          cases found
          exact candidateCheck
      | false =>
          change
            (match preservesRelationOn context sources candidate with
            | true => some candidate
            | false => findCompatibleTransport context sources rest) =
              some transport at found
          rw [candidateCheck] at found
          exact ih found

/-- Convert a raw found transport and its reconstructed check into an alignment. -/
def alignmentOfFoundTransport
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : IntrinsicRelationalContext Source Target Value)
    (sources : FiniteListing Source)
    (transport : ExactTypeTransport Source Target)
    (checked : preservesRelationOn context sources.values transport = true) :
    IntrinsicCompatibleExactAlignment context :=
  { transport := transport
    preservesRelation :=
      preservesRelation_of_true context sources transport checked }

/-- End-to-end positive search without a common anchor family. -/
def searchAlignment?
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : IntrinsicRelationalContext Source Target Value)
    (sources : FiniteListing Source)
    (candidates : FiniteTransportListing Source Target) :
    Option (IntrinsicCompatibleExactAlignment context) :=
  match found : findCompatibleTransport context sources.values candidates.values with
  | none => none
  | some transport =>
      some
        (alignmentOfFoundTransport
          context sources transport
          (findCompatibleTransport_sound
            context sources.values candidates.values transport found))

/--
Completeness of the candidate family ensures that any compatible alignment makes
the raw executable finder succeed.
-/
theorem findCompatibleTransport_ne_none_of_alignment
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : IntrinsicRelationalContext Source Target Value)
    (sources : FiniteListing Source)
    (candidates : FiniteTransportListing Source Target)
    (alignment : IntrinsicCompatibleExactAlignment context) :
    findCompatibleTransport context sources.values candidates.values ≠ none := by
  let listed := candidates.complete alignment.transport
  have checked :
      preservesRelationOn context sources.values listed.1 = true :=
    preservesRelationOn_true_of_forwardAgreement
      context sources.values alignment listed.1 listed.2.2
  exact
    findCompatibleTransport_ne_none_of_mem_of_true
      context sources.values candidates.values listed.1 listed.2.1 checked

/--
A raw `none` result is a constructive non-existence certificate relative to a
complete transport listing.
-/
theorem noAlignment_of_findCompatibleTransport_none
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : IntrinsicRelationalContext Source Target Value)
    (sources : FiniteListing Source)
    (candidates : FiniteTransportListing Source Target)
    (failed :
      findCompatibleTransport context sources.values candidates.values = none)
    (alignment : IntrinsicCompatibleExactAlignment context) : False :=
  findCompatibleTransport_ne_none_of_alignment
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
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicRelationalSearch.findCompatibleTransport_sound
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicRelationalSearch.alignmentOfFoundTransport
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicRelationalSearch.searchAlignment?
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicRelationalSearch.findCompatibleTransport_ne_none_of_alignment
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicRelationalSearch.noAlignment_of_findCompatibleTransport_none
/- AXIOM_AUDIT_END -/