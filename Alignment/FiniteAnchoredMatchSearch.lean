import Alignment.AnchoredMatchStrictness

/-!
# Executable finite search for anchored structural alignment

The anchored match relation already determines at most one counterpart on each
side when the anchored profiles separate identities. The remaining obligation
was existence: total matching witnesses were still supplied as external data.

This module isolates a finite constructive case in which those witnesses can be
searched for. A finite listing is positive data: it contains an explicit list
and a proof that every element occurs in that list. Given decidable equality on
observation values, anchored profile agreement can then be checked by a Boolean
procedure over a complete anchor listing.

Forward and backward searches inspect complete carrier listings. Global Boolean
checks certify that every listed source and every listed target has a match.
From successful checks the corresponding subtype witnesses are constructed, so
`TotalAnchoredMatching`, exact transport, and finite genesis transport no longer
need an independently supplied resolver in this finite setting.
-/

namespace Alignment
namespace GenesisReconstruction
namespace FiniteAnchoredMatchSearch

universe uSource uTarget uAnchor uValue uA uB

/-- Explicit finite enumeration with constructive coverage of the carrier. -/
structure FiniteListing (A : Type uA) where
  values : List A
  complete : ∀ value : A, value ∈ values

/--
Boolean agreement of two anchored profiles on an explicit anchor list.
-/
def matchesOn
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : AnchoredRelationContext Source Target Anchor Value) :
    List Anchor → Source → Target → Bool
  | [], _, _ => true
  | anchor :: rest, source, target =>
      if context.targetRelation (context.targetAnchor anchor) target =
          context.sourceRelation (context.sourceAnchor anchor) source then
        matchesOn context rest source target
      else
        false

/-- A successful finite check proves every equality appearing in the checked list. -/
theorem anchoredEquality_of_mem_of_matchesOn_true
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : AnchoredRelationContext Source Target Anchor Value)
    (anchors : List Anchor)
    (source : Source)
    (target : Target)
    (anchor : Anchor)
    (member : anchor ∈ anchors)
    (checked : matchesOn context anchors source target = true) :
    context.targetRelation (context.targetAnchor anchor) target =
      context.sourceRelation (context.sourceAnchor anchor) source := by
  induction anchors with
  | nil =>
      cases member
  | cons head tail ih =>
      by_cases headEq :
          context.targetRelation (context.targetAnchor head) target =
            context.sourceRelation (context.sourceAnchor head) source
      · have tailChecked : matchesOn context tail source target = true := by
          change
            (if context.targetRelation (context.targetAnchor head) target =
                context.sourceRelation (context.sourceAnchor head) source then
              matchesOn context tail source target
            else
              false) = true at checked
          rw [if_pos headEq] at checked
          exact checked
        cases member with
        | head =>
            exact headEq
        | tail _ tailMember =>
            exact ih tailMember tailChecked
      · change
          (if context.targetRelation (context.targetAnchor head) target =
              context.sourceRelation (context.sourceAnchor head) source then
            matchesOn context tail source target
          else
            false) = true at checked
        rw [if_neg headEq] at checked
        cases checked

/-- Complete anchor coverage upgrades the Boolean check to the original match relation. -/
theorem matches_of_matchesOn_true
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : AnchoredRelationContext Source Target Anchor Value)
    (anchors : FiniteListing Anchor)
    (source : Source)
    (target : Target)
    (checked : matchesOn context anchors.values source target = true) :
    context.Matches source target := by
  intro anchor
  exact
    anchoredEquality_of_mem_of_matchesOn_true
      context anchors.values source target anchor
      (anchors.complete anchor) checked

/-- Any genuine anchored match passes every finite anchor check. -/
theorem matchesOn_true_of_matches
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : AnchoredRelationContext Source Target Anchor Value)
    (anchors : List Anchor)
    (source : Source)
    (target : Target)
    (matching : context.Matches source target) :
    matchesOn context anchors source target = true := by
  induction anchors with
  | nil =>
      rfl
  | cons head tail ih =>
      have headEq := matching head
      change
        (if context.targetRelation (context.targetAnchor head) target =
            context.sourceRelation (context.sourceAnchor head) source then
          matchesOn context tail source target
        else
          false) = true
      rw [if_pos headEq]
      exact ih

/-- Search a target list for the first target whose anchored profile matches a source. -/
def findTarget
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : AnchoredRelationContext Source Target Anchor Value)
    (anchors : List Anchor)
    (source : Source) :
    List Target → Option Target
  | [] => none
  | candidate :: rest =>
      match matchesOn context anchors source candidate with
      | true => some candidate
      | false => findTarget context anchors source rest

/-- Search a source list for the first source whose anchored profile matches a target. -/
def findSource
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : AnchoredRelationContext Source Target Anchor Value)
    (anchors : List Anchor)
    (target : Target) :
    List Source → Option Source
  | [] => none
  | candidate :: rest =>
      match matchesOn context anchors candidate target with
      | true => some candidate
      | false => findSource context anchors target rest

/-- Any target returned by the executable search passed the anchored check. -/
theorem findTarget_sound
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : AnchoredRelationContext Source Target Anchor Value)
    (anchors : List Anchor)
    (source : Source)
    (candidates : List Target)
    (target : Target)
    (found : findTarget context anchors source candidates = some target) :
    matchesOn context anchors source target = true := by
  induction candidates with
  | nil =>
      change none = some target at found
      cases found
  | cons candidate rest ih =>
      cases check : matchesOn context anchors source candidate with
      | false =>
          change
            (match matchesOn context anchors source candidate with
            | true => some candidate
            | false => findTarget context anchors source rest) = some target at found
          rw [check] at found
          exact ih found
      | true =>
          change
            (match matchesOn context anchors source candidate with
            | true => some candidate
            | false => findTarget context anchors source rest) = some target at found
          rw [check] at found
          cases found
          exact check

/-- Any source returned by the executable reverse search passed the anchored check. -/
theorem findSource_sound
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : AnchoredRelationContext Source Target Anchor Value)
    (anchors : List Anchor)
    (target : Target)
    (candidates : List Source)
    (source : Source)
    (found : findSource context anchors target candidates = some source) :
    matchesOn context anchors source target = true := by
  induction candidates with
  | nil =>
      change none = some source at found
      cases found
  | cons candidate rest ih =>
      cases check : matchesOn context anchors candidate target with
      | false =>
          change
            (match matchesOn context anchors candidate target with
            | true => some candidate
            | false => findSource context anchors target rest) = some source at found
          rw [check] at found
          exact ih found
      | true =>
          change
            (match matchesOn context anchors candidate target with
            | true => some candidate
            | false => findSource context anchors target rest) = some source at found
          rw [check] at found
          cases found
          exact check

/-- Boolean assertion that a search succeeds for every value in an explicit list. -/
def allFound
    {A : Type uA}
    {B : Type uB}
    (find : A → Option B) :
    List A → Bool
  | [] => true
  | value :: rest =>
      match find value with
      | none => false
      | some _ => allFound find rest

/-- A successful global check rules out `none` for every member of the checked list. -/
theorem find_ne_none_of_mem_of_allFound_true
    {A : Type uA}
    {B : Type uB}
    (find : A → Option B)
    (values : List A)
    (value : A)
    (member : value ∈ values)
    (checked : allFound find values = true) :
    find value ≠ none := by
  induction values with
  | nil =>
      cases member
  | cons head tail ih =>
      cases headFound : find head with
      | none =>
          change
            (match find head with
            | none => false
            | some _ => allFound find tail) = true at checked
          rw [headFound] at checked
          cases checked
      | some result =>
          have tailChecked : allFound find tail = true := by
            change
              (match find head with
              | none => false
              | some _ => allFound find tail) = true at checked
            rw [headFound] at checked
            exact checked
          cases member with
          | head =>
              intro impossible
              rw [impossible] at headFound
              cases headFound
          | tail _ tailMember =>
              exact ih tailMember tailChecked

/-- Executable forward-totality check on complete finite source and target listings. -/
def forwardTotalCheck
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : AnchoredRelationContext Source Target Anchor Value)
    (anchors : FiniteListing Anchor)
    (sources : FiniteListing Source)
    (targets : FiniteListing Target) : Bool :=
  allFound
    (fun source => findTarget context anchors.values source targets.values)
    sources.values

/-- Executable backward-totality check on complete finite source and target listings. -/
def backwardTotalCheck
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : AnchoredRelationContext Source Target Anchor Value)
    (anchors : FiniteListing Anchor)
    (sources : FiniteListing Source)
    (targets : FiniteListing Target) : Bool :=
  allFound
    (fun target => findSource context anchors.values target sources.values)
    targets.values

/-- Successful forward totality makes the executable search defined on every source. -/
theorem forwardSearch_ne_none
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : AnchoredRelationContext Source Target Anchor Value)
    (anchors : FiniteListing Anchor)
    (sources : FiniteListing Source)
    (targets : FiniteListing Target)
    (checked : forwardTotalCheck context anchors sources targets = true)
    (source : Source) :
    findTarget context anchors.values source targets.values ≠ none :=
  find_ne_none_of_mem_of_allFound_true
    (fun current => findTarget context anchors.values current targets.values)
    sources.values source (sources.complete source) checked

/-- Successful backward totality makes the reverse search defined on every target. -/
theorem backwardSearch_ne_none
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : AnchoredRelationContext Source Target Anchor Value)
    (anchors : FiniteListing Anchor)
    (sources : FiniteListing Source)
    (targets : FiniteListing Target)
    (checked : backwardTotalCheck context anchors sources targets = true)
    (target : Target) :
    findSource context anchors.values target sources.values ≠ none :=
  find_ne_none_of_mem_of_allFound_true
    (fun current => findSource context anchors.values current sources.values)
    targets.values target (targets.complete target) checked

/-- Construct the positive forward matching witness from a successful finite check. -/
def forwardWitnessOfCheck
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : AnchoredRelationContext Source Target Anchor Value)
    (anchors : FiniteListing Anchor)
    (sources : FiniteListing Source)
    (targets : FiniteListing Target)
    (checked : forwardTotalCheck context anchors sources targets = true)
    (source : Source) :
    { target : Target // context.Matches source target } :=
  match found : findTarget context anchors.values source targets.values with
  | none =>
      False.elim ((forwardSearch_ne_none context anchors sources targets checked source) found)
  | some target =>
      ⟨target,
        matches_of_matchesOn_true
          context anchors source target
          (findTarget_sound
            context anchors.values source targets.values target found)⟩

/-- Construct the positive backward matching witness from a successful finite check. -/
def backwardWitnessOfCheck
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : AnchoredRelationContext Source Target Anchor Value)
    (anchors : FiniteListing Anchor)
    (sources : FiniteListing Source)
    (targets : FiniteListing Target)
    (checked : backwardTotalCheck context anchors sources targets = true)
    (target : Target) :
    { source : Source // context.Matches source target } :=
  match found : findSource context anchors.values target sources.values with
  | none =>
      False.elim ((backwardSearch_ne_none context anchors sources targets checked target) found)
  | some source =>
      ⟨source,
        matches_of_matchesOn_true
          context anchors source target
          (findSource_sound
            context anchors.values target sources.values source found)⟩

/--
Successful finite searches in both directions construct total anchored matching.
No forward or backward resolver is supplied independently.
-/
def totalMatchingOfChecks
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : AnchoredRelationContext Source Target Anchor Value)
    (anchors : FiniteListing Anchor)
    (sources : FiniteListing Source)
    (targets : FiniteListing Target)
    (forwardChecked : forwardTotalCheck context anchors sources targets = true)
    (backwardChecked : backwardTotalCheck context anchors sources targets = true) :
    TotalAnchoredMatching context :=
  { forwardWitness :=
      forwardWitnessOfCheck context anchors sources targets forwardChecked
    backwardWitness :=
      backwardWitnessOfCheck context anchors sources targets backwardChecked }

/--
Run both finite totality checks and return a total structural matching exactly
when both searches succeed.
-/
def searchTotalMatching?
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : AnchoredRelationContext Source Target Anchor Value)
    (anchors : FiniteListing Anchor)
    (sources : FiniteListing Source)
    (targets : FiniteListing Target) :
    Option (TotalAnchoredMatching context) :=
  if forwardChecked : forwardTotalCheck context anchors sources targets = true then
    if backwardChecked : backwardTotalCheck context anchors sources targets = true then
      some
        (totalMatchingOfChecks
          context anchors sources targets forwardChecked backwardChecked)
    else
      none
  else
    none

/-- Search directly for the exact initial transport induced by finite structural matching. -/
def searchExactTransport?
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : AnchoredRelationContext Source Target Anchor Value)
    (anchors : FiniteListing Anchor)
    (sources : FiniteListing Source)
    (targets : FiniteListing Target) :
    Option (ExactTypeTransport Source Target) :=
  (searchTotalMatching? context anchors sources targets).map
    TotalAnchoredMatching.toExactTransport

/-- Search for the corresponding exact transport at any finite genesis depth. -/
def searchFiniteTransport?
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : AnchoredRelationContext Source Target Anchor Value)
    (anchors : FiniteListing Anchor)
    (sources : FiniteListing Source)
    (targets : FiniteListing Target)
    (depth : Nat) :
    Option
      (ExactTypeTransport
        (IteratedCarrier Source depth)
        (IteratedCarrier Target depth)) :=
  (searchTotalMatching? context anchors sources targets).map
    (fun matching => matching.finiteTransport depth)

end FiniteAnchoredMatchSearch
end GenesisReconstruction
end Alignment

/- AXIOM_AUDIT_BEGIN -/
#print axioms Alignment.GenesisReconstruction.FiniteAnchoredMatchSearch.FiniteListing
#print axioms Alignment.GenesisReconstruction.FiniteAnchoredMatchSearch.matchesOn
#print axioms Alignment.GenesisReconstruction.FiniteAnchoredMatchSearch.anchoredEquality_of_mem_of_matchesOn_true
#print axioms Alignment.GenesisReconstruction.FiniteAnchoredMatchSearch.matches_of_matchesOn_true
#print axioms Alignment.GenesisReconstruction.FiniteAnchoredMatchSearch.matchesOn_true_of_matches
#print axioms Alignment.GenesisReconstruction.FiniteAnchoredMatchSearch.findTarget
#print axioms Alignment.GenesisReconstruction.FiniteAnchoredMatchSearch.findSource
#print axioms Alignment.GenesisReconstruction.FiniteAnchoredMatchSearch.findTarget_sound
#print axioms Alignment.GenesisReconstruction.FiniteAnchoredMatchSearch.findSource_sound
#print axioms Alignment.GenesisReconstruction.FiniteAnchoredMatchSearch.allFound
#print axioms Alignment.GenesisReconstruction.FiniteAnchoredMatchSearch.find_ne_none_of_mem_of_allFound_true
#print axioms Alignment.GenesisReconstruction.FiniteAnchoredMatchSearch.forwardTotalCheck
#print axioms Alignment.GenesisReconstruction.FiniteAnchoredMatchSearch.backwardTotalCheck
#print axioms Alignment.GenesisReconstruction.FiniteAnchoredMatchSearch.forwardSearch_ne_none
#print axioms Alignment.GenesisReconstruction.FiniteAnchoredMatchSearch.backwardSearch_ne_none
#print axioms Alignment.GenesisReconstruction.FiniteAnchoredMatchSearch.forwardWitnessOfCheck
#print axioms Alignment.GenesisReconstruction.FiniteAnchoredMatchSearch.backwardWitnessOfCheck
#print axioms Alignment.GenesisReconstruction.FiniteAnchoredMatchSearch.totalMatchingOfChecks
#print axioms Alignment.GenesisReconstruction.FiniteAnchoredMatchSearch.searchTotalMatching?
#print axioms Alignment.GenesisReconstruction.FiniteAnchoredMatchSearch.searchExactTransport?
#print axioms Alignment.GenesisReconstruction.FiniteAnchoredMatchSearch.searchFiniteTransport?
/- AXIOM_AUDIT_END -/
