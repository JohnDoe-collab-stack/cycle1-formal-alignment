import Alignment.FiniteIntrinsicFunctionEnumeration

/-!
# Finite intrinsic alignment decision from local carrier listings

This module removes the supplied `FiniteTransportListing` from the executable
intrinsic alignment layer.

Starting only from complete finite listings of the source and target carriers,
`FiniteIntrinsicFunctionEnumeration` generates extensionally complete families
of forward and backward functions.  This module pairs those local functions,
checks both round trips on the complete local carriers, and only then constructs
an `ExactTypeTransport`.  The existing full-relation checker is applied after
exactness has been reconstructed.

Thus no common anchor, mediator, cross-system pairing, exact transport, or list
of candidate transports is supplied to the search.  If the generated search
returns `none`, completeness of the local function enumerations constructively
refutes every intrinsic compatible exact alignment.
-/

namespace Alignment
namespace GenesisReconstruction
namespace FiniteIntrinsicAlignmentDecision

open FiniteAnchoredMatchSearch
open FiniteIntrinsicRelationalSearch
open FiniteIntrinsicFunctionEnumeration

universe uSource uTarget uValue

/-- A raw candidate consists only of independently generated local functions. -/
structure FunctionPair
    (Source : Type uSource)
    (Target : Type uTarget) where
  forward : Source → Target
  backward : Target → Source

/-- Check that one endomap fixes every identity in an explicit list. -/
def allFixedOn
    {Carrier : Type uSource}
    [DecidableEq Carrier]
    (function : Carrier → Carrier) : List Carrier → Bool
  | [] => true
  | identity :: rest =>
      if function identity = identity then
        allFixedOn function rest
      else
        false

/-- A successful finite fixed-point check proves every listed point is fixed. -/
theorem fixed_of_mem_of_allFixedOn_true
    {Carrier : Type uSource}
    [DecidableEq Carrier]
    (function : Carrier → Carrier)
    (identity : Carrier)
    (values : List Carrier)
    (member : identity ∈ values)
    (checked : allFixedOn function values = true) :
    function identity = identity := by
  induction values with
  | nil =>
      cases member
  | cons head tail ih =>
      by_cases headFixed : function head = head
      · change
          (if function head = head then
            allFixedOn function tail
          else
            false) = true at checked
        rw [if_pos headFixed] at checked
        cases member with
        | head => exact headFixed
        | tail _ tailMember => exact ih tailMember checked
      · change
          (if function head = head then
            allFixedOn function tail
          else
            false) = true at checked
        rw [if_neg headFixed] at checked
        cases checked

/-- A genuinely pointwise-fixed endomap passes every finite check. -/
theorem allFixedOn_true_of_fixed
    {Carrier : Type uSource}
    [DecidableEq Carrier]
    (function : Carrier → Carrier)
    (fixed : (identity : Carrier) → function identity = identity)
    (values : List Carrier) :
    allFixedOn function values = true := by
  induction values with
  | nil => rfl
  | cons identity rest ih =>
      change
        (if function identity = identity then
          allFixedOn function rest
        else
          false) = true
      rw [if_pos (fixed identity)]
      exact ih

/-- Source-side round-trip check for a raw function pair. -/
def sourceRoundTripCheck
    {Source : Type uSource}
    {Target : Type uTarget}
    [DecidableEq Source]
    (sources : FiniteListing Source)
    (candidate : FunctionPair Source Target) : Bool :=
  allFixedOn
    (fun source => candidate.backward (candidate.forward source))
    sources.values

/-- Target-side round-trip check for a raw function pair. -/
def targetRoundTripCheck
    {Source : Type uSource}
    {Target : Type uTarget}
    [DecidableEq Target]
    (targets : FiniteListing Target)
    (candidate : FunctionPair Source Target) : Bool :=
  allFixedOn
    (fun target => candidate.forward (candidate.backward target))
    targets.values

/--
Construct exact transport only after both complete local round-trip checks pass.
The proofs are reconstructed from the Boolean certificates and listing
completeness; no inverse law is stored in the raw candidate.
-/
def exactTransport?
    {Source : Type uSource}
    {Target : Type uTarget}
    [DecidableEq Source]
    [DecidableEq Target]
    (sources : FiniteListing Source)
    (targets : FiniteListing Target)
    (candidate : FunctionPair Source Target) :
    Option (ExactTypeTransport Source Target) :=
  match sourceChecked : sourceRoundTripCheck sources candidate with
  | false => none
  | true =>
      match targetChecked : targetRoundTripCheck targets candidate with
      | false => none
      | true =>
          some
            { forward := candidate.forward
              backward := candidate.backward
              forwardBackward := by
                intro source
                exact
                  fixed_of_mem_of_allFixedOn_true
                    (fun identity =>
                      candidate.backward (candidate.forward identity))
                    source
                    sources.values
                    (sources.complete source)
                    sourceChecked
              backwardForward := by
                intro target
                exact
                  fixed_of_mem_of_allFixedOn_true
                    (fun identity =>
                      candidate.forward (candidate.backward identity))
                    target
                    targets.values
                    (targets.complete target)
                    targetChecked }

/--
A candidate passes iff it first reconstructs an exact transport and that exact
transport preserves the complete intrinsic relation matrix.
-/
def candidatePasses
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    [DecidableEq Source]
    [DecidableEq Target]
    [DecidableEq Value]
    (context : IntrinsicRelationalContext Source Target Value)
    (sources : FiniteListing Source)
    (targets : FiniteListing Target)
    (candidate : FunctionPair Source Target) : Bool :=
  match exactTransport? sources targets candidate with
  | none => false
  | some transport =>
      preservesRelationOn context sources.values transport

/-- A passing raw candidate reconstructs a certified intrinsic exact alignment. -/
def alignmentOfPassingCandidate
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    [DecidableEq Source]
    [DecidableEq Target]
    [DecidableEq Value]
    (context : IntrinsicRelationalContext Source Target Value)
    (sources : FiniteListing Source)
    (targets : FiniteListing Target)
    (candidate : FunctionPair Source Target)
    (checked : candidatePasses context sources targets candidate = true) :
    IntrinsicCompatibleExactAlignment context := by
  unfold candidatePasses at checked
  cases found : exactTransport? sources targets candidate with
  | none =>
      rw [found] at checked
      cases checked
  | some transport =>
      rw [found] at checked
      exact alignmentOfFoundTransport context sources transport checked

/--
Every exact alignment makes any extensionally agreeing raw pair pass the two
round trips and the full intrinsic relation check.
-/
theorem candidatePasses_true_of_alignmentAgreement
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    [DecidableEq Source]
    [DecidableEq Target]
    [DecidableEq Value]
    (context : IntrinsicRelationalContext Source Target Value)
    (sources : FiniteListing Source)
    (targets : FiniteListing Target)
    (alignment : IntrinsicCompatibleExactAlignment context)
    (candidate : FunctionPair Source Target)
    (forwardAgreement :
      (source : Source) →
        candidate.forward source = alignment.transport.forward source)
    (backwardAgreement :
      (target : Target) →
        candidate.backward target = alignment.transport.backward target) :
    candidatePasses context sources targets candidate = true := by
  have sourceFixed :
      (source : Source) →
        candidate.backward (candidate.forward source) = source := by
    intro source
    calc
      candidate.backward (candidate.forward source) =
          alignment.transport.backward (candidate.forward source) :=
        backwardAgreement (candidate.forward source)
      _ = alignment.transport.backward
            (alignment.transport.forward source) :=
        congrArg alignment.transport.backward (forwardAgreement source)
      _ = source := alignment.transport.forwardBackward source
  have targetFixed :
      (target : Target) →
        candidate.forward (candidate.backward target) = target := by
    intro target
    calc
      candidate.forward (candidate.backward target) =
          alignment.transport.forward (candidate.backward target) :=
        forwardAgreement (candidate.backward target)
      _ = alignment.transport.forward
            (alignment.transport.backward target) :=
        congrArg alignment.transport.forward (backwardAgreement target)
      _ = target := alignment.transport.backwardForward target
  have sourceChecked : sourceRoundTripCheck sources candidate = true := by
    exact
      allFixedOn_true_of_fixed
        (fun source => candidate.backward (candidate.forward source))
        sourceFixed
        sources.values
  have targetChecked : targetRoundTripCheck targets candidate = true := by
    exact
      allFixedOn_true_of_fixed
        (fun target => candidate.forward (candidate.backward target))
        targetFixed
        targets.values
  unfold candidatePasses exactTransport?
  rw [sourceChecked, targetChecked]
  apply preservesRelationOn_true_of_forwardAgreement
  intro source
  exact forwardAgreement source

/--
All raw function pairs generated independently from the two complete local
carrier listings. No cross-system correspondence appears in this definition.
-/
def generatedPairs
    {Source : Type uSource}
    {Target : Type uTarget}
    [DecidableEq Source]
    [DecidableEq Target]
    (sources : FiniteListing Source)
    (targets : FiniteListing Target) :
    List (FunctionPair Source Target) :=
  (enumerateFunctions sources targets).values.flatMap fun forward =>
    (enumerateFunctions targets sources).values.map fun backward =>
      { forward := forward
        backward := backward }

/--
Every exact transport has a generated raw representative agreeing with both of
its maps pointwise.
-/
theorem generatedPair_of_exactTransport
    {Source : Type uSource}
    {Target : Type uTarget}
    [DecidableEq Source]
    [DecidableEq Target]
    (sources : FiniteListing Source)
    (targets : FiniteListing Target)
    (transport : ExactTypeTransport Source Target) :
    { candidate : FunctionPair Source Target //
      candidate ∈ generatedPairs sources targets ∧
        ((source : Source) →
          candidate.forward source = transport.forward source) ∧
        ((target : Target) →
          candidate.backward target = transport.backward target) } := by
  let forwardListing := enumerateFunctions sources targets
  let backwardListing := enumerateFunctions targets sources
  let forwardWitness := forwardListing.complete transport.forward
  let backwardWitness := backwardListing.complete transport.backward
  let candidate : FunctionPair Source Target :=
    { forward := forwardWitness.1
      backward := backwardWitness.1 }
  refine ⟨candidate, ?_, forwardWitness.2.2, backwardWitness.2.2⟩
  unfold generatedPairs
  apply mem_flatMap_of_mem_of_mem
    (fun forward =>
      (enumerateFunctions targets sources).values.map fun backward =>
        { forward := forward
          backward := backward })
  · exact forwardWitness.2.1
  · exact
      mem_map_of_mem
        (fun backward =>
          { forward := forwardWitness.1
            backward := backward })
        backwardWitness.2.1

/-- Search raw generated candidates for the first one passing all intrinsic checks. -/
def findPassingCandidate
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    [DecidableEq Source]
    [DecidableEq Target]
    [DecidableEq Value]
    (context : IntrinsicRelationalContext Source Target Value)
    (sources : FiniteListing Source)
    (targets : FiniteListing Target) :
    List (FunctionPair Source Target) → Option (FunctionPair Source Target)
  | [] => none
  | candidate :: rest =>
      match candidatePasses context sources targets candidate with
      | true => some candidate
      | false => findPassingCandidate context sources targets rest

/-- A listed passing raw candidate prevents the finder from returning `none`. -/
theorem findPassingCandidate_ne_none_of_mem_of_true
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    [DecidableEq Source]
    [DecidableEq Target]
    [DecidableEq Value]
    (context : IntrinsicRelationalContext Source Target Value)
    (sources : FiniteListing Source)
    (targets : FiniteListing Target)
    (candidates : List (FunctionPair Source Target))
    (candidate : FunctionPair Source Target)
    (member : candidate ∈ candidates)
    (checked : candidatePasses context sources targets candidate = true) :
    findPassingCandidate context sources targets candidates ≠ none := by
  induction candidates with
  | nil => cases member
  | cons current rest ih =>
      cases member with
      | head =>
          change
            (match candidatePasses context sources targets candidate with
            | true => some candidate
            | false => findPassingCandidate context sources targets rest) ≠ none
          rw [checked]
          intro impossible
          cases impossible
      | tail _ tailMember =>
          cases currentCheck : candidatePasses context sources targets current with
          | true =>
              change
                (match candidatePasses context sources targets current with
                | true => some current
                | false => findPassingCandidate context sources targets rest) ≠ none
              rw [currentCheck]
              intro impossible
              cases impossible
          | false =>
              change
                (match candidatePasses context sources targets current with
                | true => some current
                | false => findPassingCandidate context sources targets rest) ≠ none
              rw [currentCheck]
              exact ih tailMember

/-- Every raw candidate returned by the finder passed all checks. -/
theorem findPassingCandidate_sound
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    [DecidableEq Source]
    [DecidableEq Target]
    [DecidableEq Value]
    (context : IntrinsicRelationalContext Source Target Value)
    (sources : FiniteListing Source)
    (targets : FiniteListing Target)
    (candidates : List (FunctionPair Source Target))
    (candidate : FunctionPair Source Target)
    (found :
      findPassingCandidate context sources targets candidates = some candidate) :
    candidatePasses context sources targets candidate = true := by
  induction candidates with
  | nil =>
      change none = some candidate at found
      cases found
  | cons current rest ih =>
      cases currentCheck : candidatePasses context sources targets current with
      | true =>
          change
            (match candidatePasses context sources targets current with
            | true => some current
            | false => findPassingCandidate context sources targets rest) =
              some candidate at found
          rw [currentCheck] at found
          cases found
          exact currentCheck
      | false =>
          change
            (match candidatePasses context sources targets current with
            | true => some current
            | false => findPassingCandidate context sources targets rest) =
              some candidate at found
          rw [currentCheck] at found
          exact ih found

/-- Any intrinsic compatible exact alignment forces the generated raw search to succeed. -/
theorem generatedFinder_ne_none_of_alignment
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    [DecidableEq Source]
    [DecidableEq Target]
    [DecidableEq Value]
    (context : IntrinsicRelationalContext Source Target Value)
    (sources : FiniteListing Source)
    (targets : FiniteListing Target)
    (alignment : IntrinsicCompatibleExactAlignment context) :
    findPassingCandidate
        context sources targets (generatedPairs sources targets) ≠ none := by
  let witness :=
    generatedPair_of_exactTransport sources targets alignment.transport
  have checked :
      candidatePasses context sources targets witness.1 = true :=
    candidatePasses_true_of_alignmentAgreement
      context sources targets alignment witness.1
      witness.2.2.1 witness.2.2.2
  exact
    findPassingCandidate_ne_none_of_mem_of_true
      context sources targets (generatedPairs sources targets)
      witness.1 witness.2.1 checked

/-- A computed `none` constructively refutes every intrinsic compatible exact alignment. -/
theorem noAlignment_of_generatedFinder_none
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    [DecidableEq Source]
    [DecidableEq Target]
    [DecidableEq Value]
    (context : IntrinsicRelationalContext Source Target Value)
    (sources : FiniteListing Source)
    (targets : FiniteListing Target)
    (noneFound :
      findPassingCandidate
          context sources targets (generatedPairs sources targets) = none)
    (alignment : IntrinsicCompatibleExactAlignment context) : False :=
  (generatedFinder_ne_none_of_alignment
    context sources targets alignment) noneFound

/--
End-to-end executable intrinsic exact alignment search from the two local finite
carrier listings alone.
-/
def searchAlignmentFromListings?
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    [DecidableEq Source]
    [DecidableEq Target]
    [DecidableEq Value]
    (context : IntrinsicRelationalContext Source Target Value)
    (sources : FiniteListing Source)
    (targets : FiniteListing Target) :
    Option (IntrinsicCompatibleExactAlignment context) :=
  match found :
      findPassingCandidate
        context sources targets (generatedPairs sources targets) with
  | none => none
  | some candidate =>
      some
        (alignmentOfPassingCandidate
          context sources targets candidate
          (findPassingCandidate_sound
            context sources targets (generatedPairs sources targets)
            candidate found))

/-- Existence of an intrinsic exact alignment makes the end-to-end search succeed. -/
theorem searchAlignmentFromListings_ne_none_of_alignment
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    [DecidableEq Source]
    [DecidableEq Target]
    [DecidableEq Value]
    (context : IntrinsicRelationalContext Source Target Value)
    (sources : FiniteListing Source)
    (targets : FiniteListing Target)
    (alignment : IntrinsicCompatibleExactAlignment context) :
    searchAlignmentFromListings? context sources targets ≠ none := by
  have rawNonempty :=
    generatedFinder_ne_none_of_alignment context sources targets alignment
  unfold searchAlignmentFromListings?
  cases found :
      findPassingCandidate context sources targets (generatedPairs sources targets) with
  | none =>
      exact (rawNonempty found).elim
  | some candidate =>
      intro impossible
      cases impossible

/-- A `none` result from the end-to-end search refutes exact intrinsic alignment. -/
theorem noAlignment_of_searchAlignmentFromListings_none
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    [DecidableEq Source]
    [DecidableEq Target]
    [DecidableEq Value]
    (context : IntrinsicRelationalContext Source Target Value)
    (sources : FiniteListing Source)
    (targets : FiniteListing Target)
    (noneFound : searchAlignmentFromListings? context sources targets = none)
    (alignment : IntrinsicCompatibleExactAlignment context) : False :=
  (searchAlignmentFromListings_ne_none_of_alignment
    context sources targets alignment) noneFound

end FiniteIntrinsicAlignmentDecision
end GenesisReconstruction
end Alignment

/- AXIOM_AUDIT_BEGIN -/
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicAlignmentDecision.FunctionPair
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicAlignmentDecision.allFixedOn
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicAlignmentDecision.fixed_of_mem_of_allFixedOn_true
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicAlignmentDecision.allFixedOn_true_of_fixed
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicAlignmentDecision.sourceRoundTripCheck
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicAlignmentDecision.targetRoundTripCheck
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicAlignmentDecision.exactTransport?
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicAlignmentDecision.candidatePasses
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicAlignmentDecision.alignmentOfPassingCandidate
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicAlignmentDecision.candidatePasses_true_of_alignmentAgreement
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicAlignmentDecision.generatedPairs
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicAlignmentDecision.generatedPair_of_exactTransport
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicAlignmentDecision.findPassingCandidate
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicAlignmentDecision.findPassingCandidate_ne_none_of_mem_of_true
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicAlignmentDecision.findPassingCandidate_sound
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicAlignmentDecision.generatedFinder_ne_none_of_alignment
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicAlignmentDecision.noAlignment_of_generatedFinder_none
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicAlignmentDecision.searchAlignmentFromListings?
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicAlignmentDecision.searchAlignmentFromListings_ne_none_of_alignment
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicAlignmentDecision.noAlignment_of_searchAlignmentFromListings_none
/- AXIOM_AUDIT_END -/
