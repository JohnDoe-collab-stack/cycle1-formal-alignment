import Alignment.FiniteIntrinsicFunctionEnumeration

/-!
# Finite intrinsic alignment decision from local carrier listings

This module removes the supplied `FiniteTransportListing` from the executable
intrinsic alignment layer.

Starting only from complete finite listings of the source and target carriers,
`FiniteIntrinsicFunctionEnumeration` generates extensionally complete families
of forward and backward functions. This module pairs those local functions,
checks both round trips on the complete local carriers, checks the intrinsic
relation directly on the raw forward map, and only then constructs an
`ExactTypeTransport`.

Thus no common anchor, mediator, cross-system pairing, exact transport, or list
of candidate transports is supplied to the search. If the generated raw search
returns `none`, completeness of the local function enumerations constructively
refutes every intrinsic compatible exact alignment.
-/

namespace Alignment
namespace GenesisReconstruction
namespace FiniteIntrinsicAlignmentDecision

open FiniteAnchoredMatchSearch
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
  | nil => cases member
  | cons head tail ih =>
      by_cases headFixed : function head = head
      · change
          (if function head = head then allFixedOn function tail else false) = true
          at checked
        rw [if_pos headFixed] at checked
        cases member with
        | head => exact headFixed
        | tail _ tailMember => exact ih tailMember checked
      · change
          (if function head = head then allFixedOn function tail else false) = true
          at checked
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
        (if function identity = identity then allFixedOn function rest else false) = true
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

/-- Check one row of the intrinsic relation matrix using only a raw forward map. -/
def rowPreservesForwardOn
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : IntrinsicRelationalContext Source Target Value)
    (forward : Source → Target)
    (first : Source) : List Source → Bool
  | [] => true
  | second :: rest =>
      if context.targetRelation (forward first) (forward second) =
          context.sourceRelation first second then
        rowPreservesForwardOn context forward first rest
      else
        false

/-- A successful raw row check proves every checked relation entry. -/
theorem rowEquality_of_mem_of_forwardRow_true
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : IntrinsicRelationalContext Source Target Value)
    (forward : Source → Target)
    (first second : Source)
    (sources : List Source)
    (member : second ∈ sources)
    (checked : rowPreservesForwardOn context forward first sources = true) :
    context.targetRelation (forward first) (forward second) =
      context.sourceRelation first second := by
  induction sources with
  | nil => cases member
  | cons head tail ih =>
      by_cases headExact :
          context.targetRelation (forward first) (forward head) =
            context.sourceRelation first head
      · change
          (if context.targetRelation (forward first) (forward head) =
              context.sourceRelation first head then
            rowPreservesForwardOn context forward first tail
          else false) = true at checked
        rw [if_pos headExact] at checked
        cases member with
        | head => exact headExact
        | tail _ tailMember => exact ih tailMember checked
      · change
          (if context.targetRelation (forward first) (forward head) =
              context.sourceRelation first head then
            rowPreservesForwardOn context forward first tail
          else false) = true at checked
        rw [if_neg headExact] at checked
        cases checked

/-- Check all requested rows against one fixed column list. -/
def rowsPreserveForwardOn
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : IntrinsicRelationalContext Source Target Value)
    (forward : Source → Target)
    (allSources : List Source) : List Source → Bool
  | [] => true
  | first :: rest =>
      match rowPreservesForwardOn context forward first allSources with
      | true => rowsPreserveForwardOn context forward allSources rest
      | false => false

/-- Successful raw matrix checking proves any listed row/column entry. -/
theorem relationEquality_of_mem_of_mem_of_forwardRows_true
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : IntrinsicRelationalContext Source Target Value)
    (forward : Source → Target)
    (allSources rows : List Source)
    (first second : Source)
    (firstMember : first ∈ rows)
    (secondMember : second ∈ allSources)
    (checked : rowsPreserveForwardOn context forward allSources rows = true) :
    context.targetRelation (forward first) (forward second) =
      context.sourceRelation first second := by
  induction rows with
  | nil => cases firstMember
  | cons current rest ih =>
      cases rowCheck : rowPreservesForwardOn context forward current allSources with
      | false =>
          change
            (match rowPreservesForwardOn context forward current allSources with
            | true => rowsPreserveForwardOn context forward allSources rest
            | false => false) = true at checked
          rw [rowCheck] at checked
          cases checked
      | true =>
          have tailChecked :
              rowsPreserveForwardOn context forward allSources rest = true := by
            change
              (match rowPreservesForwardOn context forward current allSources with
              | true => rowsPreserveForwardOn context forward allSources rest
              | false => false) = true at checked
            rw [rowCheck] at checked
            exact checked
          cases firstMember with
          | head =>
              exact
                rowEquality_of_mem_of_forwardRow_true
                  context forward first second allSources secondMember rowCheck
          | tail _ tailMember =>
              exact ih tailMember tailChecked

/-- Boolean preservation test for the complete raw forward relation matrix. -/
def preservesForwardRelationOn
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : IntrinsicRelationalContext Source Target Value)
    (sources : List Source)
    (forward : Source → Target) : Bool :=
  rowsPreserveForwardOn context forward sources sources

/-- Complete source enumeration upgrades raw matrix success to full preservation. -/
theorem preservesForwardRelation_of_true
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : IntrinsicRelationalContext Source Target Value)
    (sources : FiniteListing Source)
    (forward : Source → Target)
    (checked : preservesForwardRelationOn context sources.values forward = true) :
    (first second : Source) →
      context.targetRelation (forward first) (forward second) =
        context.sourceRelation first second := by
  intro first second
  exact
    relationEquality_of_mem_of_mem_of_forwardRows_true
      context forward sources.values sources.values first second
      (sources.complete first) (sources.complete second) checked

/-- A genuinely relation-preserving raw forward map passes every matrix check. -/
theorem rowPreservesForwardOn_true_of_preserves
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : IntrinsicRelationalContext Source Target Value)
    (forward : Source → Target)
    (preserves :
      (first second : Source) →
        context.targetRelation (forward first) (forward second) =
          context.sourceRelation first second)
    (first : Source)
    (sources : List Source) :
    rowPreservesForwardOn context forward first sources = true := by
  induction sources with
  | nil => rfl
  | cons second rest ih =>
      change
        (if context.targetRelation (forward first) (forward second) =
            context.sourceRelation first second then
          rowPreservesForwardOn context forward first rest
        else false) = true
      rw [if_pos (preserves first second)]
      exact ih

/-- Full raw relation preservation passes every finite matrix check. -/
theorem rowsPreserveForwardOn_true_of_preserves
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : IntrinsicRelationalContext Source Target Value)
    (forward : Source → Target)
    (preserves :
      (first second : Source) →
        context.targetRelation (forward first) (forward second) =
          context.sourceRelation first second)
    (allSources rows : List Source) :
    rowsPreserveForwardOn context forward allSources rows = true := by
  induction rows with
  | nil => rfl
  | cons first rest ih =>
      have rowChecked :=
        rowPreservesForwardOn_true_of_preserves
          context forward preserves first allSources
      change
        (match rowPreservesForwardOn context forward first allSources with
        | true => rowsPreserveForwardOn context forward allSources rest
        | false => false) = true
      rw [rowChecked]
      exact ih

/-- A preserving raw forward map passes the complete listed relation matrix. -/
theorem preservesForwardRelationOn_true_of_preserves
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : IntrinsicRelationalContext Source Target Value)
    (forward : Source → Target)
    (preserves :
      (first second : Source) →
        context.targetRelation (forward first) (forward second) =
          context.sourceRelation first second)
    (sources : List Source) :
    preservesForwardRelationOn context sources forward = true :=
  rowsPreserveForwardOn_true_of_preserves
    context forward preserves sources sources

/--
A candidate passes exactly when both local round trips and the raw forward
relation matrix pass. No proof-bearing transport is needed to compute this Bool.
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
  match sourceRoundTripCheck sources candidate with
  | false => false
  | true =>
      match targetRoundTripCheck targets candidate with
      | false => false
      | true =>
          preservesForwardRelationOn context sources.values candidate.forward

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
  cases sourceChecked : sourceRoundTripCheck sources candidate with
  | false =>
      unfold candidatePasses at checked
      rw [sourceChecked] at checked
      cases checked
  | true =>
      cases targetChecked : targetRoundTripCheck targets candidate with
      | false =>
          unfold candidatePasses at checked
          rw [sourceChecked, targetChecked] at checked
          cases checked
      | true =>
          have relationChecked :
              preservesForwardRelationOn
                  context sources.values candidate.forward = true := by
            unfold candidatePasses at checked
            rw [sourceChecked, targetChecked] at checked
            exact checked
          exact
            { transport :=
                { forward := candidate.forward
                  backward := candidate.backward
                  forwardBackward := by
                    intro source
                    exact
                      fixed_of_mem_of_allFixedOn_true
                        (fun identity =>
                          candidate.backward (candidate.forward identity))
                        source sources.values (sources.complete source)
                        sourceChecked
                  backwardForward := by
                    intro target
                    exact
                      fixed_of_mem_of_allFixedOn_true
                        (fun identity =>
                          candidate.forward (candidate.backward identity))
                        target targets.values (targets.complete target)
                        targetChecked }
              preservesRelation :=
                preservesForwardRelation_of_true
                  context sources candidate.forward relationChecked }

/--
Every exact alignment makes any extensionally agreeing raw pair pass both round
trips and the full intrinsic relation check.
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
  have sourceChecked : sourceRoundTripCheck sources candidate = true :=
    allFixedOn_true_of_fixed
      (fun source => candidate.backward (candidate.forward source))
      sourceFixed sources.values
  have targetChecked : targetRoundTripCheck targets candidate = true :=
    allFixedOn_true_of_fixed
      (fun target => candidate.forward (candidate.backward target))
      targetFixed targets.values
  have relationPreserved :
      (first second : Source) →
        context.targetRelation
            (candidate.forward first) (candidate.forward second) =
          context.sourceRelation first second := by
    intro first second
    calc
      context.targetRelation
          (candidate.forward first) (candidate.forward second) =
        context.targetRelation
          (alignment.transport.forward first)
          (alignment.transport.forward second) := by
            rw [forwardAgreement first, forwardAgreement second]
      _ = context.sourceRelation first second :=
        alignment.preservesRelation first second
  have relationChecked :
      preservesForwardRelationOn
          context sources.values candidate.forward = true :=
    preservesForwardRelationOn_true_of_preserves
      context candidate.forward relationPreserved sources.values
  unfold candidatePasses
  rw [sourceChecked, targetChecked]
  exact relationChecked

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
Every exact transport has a generated raw representative agreeing pointwise
with both of its maps.
-/
def generatedPairOfExactTransport
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
  let forwardWitness :=
    (enumerateFunctions sources targets).complete transport.forward
  let backwardWitness :=
    (enumerateFunctions targets sources).complete transport.backward
  let candidate : FunctionPair Source Target :=
    { forward := forwardWitness.1
      backward := backwardWitness.1 }
  have backwardMember :
      candidate ∈
        (enumerateFunctions targets sources).values.map
          (fun backward : Target → Source =>
            ({ forward := forwardWitness.1
               backward := backward } : FunctionPair Source Target)) := by
    change
      ({ forward := forwardWitness.1
         backward := backwardWitness.1 } : FunctionPair Source Target) ∈
        (enumerateFunctions targets sources).values.map
          (fun backward : Target → Source =>
            ({ forward := forwardWitness.1
               backward := backward } : FunctionPair Source Target))
    exact
      mem_map_of_mem
        (fun backward : Target → Source =>
          ({ forward := forwardWitness.1
             backward := backward } : FunctionPair Source Target))
        backwardWitness.2.1
  have candidateMember : candidate ∈ generatedPairs sources targets := by
    unfold generatedPairs
    exact
      mem_flatMap_of_mem_of_mem
        (fun forward : Source → Target =>
          (enumerateFunctions targets sources).values.map
            (fun backward : Target → Source =>
              ({ forward := forward
                 backward := backward } : FunctionPair Source Target)))
        forwardWitness.2.1
        backwardMember
  refine ⟨candidate, candidateMember, ?_, ?_⟩
  · exact forwardWitness.2.2
  · exact backwardWitness.2.2

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
    generatedPairOfExactTransport sources targets alignment.transport
  have checked : candidatePasses context sources targets witness.1 = true :=
    candidatePasses_true_of_alignmentAgreement
      context sources targets alignment witness.1
      witness.2.2.1 witness.2.2.2
  exact
    findPassingCandidate_ne_none_of_mem_of_true
      context sources targets (generatedPairs sources targets)
      witness.1 witness.2.1 checked

/-- A computed raw `none` constructively refutes every intrinsic exact alignment. -/
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

/-- End-to-end positive wrapper from local listings alone. -/
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
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicAlignmentDecision.rowPreservesForwardOn
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicAlignmentDecision.rowEquality_of_mem_of_forwardRow_true
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicAlignmentDecision.rowsPreserveForwardOn
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicAlignmentDecision.relationEquality_of_mem_of_mem_of_forwardRows_true
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicAlignmentDecision.preservesForwardRelationOn
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicAlignmentDecision.preservesForwardRelation_of_true
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicAlignmentDecision.rowPreservesForwardOn_true_of_preserves
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicAlignmentDecision.rowsPreserveForwardOn_true_of_preserves
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicAlignmentDecision.preservesForwardRelationOn_true_of_preserves
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicAlignmentDecision.candidatePasses
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicAlignmentDecision.alignmentOfPassingCandidate
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicAlignmentDecision.candidatePasses_true_of_alignmentAgreement
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicAlignmentDecision.generatedPairs
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicAlignmentDecision.generatedPairOfExactTransport
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicAlignmentDecision.findPassingCandidate
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicAlignmentDecision.findPassingCandidate_ne_none_of_mem_of_true
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicAlignmentDecision.findPassingCandidate_sound
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicAlignmentDecision.generatedFinder_ne_none_of_alignment
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicAlignmentDecision.noAlignment_of_generatedFinder_none
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicAlignmentDecision.searchAlignmentFromListings?
/- AXIOM_AUDIT_END -/
