import Alignment.FiniteAlignmentClassification

namespace Alignment.Tests.FiniteAnchoredMatchSearchRegression

open GenesisReconstruction
open GenesisReconstruction.FiniteAnchoredMatchSearch
open GenesisReconstruction.FiniteAnchoredMatchDecision
open GenesisReconstruction.FiniteAlignmentClassification

inductive SourceNode
  | root
  | next

inductive TargetNode
  | origin
  | successor

/-- A one-edge source relation whose anchored profile distinguishes both nodes. -/
def sourceRelation (source target : SourceNode) : Bool :=
  match source with
  | .root =>
      match target with
      | .root => false
      | .next => true
  | .next => false

/-- The same relation on a distinct target carrier. -/
def targetRelation (source target : TargetNode) : Bool :=
  match source with
  | .origin =>
      match target with
      | .origin => false
      | .successor => true
  | .successor => false

def sourceAnchor : Unit → SourceNode :=
  fun _ => .root

def targetAnchor : Unit → TargetNode :=
  fun _ => .origin

theorem sourceProfile_separates :
    ProfileSeparates
      (fun identity anchor => sourceRelation (sourceAnchor anchor) identity) := by
  intro first second agreement
  cases first <;> cases second
  · rfl
  · have impossible := agreement ()
    cases impossible
  · have impossible := agreement ()
    cases impossible
  · rfl

theorem targetProfile_separates :
    ProfileSeparates
      (fun identity anchor => targetRelation (targetAnchor anchor) identity) := by
  intro first second agreement
  cases first <;> cases second
  · rfl
  · have impossible := agreement ()
    cases impossible
  · have impossible := agreement ()
    cases impossible
  · rfl

def context :
    AnchoredRelationContext SourceNode TargetNode Unit Bool :=
  { sourceRelation := sourceRelation
    targetRelation := targetRelation
    sourceAnchor := sourceAnchor
    targetAnchor := targetAnchor
    sourceSeparates := sourceProfile_separates
    targetSeparates := targetProfile_separates }

def anchorListing : FiniteListing Unit :=
  { values := [()]
    complete := by
      intro value
      cases value
      exact List.Mem.head [] }

def sourceListing : FiniteListing SourceNode :=
  { values := [SourceNode.root, SourceNode.next]
    complete := by
      intro value
      cases value with
      | root =>
          exact List.Mem.head [SourceNode.next]
      | next =>
          exact List.Mem.tail SourceNode.root (List.Mem.head []) }

def targetListing : FiniteListing TargetNode :=
  { values := [TargetNode.origin, TargetNode.successor]
    complete := by
      intro value
      cases value with
      | origin =>
          exact List.Mem.head [TargetNode.successor]
      | successor =>
          exact List.Mem.tail TargetNode.origin (List.Mem.head []) }

/-- The finite search discovers the first structural pair directly. -/
theorem find_root :
    findTarget context anchorListing.values SourceNode.root targetListing.values =
      some TargetNode.origin := by
  rfl

/-- The search skips the wrong profile and discovers the second pair. -/
theorem find_next :
    findTarget context anchorListing.values SourceNode.next targetListing.values =
      some TargetNode.successor := by
  rfl

/-- Every source is found by computation. -/
theorem forward_check_succeeds :
    forwardTotalCheck context anchorListing sourceListing targetListing = true := by
  rfl

/-- Every target is found by the reverse computation. -/
theorem backward_check_succeeds :
    backwardTotalCheck context anchorListing sourceListing targetListing = true := by
  rfl

/-- Total structural matching is built from the two Boolean checks, not supplied as a resolver. -/
def computedMatching : TotalAnchoredMatching context :=
  totalMatchingOfChecks
    context anchorListing sourceListing targetListing
    forward_check_succeeds backward_check_succeeds

/-- The computed matching maps the second source identity to its structural counterpart. -/
theorem computed_forward_next :
    computedMatching.forward SourceNode.next = TargetNode.successor := by
  rfl

/-- The reverse map is computed from the same finite relational data. -/
theorem computed_backward_successor :
    computedMatching.backward TargetNode.successor = SourceNode.next := by
  rfl

/-- The computed search therefore reconstructs an exact initial transport. -/
theorem computed_source_roundTrip :
    computedMatching.toExactTransport.backward
        (computedMatching.toExactTransport.forward SourceNode.next) =
      SourceNode.next :=
  computedMatching.toExactTransport.forwardBackward SourceNode.next

/-- The reconstructed alignment propagates through arbitrary natural-number genesis depth. -/
theorem computed_depth_three_preservesGenesis :
    PreservesGenesis (computedMatching.finiteTransport 3) :=
  computedMatching.finiteTransport_preservesGenesis 3

/-- The two successful checks characterize inhabited total structural matching. -/
theorem total_checks_characterize_matching :
    Nonempty (TotalAnchoredMatching context) :=
  (totalChecks_true_iff_nonempty
    context anchorListing sourceListing targetListing).mp
      ⟨forward_check_succeeds, backward_check_succeeds⟩

/-- The witness-carrying classifier computes the exact regime on the total context. -/
def computedClassification : Classification context :=
  classify context anchorListing sourceListing targetListing

/-- The exact regime tag is obtained by computation. -/
theorem computed_classification_kind :
    computedClassification.kind = Kind.exact := by
  rfl

/-- Exact classification exposes the transport at the requested natural-number genesis depth directly. -/
theorem computed_classification_depth_three_transport :
    computedClassification.finiteTransport? 3 ≠ none := by
  intro impossible
  change some _ = none at impossible
  cases impossible

/-- The optional end-to-end search succeeds on the total finite context. -/
theorem optional_search_succeeds :
    searchTotalMatching? context anchorListing sourceListing targetListing ≠ none := by
  intro impossible
  change some _ = none at impossible
  cases impossible

inductive PartialTarget
  | matched
  | extra

def partialSourceRelation (_source _target : Unit) : Bool :=
  false

def partialTargetRelation (source target : PartialTarget) : Bool :=
  match source with
  | .matched =>
      match target with
      | .matched => false
      | .extra => true
  | .extra =>
      match target with
      | .matched => false
      | .extra => true

def partialSourceAnchor : Unit → Unit :=
  fun _ => ()

def partialTargetAnchor : Unit → PartialTarget :=
  fun _ => .matched

theorem partialSourceProfile_separates :
    ProfileSeparates
      (fun identity anchor =>
        partialSourceRelation (partialSourceAnchor anchor) identity) := by
  intro first second _
  cases first
  cases second
  rfl

theorem partialTargetProfile_separates :
    ProfileSeparates
      (fun identity anchor =>
        partialTargetRelation (partialTargetAnchor anchor) identity) := by
  intro first second agreement
  cases first <;> cases second
  · rfl
  · have impossible := agreement ()
    cases impossible
  · have impossible := agreement ()
    cases impossible
  · rfl

def partialContext :
    AnchoredRelationContext Unit PartialTarget Unit Bool :=
  { sourceRelation := partialSourceRelation
    targetRelation := partialTargetRelation
    sourceAnchor := partialSourceAnchor
    targetAnchor := partialTargetAnchor
    sourceSeparates := partialSourceProfile_separates
    targetSeparates := partialTargetProfile_separates }

def unitListing : FiniteListing Unit :=
  { values := [()]
    complete := by
      intro value
      cases value
      exact List.Mem.head [] }

def partialTargetListing : FiniteListing PartialTarget :=
  { values := [PartialTarget.matched, PartialTarget.extra]
    complete := by
      intro value
      cases value with
      | matched =>
          exact List.Mem.head [PartialTarget.extra]
      | extra =>
          exact List.Mem.tail PartialTarget.matched (List.Mem.head []) }

/-- One-sided totality is detected positively by the executable checker. -/
theorem partial_forward_check_succeeds :
    forwardTotalCheck
      partialContext unitListing unitListing partialTargetListing = true := by
  rfl

/-- The successful forward check constructs an actual one-sided structural matching. -/
def partialForwardMatching : ForwardAnchoredMatching partialContext :=
  forwardMatchingOfCheck
    partialContext unitListing unitListing partialTargetListing
    partial_forward_check_succeeds

/-- The computed one-sided structural matching is injective. -/
theorem partial_forward_injective :
    Function.Injective partialForwardMatching.forward :=
  partialForwardMatching.forward_injective

/-- The executable forward search returns the positive structural matching. -/
theorem partial_forward_search_succeeds :
    searchForwardMatching?
      partialContext unitListing unitListing partialTargetListing ≠ none := by
  intro impossible
  change some _ = none at impossible
  cases impossible

/-- Reverse totality fails because the extra target has no source profile match. -/
theorem partial_backward_check_fails :
    backwardTotalCheck
      partialContext unitListing unitListing partialTargetListing = false := by
  rfl

/-- The failed reverse check certifies that no reverse structural matching can exist. -/
theorem partial_no_backward_matching
    (matching : BackwardAnchoredMatching partialContext) : False :=
  noBackwardMatching_of_backwardTotalCheck_false
    partialContext unitListing unitListing partialTargetListing
    partial_backward_check_fails matching

/-- The failed reverse check also certifies that exact compatible alignment is impossible. -/
theorem partial_no_compatible_exact_alignment
    (alignment : CompatibleExactAlignment partialContext) : False :=
  noCompatibleExactAlignment_of_backwardTotalCheck_false
    partialContext unitListing unitListing partialTargetListing
    partial_backward_check_fails alignment

/-- The positive and negative directional checks package into a forward-only certificate. -/
def partialForwardOnlyCertificate : ForwardOnlyCertificate partialContext :=
  forwardOnlyCertificateOfChecks
    partialContext unitListing unitListing partialTargetListing
    partial_forward_check_succeeds partial_backward_check_fails

/-- The certificate retains the positive injective forward matching. -/
theorem partial_certificate_forward_injective :
    Function.Injective partialForwardOnlyCertificate.matching.forward :=
  partialForwardOnlyCertificate.matching.forward_injective

/-- The certificate carries the exact-alignment refutation as part of the same value. -/
theorem partial_certificate_refutes_exact
    (alignment : CompatibleExactAlignment partialContext) : False :=
  partialForwardOnlyCertificate.refutesExact alignment

/-- The classifier computes the forward-only regime on the asymmetric context. -/
def partialClassification : Classification partialContext :=
  classify partialContext unitListing unitListing partialTargetListing

/-- The forward-only tag is obtained by computation from the two directional checks. -/
theorem partial_classification_kind :
    partialClassification.kind = Kind.forwardOnly := by
  rfl

/-- The forward-only classification retains the positive structural injection. -/
theorem partial_classification_forward_matching :
    partialClassification.forwardMatching? ≠ none := by
  intro impossible
  change some _ = none at impossible
  cases impossible

/-- The forward-only classification exposes no exact transport. -/
theorem partial_classification_no_exact_transport :
    partialClassification.exactTransport? = none := by
  rfl

/-- The computed forward-only regime is definitionally non-exact. -/
theorem partial_classification_nonexact :
    partialClassification.kind ≠ Kind.exact := by
  intro impossible
  cases impossible

/-- The classification itself carries enough negative information to refute exact alignment. -/
theorem partial_classification_refutes_exact
    (alignment : CompatibleExactAlignment partialContext) : False :=
  partialClassification.refutesExact_of_nonexact
    partial_classification_nonexact alignment

/-- The executable reverse search rejects the missing reverse totality. -/
theorem partial_backward_search_rejects :
    searchBackwardMatching?
      partialContext unitListing unitListing partialTargetListing = none := by
  rfl

/-- The end-to-end procedure refuses to manufacture an exact alignment when totality fails. -/
theorem partial_optional_search_rejects :
    searchTotalMatching?
      partialContext unitListing unitListing partialTargetListing = none := by
  rfl

end Alignment.Tests.FiniteAnchoredMatchSearchRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms Alignment.Tests.FiniteAnchoredMatchSearchRegression.context
#print axioms Alignment.Tests.FiniteAnchoredMatchSearchRegression.anchorListing
#print axioms Alignment.Tests.FiniteAnchoredMatchSearchRegression.sourceListing
#print axioms Alignment.Tests.FiniteAnchoredMatchSearchRegression.targetListing
#print axioms Alignment.Tests.FiniteAnchoredMatchSearchRegression.find_root
#print axioms Alignment.Tests.FiniteAnchoredMatchSearchRegression.find_next
#print axioms Alignment.Tests.FiniteAnchoredMatchSearchRegression.forward_check_succeeds
#print axioms Alignment.Tests.FiniteAnchoredMatchSearchRegression.backward_check_succeeds
#print axioms Alignment.Tests.FiniteAnchoredMatchSearchRegression.computedMatching
#print axioms Alignment.Tests.FiniteAnchoredMatchSearchRegression.computed_forward_next
#print axioms Alignment.Tests.FiniteAnchoredMatchSearchRegression.computed_backward_successor
#print axioms Alignment.Tests.FiniteAnchoredMatchSearchRegression.computed_source_roundTrip
#print axioms Alignment.Tests.FiniteAnchoredMatchSearchRegression.computed_depth_three_preservesGenesis
#print axioms Alignment.Tests.FiniteAnchoredMatchSearchRegression.total_checks_characterize_matching
#print axioms Alignment.Tests.FiniteAnchoredMatchSearchRegression.computedClassification
#print axioms Alignment.Tests.FiniteAnchoredMatchSearchRegression.computed_classification_kind
#print axioms Alignment.Tests.FiniteAnchoredMatchSearchRegression.computed_classification_depth_three_transport
#print axioms Alignment.Tests.FiniteAnchoredMatchSearchRegression.optional_search_succeeds
#print axioms Alignment.Tests.FiniteAnchoredMatchSearchRegression.partialContext
#print axioms Alignment.Tests.FiniteAnchoredMatchSearchRegression.partial_forward_check_succeeds
#print axioms Alignment.Tests.FiniteAnchoredMatchSearchRegression.partialForwardMatching
#print axioms Alignment.Tests.FiniteAnchoredMatchSearchRegression.partial_forward_injective
#print axioms Alignment.Tests.FiniteAnchoredMatchSearchRegression.partial_forward_search_succeeds
#print axioms Alignment.Tests.FiniteAnchoredMatchSearchRegression.partial_backward_check_fails
#print axioms Alignment.Tests.FiniteAnchoredMatchSearchRegression.partial_no_backward_matching
#print axioms Alignment.Tests.FiniteAnchoredMatchSearchRegression.partial_no_compatible_exact_alignment
#print axioms Alignment.Tests.FiniteAnchoredMatchSearchRegression.partialForwardOnlyCertificate
#print axioms Alignment.Tests.FiniteAnchoredMatchSearchRegression.partial_certificate_forward_injective
#print axioms Alignment.Tests.FiniteAnchoredMatchSearchRegression.partial_certificate_refutes_exact
#print axioms Alignment.Tests.FiniteAnchoredMatchSearchRegression.partialClassification
#print axioms Alignment.Tests.FiniteAnchoredMatchSearchRegression.partial_classification_kind
#print axioms Alignment.Tests.FiniteAnchoredMatchSearchRegression.partial_classification_forward_matching
#print axioms Alignment.Tests.FiniteAnchoredMatchSearchRegression.partial_classification_no_exact_transport
#print axioms Alignment.Tests.FiniteAnchoredMatchSearchRegression.partial_classification_nonexact
#print axioms Alignment.Tests.FiniteAnchoredMatchSearchRegression.partial_classification_refutes_exact
#print axioms Alignment.Tests.FiniteAnchoredMatchSearchRegression.partial_backward_search_rejects
#print axioms Alignment.Tests.FiniteAnchoredMatchSearchRegression.partial_optional_search_rejects
/- AXIOM_AUDIT_END -/
