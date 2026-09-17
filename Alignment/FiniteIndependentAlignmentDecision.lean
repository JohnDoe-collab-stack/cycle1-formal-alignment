import Alignment.IndependentRelationalAlignment
import Alignment.FiniteIntrinsicAlignmentDecision

/-!
# Finite decision with independent local relation observations

This module makes the finite intrinsic decision independent of any common
relation-value carrier.

Candidate transports are still generated solely from complete finite listings
of the two identity carriers. A candidate passes when both round trips hold and
when it preserves the equality pattern of locally generated relation
observations. Source and target observation types may be unrelated.
-/

namespace Alignment
namespace GenesisReconstruction
namespace FiniteIndependentAlignmentDecision

open FiniteAnchoredMatchSearch
open FiniteIntrinsicFunctionEnumeration
open FiniteIntrinsicAlignmentDecision

universe uSource uTarget uSourceValue uTargetValue uAux

/-- Every ordered relation position generated from one finite carrier list. -/
def relationPositions
    {Carrier : Type uSource}
    (values : List Carrier) : List (Carrier × Carrier) :=
  values.flatMap fun first =>
    values.map fun second => (first, second)

/-- Complete carrier listings generate every ordered relation position. -/
theorem relationPosition_mem
    {Carrier : Type uSource}
    (listing : FiniteListing Carrier)
    (first second : Carrier) :
    (first, second) ∈ relationPositions listing.values := by
  unfold relationPositions
  apply
    mem_flatMap_of_mem_of_mem
      (fun current =>
        listing.values.map fun other => (current, other))
      (listing.complete first)
  exact
    mem_map_of_mem
      (fun other => (first, other))
      (listing.complete second)

/-- Generic finite universal Boolean check. -/
def allCheck
    {α : Type uAux}
    (check : α → Bool) : List α → Bool
  | [] => true
  | value :: rest =>
      match check value with
      | true => allCheck check rest
      | false => false

/-- Success of an all-check exposes success at every listed point. -/
theorem check_true_of_mem_of_allCheck_true
    {α : Type uAux}
    (check : α → Bool)
    (value : α)
    (values : List α)
    (member : value ∈ values)
    (checked : allCheck check values = true) :
    check value = true := by
  induction values with
  | nil =>
      cases member
  | cons head tail ih =>
      cases headCheck : check head with
      | false =>
          change
            (match check head with
            | true => allCheck check tail
            | false => false) = true at checked
          rw [headCheck] at checked
          cases checked
      | true =>
          have tailChecked : allCheck check tail = true := by
            change
              (match check head with
              | true => allCheck check tail
              | false => false) = true at checked
            rw [headCheck] at checked
            exact checked
          cases member with
          | head =>
              exact headCheck
          | tail _ tailMember =>
              exact ih tailMember tailChecked

/-- Pointwise Boolean success implies success of the finite universal check. -/
theorem allCheck_true_of_forall
    {α : Type uAux}
    (check : α → Bool)
    (values : List α)
    (pointwise : (value : α) → value ∈ values → check value = true) :
    allCheck check values = true := by
  induction values with
  | nil =>
      rfl
  | cons head tail ih =>
      have headTrue := pointwise head (List.Mem.head tail)
      have tailPointwise :
          (value : α) → value ∈ tail → check value = true := by
        intro value member
        exact pointwise value (List.Mem.tail head member)
      change
        (match check head with
        | true => allCheck check tail
        | false => false) = true
      rw [headTrue]
      exact ih tailPointwise

/--
Check one pair of relation positions. The result is true exactly when source
and target agree on whether the two local observations are equal.
-/
def relationPatternEntryCheck
    {Source : Type uSource}
    {Target : Type uTarget}
    {SourceValue : Type uSourceValue}
    {TargetValue : Type uTargetValue}
    [DecidableEq SourceValue]
    [DecidableEq TargetValue]
    (context :
      IndependentRelationalContext Source Target SourceValue TargetValue)
    (forward : Source → Target)
    (first second : Source × Source) : Bool :=
  if context.sourceRelation first.1 first.2 =
      context.sourceRelation second.1 second.2 then
    if context.targetRelation (forward first.1) (forward first.2) =
        context.targetRelation (forward second.1) (forward second.2) then
      true
    else
      false
  else
    if context.targetRelation (forward first.1) (forward first.2) =
        context.targetRelation (forward second.1) (forward second.2) then
      false
    else
      true

/-- A successful entry check yields the corresponding relational-pattern equivalence. -/
theorem relationalPattern_of_entryCheck_true
    {Source : Type uSource}
    {Target : Type uTarget}
    {SourceValue : Type uSourceValue}
    {TargetValue : Type uTargetValue}
    [DecidableEq SourceValue]
    [DecidableEq TargetValue]
    (context :
      IndependentRelationalContext Source Target SourceValue TargetValue)
    (forward : Source → Target)
    (first second : Source × Source)
    (checked : relationPatternEntryCheck context forward first second = true) :
    (context.sourceRelation first.1 first.2 =
        context.sourceRelation second.1 second.2) ↔
      (context.targetRelation (forward first.1) (forward first.2) =
        context.targetRelation (forward second.1) (forward second.2)) := by
  by_cases sourceEqual :
      context.sourceRelation first.1 first.2 =
        context.sourceRelation second.1 second.2
  · by_cases targetEqual :
        context.targetRelation (forward first.1) (forward first.2) =
          context.targetRelation (forward second.1) (forward second.2)
    · constructor
      · intro _
        exact targetEqual
      · intro _
        exact sourceEqual
    · unfold relationPatternEntryCheck at checked
      rw [if_pos sourceEqual, if_neg targetEqual] at checked
      cases checked
  · by_cases targetEqual :
        context.targetRelation (forward first.1) (forward first.2) =
          context.targetRelation (forward second.1) (forward second.2)
    · unfold relationPatternEntryCheck at checked
      rw [if_neg sourceEqual, if_pos targetEqual] at checked
      cases checked
    · constructor
      · intro impossible
        exact False.elim (sourceEqual impossible)
      · intro impossible
        exact False.elim (targetEqual impossible)

/-- A true relational-pattern equivalence makes the corresponding entry check pass. -/
theorem entryCheck_true_of_relationalPattern
    {Source : Type uSource}
    {Target : Type uTarget}
    {SourceValue : Type uSourceValue}
    {TargetValue : Type uTargetValue}
    [DecidableEq SourceValue]
    [DecidableEq TargetValue]
    (context :
      IndependentRelationalContext Source Target SourceValue TargetValue)
    (forward : Source → Target)
    (first second : Source × Source)
    (preserves :
      (context.sourceRelation first.1 first.2 =
          context.sourceRelation second.1 second.2) ↔
        (context.targetRelation (forward first.1) (forward first.2) =
          context.targetRelation (forward second.1) (forward second.2))) :
    relationPatternEntryCheck context forward first second = true := by
  by_cases sourceEqual :
      context.sourceRelation first.1 first.2 =
        context.sourceRelation second.1 second.2
  · have targetEqual := preserves.mp sourceEqual
    unfold relationPatternEntryCheck
    rw [if_pos sourceEqual, if_pos targetEqual]
  · have targetNotEqual :
        context.targetRelation (forward first.1) (forward first.2) ≠
          context.targetRelation (forward second.1) (forward second.2) := by
      intro targetEqual
      exact sourceEqual (preserves.mpr targetEqual)
    unfold relationPatternEntryCheck
    rw [if_neg sourceEqual, if_neg targetNotEqual]

/-- Finite Boolean check of the entire local relational equality pattern. -/
def preservesRelationalPatternOn
    {Source : Type uSource}
    {Target : Type uTarget}
    {SourceValue : Type uSourceValue}
    {TargetValue : Type uTargetValue}
    [DecidableEq SourceValue]
    [DecidableEq TargetValue]
    (context :
      IndependentRelationalContext Source Target SourceValue TargetValue)
    (sources : List Source)
    (forward : Source → Target) : Bool :=
  let positions := relationPositions sources
  allCheck
    (fun first =>
      allCheck
        (fun second =>
          relationPatternEntryCheck context forward first second)
        positions)
    positions

/-- Complete finite success upgrades to full pattern preservation. -/
theorem preservesRelationalPattern_of_true
    {Source : Type uSource}
    {Target : Type uTarget}
    {SourceValue : Type uSourceValue}
    {TargetValue : Type uTargetValue}
    [DecidableEq SourceValue]
    [DecidableEq TargetValue]
    (context :
      IndependentRelationalContext Source Target SourceValue TargetValue)
    (sources : FiniteListing Source)
    (forward : Source → Target)
    (checked :
      preservesRelationalPatternOn context sources.values forward = true) :
    PreservesRelationalPattern context forward := by
  intro first second third fourth
  let positions := relationPositions sources.values
  have firstMember :
      (first, second) ∈ positions :=
    relationPosition_mem sources first second
  have secondMember :
      (third, fourth) ∈ positions :=
    relationPosition_mem sources third fourth
  have firstChecked :
      allCheck
          (fun other =>
            relationPatternEntryCheck
              context forward (first, second) other)
          positions = true := by
    exact
      check_true_of_mem_of_allCheck_true
        (fun current =>
          allCheck
            (fun other =>
              relationPatternEntryCheck context forward current other)
            positions)
        (first, second)
        positions
        firstMember
        checked
  have entryChecked :
      relationPatternEntryCheck
          context forward (first, second) (third, fourth) = true :=
    check_true_of_mem_of_allCheck_true
      (fun other =>
        relationPatternEntryCheck context forward (first, second) other)
      (third, fourth)
      positions
      secondMember
      firstChecked
  exact
    relationalPattern_of_entryCheck_true
      context forward (first, second) (third, fourth) entryChecked

/-- Genuine full pattern preservation passes every finite pattern check. -/
theorem preservesRelationalPatternOn_true_of_preserves
    {Source : Type uSource}
    {Target : Type uTarget}
    {SourceValue : Type uSourceValue}
    {TargetValue : Type uTargetValue}
    [DecidableEq SourceValue]
    [DecidableEq TargetValue]
    (context :
      IndependentRelationalContext Source Target SourceValue TargetValue)
    (forward : Source → Target)
    (preserves : PreservesRelationalPattern context forward)
    (sources : List Source) :
    preservesRelationalPatternOn context sources forward = true := by
  unfold preservesRelationalPatternOn
  let positions := relationPositions sources
  apply
    allCheck_true_of_forall
      (fun first =>
        allCheck
          (fun second =>
            relationPatternEntryCheck context forward first second)
          positions)
      positions
  intro firstPosition firstMember
  apply
    allCheck_true_of_forall
      (fun secondPosition =>
        relationPatternEntryCheck
          context forward firstPosition secondPosition)
      positions
  intro secondPosition secondMember
  cases firstPosition with
  | mk first second =>
      cases secondPosition with
      | mk third fourth =>
          exact
            entryCheck_true_of_relationalPattern
              context forward
              (first, second) (third, fourth)
              (preserves first second third fourth)

/-- Raw candidate check with no shared observation type. -/
def candidatePasses
    {Source : Type uSource}
    {Target : Type uTarget}
    {SourceValue : Type uSourceValue}
    {TargetValue : Type uTargetValue}
    [DecidableEq Source]
    [DecidableEq Target]
    [DecidableEq SourceValue]
    [DecidableEq TargetValue]
    (context :
      IndependentRelationalContext Source Target SourceValue TargetValue)
    (sources : FiniteListing Source)
    (targets : FiniteListing Target)
    (candidate : FunctionPair Source Target) : Bool :=
  match sourceRoundTripCheck sources candidate with
  | false => false
  | true =>
      match targetRoundTripCheck targets candidate with
      | false => false
      | true =>
          preservesRelationalPatternOn
            context sources.values candidate.forward

/-- Passing raw functions reconstruct a certified independent exact alignment. -/
def alignmentOfPassingCandidate
    {Source : Type uSource}
    {Target : Type uTarget}
    {SourceValue : Type uSourceValue}
    {TargetValue : Type uTargetValue}
    [DecidableEq Source]
    [DecidableEq Target]
    [DecidableEq SourceValue]
    [DecidableEq TargetValue]
    (context :
      IndependentRelationalContext Source Target SourceValue TargetValue)
    (sources : FiniteListing Source)
    (targets : FiniteListing Target)
    (candidate : FunctionPair Source Target)
    (checked : candidatePasses context sources targets candidate = true) :
    IndependentCompatibleExactAlignment context := by
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
          have patternChecked :
              preservesRelationalPatternOn
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
              preservesPattern :=
                preservesRelationalPattern_of_true
                  context sources candidate.forward patternChecked }

/-- Extensionally agreeing raw functions inherit any independent exact alignment. -/
theorem candidatePasses_true_of_alignmentAgreement
    {Source : Type uSource}
    {Target : Type uTarget}
    {SourceValue : Type uSourceValue}
    {TargetValue : Type uTargetValue}
    [DecidableEq Source]
    [DecidableEq Target]
    [DecidableEq SourceValue]
    [DecidableEq TargetValue]
    (context :
      IndependentRelationalContext Source Target SourceValue TargetValue)
    (sources : FiniteListing Source)
    (targets : FiniteListing Target)
    (alignment : IndependentCompatibleExactAlignment context)
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
  have candidatePattern :
      PreservesRelationalPattern context candidate.forward := by
    intro first second third fourth
    have alignedPattern :=
      alignment.preservesPattern first second third fourth
    constructor
    · intro sourceEquality
      have targetEquality := alignedPattern.mp sourceEquality
      calc
        context.targetRelation
            (candidate.forward first)
            (candidate.forward second) =
          context.targetRelation
            (alignment.transport.forward first)
            (alignment.transport.forward second) := by
              rw [forwardAgreement first, forwardAgreement second]
        _ = context.targetRelation
            (alignment.transport.forward third)
            (alignment.transport.forward fourth) := targetEquality
        _ = context.targetRelation
            (candidate.forward third)
            (candidate.forward fourth) := by
              rw [forwardAgreement third, forwardAgreement fourth]
    · intro targetEquality
      apply alignedPattern.mpr
      calc
        context.targetRelation
            (alignment.transport.forward first)
            (alignment.transport.forward second) =
          context.targetRelation
            (candidate.forward first)
            (candidate.forward second) := by
              rw [forwardAgreement first, forwardAgreement second]
        _ = context.targetRelation
            (candidate.forward third)
            (candidate.forward fourth) := targetEquality
        _ = context.targetRelation
            (alignment.transport.forward third)
            (alignment.transport.forward fourth) := by
              rw [forwardAgreement third, forwardAgreement fourth]
  have patternChecked :
      preservesRelationalPatternOn
          context sources.values candidate.forward = true :=
    preservesRelationalPatternOn_true_of_preserves
      context candidate.forward candidatePattern sources.values
  unfold candidatePasses
  rw [sourceChecked, targetChecked]
  exact patternChecked

/-- Search generated raw candidates for a pattern-compatible exact transport. -/
def findPassingCandidate
    {Source : Type uSource}
    {Target : Type uTarget}
    {SourceValue : Type uSourceValue}
    {TargetValue : Type uTargetValue}
    [DecidableEq Source]
    [DecidableEq Target]
    [DecidableEq SourceValue]
    [DecidableEq TargetValue]
    (context :
      IndependentRelationalContext Source Target SourceValue TargetValue)
    (sources : FiniteListing Source)
    (targets : FiniteListing Target) :
    List (FunctionPair Source Target) → Option (FunctionPair Source Target)
  | [] => none
  | candidate :: rest =>
      match candidatePasses context sources targets candidate with
      | true => some candidate
      | false => findPassingCandidate context sources targets rest

theorem findPassingCandidate_ne_none_of_mem_of_true
    {Source : Type uSource}
    {Target : Type uTarget}
    {SourceValue : Type uSourceValue}
    {TargetValue : Type uTargetValue}
    [DecidableEq Source]
    [DecidableEq Target]
    [DecidableEq SourceValue]
    [DecidableEq TargetValue]
    (context :
      IndependentRelationalContext Source Target SourceValue TargetValue)
    (sources : FiniteListing Source)
    (targets : FiniteListing Target)
    (candidates : List (FunctionPair Source Target))
    (candidate : FunctionPair Source Target)
    (member : candidate ∈ candidates)
    (checked : candidatePasses context sources targets candidate = true) :
    findPassingCandidate context sources targets candidates ≠ none := by
  induction candidates with
  | nil =>
      cases member
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
          cases currentCheck :
              candidatePasses context sources targets current with
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

theorem findPassingCandidate_sound
    {Source : Type uSource}
    {Target : Type uTarget}
    {SourceValue : Type uSourceValue}
    {TargetValue : Type uTargetValue}
    [DecidableEq Source]
    [DecidableEq Target]
    [DecidableEq SourceValue]
    [DecidableEq TargetValue]
    (context :
      IndependentRelationalContext Source Target SourceValue TargetValue)
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
      cases currentCheck :
          candidatePasses context sources targets current with
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

/-- Any independent exact alignment forces generated exhaustive search to succeed. -/
theorem generatedFinder_ne_none_of_alignment
    {Source : Type uSource}
    {Target : Type uTarget}
    {SourceValue : Type uSourceValue}
    {TargetValue : Type uTargetValue}
    [DecidableEq Source]
    [DecidableEq Target]
    [DecidableEq SourceValue]
    [DecidableEq TargetValue]
    (context :
      IndependentRelationalContext Source Target SourceValue TargetValue)
    (sources : FiniteListing Source)
    (targets : FiniteListing Target)
    (alignment : IndependentCompatibleExactAlignment context) :
    findPassingCandidate
        context sources targets (generatedPairs sources targets) ≠ none := by
  let witness :=
    generatedPairOfExactTransport sources targets alignment.transport
  have checked :
      candidatePasses context sources targets witness.1 = true :=
    candidatePasses_true_of_alignmentAgreement
      context sources targets alignment witness.1
      witness.2.2.1 witness.2.2.2
  exact
    findPassingCandidate_ne_none_of_mem_of_true
      context sources targets
      (generatedPairs sources targets)
      witness.1 witness.2.1 checked

/-- Computed exhaustion constructively refutes every independent exact alignment. -/
theorem noAlignment_of_generatedFinder_none
    {Source : Type uSource}
    {Target : Type uTarget}
    {SourceValue : Type uSourceValue}
    {TargetValue : Type uTargetValue}
    [DecidableEq Source]
    [DecidableEq Target]
    [DecidableEq SourceValue]
    [DecidableEq TargetValue]
    (context :
      IndependentRelationalContext Source Target SourceValue TargetValue)
    (sources : FiniteListing Source)
    (targets : FiniteListing Target)
    (noneFound :
      findPassingCandidate
          context sources targets (generatedPairs sources targets) = none)
    (alignment : IndependentCompatibleExactAlignment context) : False :=
  (generatedFinder_ne_none_of_alignment
    context sources targets alignment) noneFound

/-- Certified semantic decision for the closed independent constitutive alignment. -/
inductive AlignmentDecision
    {Source : Type uSource}
    {Target : Type uTarget}
    {SourceValue : Type uSourceValue}
    {TargetValue : Type uTargetValue}
    (context :
      IndependentRelationalContext Source Target SourceValue TargetValue) : Type _ where
  | aligned :
      IndependentConstitutiveAlignment context →
      AlignmentDecision context
  | impossible :
      (IndependentConstitutiveAlignment context → False) →
      AlignmentDecision context

namespace AlignmentDecision

def isAligned
    {Source : Type uSource}
    {Target : Type uTarget}
    {SourceValue : Type uSourceValue}
    {TargetValue : Type uTargetValue}
    {context :
      IndependentRelationalContext Source Target SourceValue TargetValue} :
    AlignmentDecision context → Bool
  | .aligned _ => true
  | .impossible _ => false

end AlignmentDecision

/--
End-to-end finite decision from local identity listings and locally typed
relations only.
-/
def decideAlignmentFromListings
    {Source : Type uSource}
    {Target : Type uTarget}
    {SourceValue : Type uSourceValue}
    {TargetValue : Type uTargetValue}
    [DecidableEq Source]
    [DecidableEq Target]
    [DecidableEq SourceValue]
    [DecidableEq TargetValue]
    (context :
      IndependentRelationalContext Source Target SourceValue TargetValue)
    (sources : FiniteListing Source)
    (targets : FiniteListing Target) :
    AlignmentDecision context :=
  match found :
      findPassingCandidate
        context sources targets (generatedPairs sources targets) with
  | none =>
      .impossible
        (fun alignment =>
          noAlignment_of_generatedFinder_none
            context sources targets found alignment.initial)
  | some candidate =>
      .aligned
        ⟨alignmentOfPassingCandidate
          context sources targets candidate
          (findPassingCandidate_sound
            context sources targets
            (generatedPairs sources targets)
            candidate found)⟩

theorem decideAlignmentFromListings_isAligned_of_alignment
    {Source : Type uSource}
    {Target : Type uTarget}
    {SourceValue : Type uSourceValue}
    {TargetValue : Type uTargetValue}
    [DecidableEq Source]
    [DecidableEq Target]
    [DecidableEq SourceValue]
    [DecidableEq TargetValue]
    (context :
      IndependentRelationalContext Source Target SourceValue TargetValue)
    (sources : FiniteListing Source)
    (targets : FiniteListing Target)
    (alignment : IndependentConstitutiveAlignment context) :
    (decideAlignmentFromListings context sources targets).isAligned = true := by
  cases decision :
      decideAlignmentFromListings context sources targets with
  | aligned found =>
      rfl
  | impossible refute =>
      exact (refute alignment).elim

theorem decideAlignmentFromListings_isAligned_false_of_refutation
    {Source : Type uSource}
    {Target : Type uTarget}
    {SourceValue : Type uSourceValue}
    {TargetValue : Type uTargetValue}
    [DecidableEq Source]
    [DecidableEq Target]
    [DecidableEq SourceValue]
    [DecidableEq TargetValue]
    (context :
      IndependentRelationalContext Source Target SourceValue TargetValue)
    (sources : FiniteListing Source)
    (targets : FiniteListing Target)
    (refute : IndependentConstitutiveAlignment context → False) :
    (decideAlignmentFromListings context sources targets).isAligned = false := by
  cases decision :
      decideAlignmentFromListings context sources targets with
  | aligned alignment =>
      exact (refute alignment).elim
  | impossible noAlignment =>
      rfl

end FiniteIndependentAlignmentDecision
end GenesisReconstruction
end Alignment

/- AXIOM_AUDIT_BEGIN -/
#print axioms Alignment.GenesisReconstruction.FiniteIndependentAlignmentDecision.relationPositions
#print axioms Alignment.GenesisReconstruction.FiniteIndependentAlignmentDecision.relationPosition_mem
#print axioms Alignment.GenesisReconstruction.FiniteIndependentAlignmentDecision.allCheck
#print axioms Alignment.GenesisReconstruction.FiniteIndependentAlignmentDecision.check_true_of_mem_of_allCheck_true
#print axioms Alignment.GenesisReconstruction.FiniteIndependentAlignmentDecision.allCheck_true_of_forall
#print axioms Alignment.GenesisReconstruction.FiniteIndependentAlignmentDecision.relationPatternEntryCheck
#print axioms Alignment.GenesisReconstruction.FiniteIndependentAlignmentDecision.relationalPattern_of_entryCheck_true
#print axioms Alignment.GenesisReconstruction.FiniteIndependentAlignmentDecision.entryCheck_true_of_relationalPattern
#print axioms Alignment.GenesisReconstruction.FiniteIndependentAlignmentDecision.preservesRelationalPatternOn
#print axioms Alignment.GenesisReconstruction.FiniteIndependentAlignmentDecision.preservesRelationalPattern_of_true
#print axioms Alignment.GenesisReconstruction.FiniteIndependentAlignmentDecision.preservesRelationalPatternOn_true_of_preserves
#print axioms Alignment.GenesisReconstruction.FiniteIndependentAlignmentDecision.candidatePasses
#print axioms Alignment.GenesisReconstruction.FiniteIndependentAlignmentDecision.alignmentOfPassingCandidate
#print axioms Alignment.GenesisReconstruction.FiniteIndependentAlignmentDecision.candidatePasses_true_of_alignmentAgreement
#print axioms Alignment.GenesisReconstruction.FiniteIndependentAlignmentDecision.findPassingCandidate
#print axioms Alignment.GenesisReconstruction.FiniteIndependentAlignmentDecision.findPassingCandidate_ne_none_of_mem_of_true
#print axioms Alignment.GenesisReconstruction.FiniteIndependentAlignmentDecision.findPassingCandidate_sound
#print axioms Alignment.GenesisReconstruction.FiniteIndependentAlignmentDecision.generatedFinder_ne_none_of_alignment
#print axioms Alignment.GenesisReconstruction.FiniteIndependentAlignmentDecision.noAlignment_of_generatedFinder_none
#print axioms Alignment.GenesisReconstruction.FiniteIndependentAlignmentDecision.AlignmentDecision
#print axioms Alignment.GenesisReconstruction.FiniteIndependentAlignmentDecision.AlignmentDecision.isAligned
#print axioms Alignment.GenesisReconstruction.FiniteIndependentAlignmentDecision.decideAlignmentFromListings
#print axioms Alignment.GenesisReconstruction.FiniteIndependentAlignmentDecision.decideAlignmentFromListings_isAligned_of_alignment
#print axioms Alignment.GenesisReconstruction.FiniteIndependentAlignmentDecision.decideAlignmentFromListings_isAligned_false_of_refutation
/- AXIOM_AUDIT_END -/
