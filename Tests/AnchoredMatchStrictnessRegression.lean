import Alignment.AnchoredMatchStrictness

namespace Alignment.Tests.AnchoredMatchStrictnessRegression

open GenesisReconstruction

inductive TargetPoint
  | matched
  | extra

/-- The one-point source has one constant anchored observation. -/
def sourceRelation (_source _target : Unit) : Bool :=
  false

/-- The target relation distinguishes the matched point from the extra point. -/
def targetRelation (source target : TargetPoint) : Bool :=
  match source with
  | .matched =>
      match target with
      | .matched => false
      | .extra => true
  | .extra =>
      match target with
      | .matched => false
      | .extra => true

def sourceAnchor : Unit → Unit :=
  fun _ => ()

def targetAnchor : Unit → TargetPoint :=
  fun _ => .matched

theorem sourceProfile_separates :
    ProfileSeparates
      (fun identity anchor => sourceRelation (sourceAnchor anchor) identity) := by
  intro first second _
  cases first
  cases second
  rfl

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

def strictContext :
    AnchoredRelationContext Unit TargetPoint Unit Bool :=
  { sourceRelation := sourceRelation
    targetRelation := targetRelation
    sourceAnchor := sourceAnchor
    targetAnchor := targetAnchor
    sourceSeparates := sourceProfile_separates
    targetSeparates := targetProfile_separates }

/-- Every source identity has a structural target match. -/
def forwardWitness :
    (source : Unit) →
      { target : TargetPoint // strictContext.Matches source target }
  | () => ⟨.matched, by intro anchor; cases anchor; rfl⟩

def forwardOnly : ForwardAnchoredMatching strictContext :=
  { forwardWitness := forwardWitness }

/-- One-sided structural totality already yields an injective forward map. -/
theorem forwardOnly_injective :
    Function.Injective forwardOnly.forward :=
  ForwardAnchoredMatching.forward_injective forwardOnly

/-- The extra target has no structural source match. -/
theorem extra_has_no_source_match :
    ¬ ∃ source : Unit, strictContext.Matches source TargetPoint.extra := by
  intro witness
  rcases witness with ⟨source, matchProof⟩
  cases source
  have impossible := matchProof ()
  change true = false at impossible
  cases impossible

/-- Forward totality does not imply reverse totality. -/
theorem no_backwardMatching :
    ¬ BackwardAnchoredMatching strictContext := by
  intro backwardMatching
  have matchProof :=
    BackwardAnchoredMatching.backward_matches
      backwardMatching TargetPoint.extra
  have impossible := matchProof ()
  change true = false at impossible
  cases impossible

/-- Hence one-sided totality is strictly weaker than bidirectional totality. -/
theorem no_totalMatching :
    ¬ TotalAnchoredMatching strictContext := by
  intro totalMatching
  exact
    no_backwardMatching
      (TotalAnchoredMatching.toBackwardMatching totalMatching)

/-- Therefore no exact alignment compatible with this structural context exists. -/
theorem no_compatibleExactAlignment :
    ¬ CompatibleExactAlignment strictContext := by
  intro alignment
  exact
    no_totalMatching
      (CompatibleExactAlignment.toTotalMatching alignment)

end Alignment.Tests.AnchoredMatchStrictnessRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms Alignment.Tests.AnchoredMatchStrictnessRegression.sourceRelation
#print axioms Alignment.Tests.AnchoredMatchStrictnessRegression.targetRelation
#print axioms Alignment.Tests.AnchoredMatchStrictnessRegression.strictContext
#print axioms Alignment.Tests.AnchoredMatchStrictnessRegression.forwardOnly
#print axioms Alignment.Tests.AnchoredMatchStrictnessRegression.forwardOnly_injective
#print axioms Alignment.Tests.AnchoredMatchStrictnessRegression.extra_has_no_source_match
#print axioms Alignment.Tests.AnchoredMatchStrictnessRegression.no_backwardMatching
#print axioms Alignment.Tests.AnchoredMatchStrictnessRegression.no_totalMatching
#print axioms Alignment.Tests.AnchoredMatchStrictnessRegression.no_compatibleExactAlignment
/- AXIOM_AUDIT_END -/
