import Alignment.AnchoredMatchStrictness

namespace Alignment.Tests.AnchoredMatchStrictnessRegression

open GenesisReconstruction

/-- The one-point source profile is necessarily rigid. -/
def sourceRelation (_source _target : Unit) : Bool :=
  false

/-- The target anchored profile exposes the Boolean target identity itself. -/
def targetRelation (_source target : Bool) : Bool :=
  target

def sourceAnchor : Unit → Unit :=
  fun _ => ()

def targetAnchor : Unit → Bool :=
  fun _ => false

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
  exact agreement ()

def strictContext :
    AnchoredRelationContext Unit Bool Unit Bool :=
  { sourceRelation := sourceRelation
    targetRelation := targetRelation
    sourceAnchor := sourceAnchor
    targetAnchor := targetAnchor
    sourceSeparates := sourceProfile_separates
    targetSeparates := targetProfile_separates }

/-- Every source identity has a structural target match. -/
def forwardWitness :
    (source : Unit) →
      { target : Bool // strictContext.Matches source target }
  | () => ⟨false, by intro anchor; cases anchor; rfl⟩

def forwardOnly : ForwardAnchoredMatching strictContext :=
  { forwardWitness := forwardWitness }

/-- One-sided structural totality already yields an injective forward map. -/
theorem forwardOnly_injective :
    Function.Injective forwardOnly.forward :=
  forwardOnly.forward_injective

/-- The unmatched target `true` blocks totality in the reverse direction. -/
theorem true_has_no_source_match :
    ¬ ∃ source : Unit, strictContext.Matches source true := by
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
  have matchProof := backwardMatching.backward_matches true
  have impossible := matchProof ()
  change true = false at impossible
  cases impossible

/-- Hence one-sided totality is strictly weaker than bidirectional totality. -/
theorem no_totalMatching :
    ¬ TotalAnchoredMatching strictContext := by
  intro totalMatching
  exact no_backwardMatching totalMatching.toBackwardMatching

/-- Therefore no exact alignment compatible with this structural context exists. -/
theorem no_compatibleExactAlignment :
    ¬ CompatibleExactAlignment strictContext := by
  intro alignment
  exact no_totalMatching alignment.toTotalMatching

end Alignment.Tests.AnchoredMatchStrictnessRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms Alignment.Tests.AnchoredMatchStrictnessRegression.strictContext
#print axioms Alignment.Tests.AnchoredMatchStrictnessRegression.forwardOnly
#print axioms Alignment.Tests.AnchoredMatchStrictnessRegression.forwardOnly_injective
#print axioms Alignment.Tests.AnchoredMatchStrictnessRegression.true_has_no_source_match
#print axioms Alignment.Tests.AnchoredMatchStrictnessRegression.no_backwardMatching
#print axioms Alignment.Tests.AnchoredMatchStrictnessRegression.no_totalMatching
#print axioms Alignment.Tests.AnchoredMatchStrictnessRegression.no_compatibleExactAlignment
/- AXIOM_AUDIT_END -/
