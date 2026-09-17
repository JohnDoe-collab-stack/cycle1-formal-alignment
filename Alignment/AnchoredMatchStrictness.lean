import Alignment.AnchoredMatchReconstruction

/-!
# Strictness and characterization of anchored structural alignment

The total anchored matching interface reconstructs an exact alignment, but its
bidirectional totality can be weakened in two independent directions.

A forward total matching supplies one structural target for every source. Under
profile separation this already yields an injective forward map. Dually, a
backward total matching yields an injective backward map. Neither one-sided
condition supplies both round-trips.

Bidirectional totality is exactly the positive data needed to construct an exact
transport compatible with the anchored match relation. Conversely, any exact
transport whose forward map respects the structural match relation supplies
both totality witnesses constructively. The correspondence is stated through
explicit conversions rather than equality of structures, so no extensionality
principle is required.
-/

namespace Alignment
namespace GenesisReconstruction

universe uSource uTarget uAnchor uValue

/-- Positive structural totality only from source to target. -/
structure ForwardAnchoredMatching
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    (context : AnchoredRelationContext Source Target Anchor Value) where
  forwardWitness :
    (source : Source) → { target : Target // context.Matches source target }

namespace ForwardAnchoredMatching

/-- Forward map projected from one-sided structural witnesses. -/
def forward
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    {context : AnchoredRelationContext Source Target Anchor Value}
    (matching : ForwardAnchoredMatching context) :
    Source → Target :=
  fun source => (matching.forwardWitness source).1

/-- Every projected target satisfies the anchored match relation. -/
theorem forward_matches
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    {context : AnchoredRelationContext Source Target Anchor Value}
    (matching : ForwardAnchoredMatching context)
    (source : Source) :
    context.Matches source (matching.forward source) :=
  (matching.forwardWitness source).2

/-- Separation turns one-sided total matching into an injective forward map. -/
theorem forward_injective
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    {context : AnchoredRelationContext Source Target Anchor Value}
    (matching : ForwardAnchoredMatching context) :
    Function.Injective matching.forward := by
  intro first second equality
  have secondMatches :
      context.Matches second (matching.forward first) := by
    rw [equality]
    exact matching.forward_matches second
  exact
    context.source_unique
      (matching.forward first)
      first
      second
      (matching.forward_matches first)
      secondMatches

end ForwardAnchoredMatching

/-- Positive structural totality only from target to source. -/
structure BackwardAnchoredMatching
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    (context : AnchoredRelationContext Source Target Anchor Value) where
  backwardWitness :
    (target : Target) → { source : Source // context.Matches source target }

namespace BackwardAnchoredMatching

/-- Backward map projected from one-sided structural witnesses. -/
def backward
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    {context : AnchoredRelationContext Source Target Anchor Value}
    (matching : BackwardAnchoredMatching context) :
    Target → Source :=
  fun target => (matching.backwardWitness target).1

/-- Every projected source satisfies the anchored match relation. -/
theorem backward_matches
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    {context : AnchoredRelationContext Source Target Anchor Value}
    (matching : BackwardAnchoredMatching context)
    (target : Target) :
    context.Matches (matching.backward target) target :=
  (matching.backwardWitness target).2

/-- Separation turns one-sided reverse totality into an injective backward map. -/
theorem backward_injective
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    {context : AnchoredRelationContext Source Target Anchor Value}
    (matching : BackwardAnchoredMatching context) :
    Function.Injective matching.backward := by
  intro first second equality
  have secondMatches :
      context.Matches (matching.backward first) second := by
    rw [equality]
    exact matching.backward_matches second
  exact
    context.target_unique
      (matching.backward first)
      first
      second
      (matching.backward_matches first)
      secondMatches

end BackwardAnchoredMatching

namespace TotalAnchoredMatching

/-- Forget reverse totality and retain the forward structural embedding. -/
def toForwardMatching
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    {context : AnchoredRelationContext Source Target Anchor Value}
    (matching : TotalAnchoredMatching context) :
    ForwardAnchoredMatching context :=
  { forwardWitness := matching.forwardWitness }

/-- Forget forward totality and retain the backward structural embedding. -/
def toBackwardMatching
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    {context : AnchoredRelationContext Source Target Anchor Value}
    (matching : TotalAnchoredMatching context) :
    BackwardAnchoredMatching context :=
  { backwardWitness := matching.backwardWitness }

end TotalAnchoredMatching

/--
An exact transport compatible with the structurally defined anchored match
relation. Only forward compatibility is stored because exactness reconstructs
the corresponding backward match.
-/
structure CompatibleExactAlignment
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    (context : AnchoredRelationContext Source Target Anchor Value) where
  transport : ExactTypeTransport Source Target
  forwardMatches :
    ∀ source : Source,
      context.Matches source (transport.forward source)

namespace CompatibleExactAlignment

/-- Exactness reflects forward structural compatibility to the backward map. -/
theorem backwardMatches
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    {context : AnchoredRelationContext Source Target Anchor Value}
    (alignment : CompatibleExactAlignment context)
    (target : Target) :
    context.Matches (alignment.transport.backward target) target := by
  have matchProof :=
    alignment.forwardMatches (alignment.transport.backward target)
  rw [alignment.transport.backwardForward target] at matchProof
  exact matchProof

/-- Exact compatible alignment supplies constructive totality in both directions. -/
def toTotalMatching
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    {context : AnchoredRelationContext Source Target Anchor Value}
    (alignment : CompatibleExactAlignment context) :
    TotalAnchoredMatching context :=
  { forwardWitness := fun source =>
      ⟨alignment.transport.forward source,
        alignment.forwardMatches source⟩
    backwardWitness := fun target =>
      ⟨alignment.transport.backward target,
        alignment.backwardMatches target⟩ }

end CompatibleExactAlignment

namespace TotalAnchoredMatching

/-- Bidirectional total matching reconstructs a compatible exact alignment. -/
def toCompatibleExactAlignment
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    {context : AnchoredRelationContext Source Target Anchor Value}
    (matching : TotalAnchoredMatching context) :
    CompatibleExactAlignment context :=
  { transport := matching.toExactTransport
    forwardMatches := matching.forward_matches }

end TotalAnchoredMatching

namespace CompatibleExactAlignment

/-- Structural separation makes compatible exact alignments pointwise unique forward. -/
theorem forward_unique
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    {context : AnchoredRelationContext Source Target Anchor Value}
    (first second : CompatibleExactAlignment context)
    (source : Source) :
    first.transport.forward source = second.transport.forward source :=
  context.target_unique
    source
    (first.transport.forward source)
    (second.transport.forward source)
    (first.forwardMatches source)
    (second.forwardMatches source)

/-- Backward maps are pointwise unique once the compatible forward map is fixed. -/
theorem backward_unique
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    {context : AnchoredRelationContext Source Target Anchor Value}
    (first second : CompatibleExactAlignment context)
    (target : Target) :
    first.transport.backward target = second.transport.backward target :=
  ExactTypeTransport.backward_eq_of_forward_eq
    first.transport
    second.transport
    (first.forward_unique second)
    target

end CompatibleExactAlignment

end GenesisReconstruction
end Alignment

/- AXIOM_AUDIT_BEGIN -/
#print axioms Alignment.GenesisReconstruction.ForwardAnchoredMatching
#print axioms Alignment.GenesisReconstruction.ForwardAnchoredMatching.forward
#print axioms Alignment.GenesisReconstruction.ForwardAnchoredMatching.forward_injective
#print axioms Alignment.GenesisReconstruction.BackwardAnchoredMatching
#print axioms Alignment.GenesisReconstruction.BackwardAnchoredMatching.backward
#print axioms Alignment.GenesisReconstruction.BackwardAnchoredMatching.backward_injective
#print axioms Alignment.GenesisReconstruction.TotalAnchoredMatching.toForwardMatching
#print axioms Alignment.GenesisReconstruction.TotalAnchoredMatching.toBackwardMatching
#print axioms Alignment.GenesisReconstruction.CompatibleExactAlignment
#print axioms Alignment.GenesisReconstruction.CompatibleExactAlignment.backwardMatches
#print axioms Alignment.GenesisReconstruction.CompatibleExactAlignment.toTotalMatching
#print axioms Alignment.GenesisReconstruction.TotalAnchoredMatching.toCompatibleExactAlignment
#print axioms Alignment.GenesisReconstruction.CompatibleExactAlignment.forward_unique
#print axioms Alignment.GenesisReconstruction.CompatibleExactAlignment.backward_unique
/- AXIOM_AUDIT_END -/
