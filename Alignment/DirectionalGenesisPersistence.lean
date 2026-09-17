import Alignment.FiniteAlignmentClassification

/-!
# Directional persistence through arbitrary natural-depth genesis

Exact transport is not required to propagate an injective structural matching
through the canonical iterated old/fresh construction. A one-sided injective map
on the initial carriers can be lifted recursively by preserving old identities
through `Sum.inl` and mapping each newly generated identity to the fresh point
at the same depth.

This module keeps that weaker directional result distinct from exact transport.
A forward-only alignment therefore persists as an injective
fresh-preserving embedding for every `depth : Nat`, without manufacturing a
reverse map. The backward-only case is symmetric.

Profile separation also makes the one-sided structural map pointwise unique.
That initial uniqueness propagates through every natural-depth lift. Hence directional
persistence adds no new ambiguity once the anchored structural context fixes
the initial matching.
-/

namespace Alignment
namespace GenesisReconstruction
namespace DirectionalGenesisPersistence

open FiniteAlignmentClassification

universe uSource uTarget uAnchor uValue

/-- Lift an arbitrary initial map through the finite old/fresh construction. -/
def liftMap
    {Source : Type uSource}
    {Target : Type uTarget}
    (initial : Source → Target) :
    (depth : Nat) →
      IteratedCarrier Source depth → IteratedCarrier Target depth
  | 0 => initial
  | depth + 1 => fun identity =>
      match identity with
      | .inl old => .inl (liftMap initial depth old)
      | .inr _ => .inr ()

/-- An injective initial map remains injective at every natural-number depth. -/
theorem liftMap_injective
    {Source : Type uSource}
    {Target : Type uTarget}
    (initial : Source → Target)
    (initialInjective : Function.Injective initial) :
    (depth : Nat) → Function.Injective (liftMap initial depth)
  | 0 => initialInjective
  | depth + 1 => by
      intro first second equality
      cases first with
      | inl firstOld =>
          cases second with
          | inl secondOld =>
              have oldEquality :
                  liftMap initial depth firstOld =
                    liftMap initial depth secondOld :=
                Sum.inl.inj equality
              exact
                congrArg Sum.inl
                  (liftMap_injective initial initialInjective depth oldEquality)
          | inr secondFresh =>
              cases secondFresh
              cases equality
      | inr firstFresh =>
          cases firstFresh
          cases second with
          | inl secondOld =>
              cases equality
          | inr secondFresh =>
              cases secondFresh
              rfl

/-- Pointwise agreement of initial maps propagates through every natural-depth lift. -/
theorem liftMap_congr
    {Source : Type uSource}
    {Target : Type uTarget}
    (first second : Source → Target)
    (agreement : ∀ identity : Source, first identity = second identity) :
    (depth : Nat) →
      ∀ identity : IteratedCarrier Source depth,
        liftMap first depth identity = liftMap second depth identity
  | 0, identity => agreement identity
  | depth + 1, .inl old =>
      congrArg Sum.inl (liftMap_congr first second agreement depth old)
  | _ + 1, .inr witness => by
      cases witness
      rfl

/-- Directional preservation of every fresh-generation stratum below the chosen natural depth. -/
def PreservesDirectionalGenesis
    {Source : Type uSource}
    {Target : Type uTarget}
    {depth : Nat}
    (map : IteratedCarrier Source depth → IteratedCarrier Target depth) : Prop :=
  ∀ {birth : Nat}
      (extension : DepthExtension (birth + 1) depth),
    map
        (IteratedCarrier.embedFrom extension
          (@IteratedCarrier.freshAtStep Source birth)) =
      IteratedCarrier.embedFrom extension
        (@IteratedCarrier.freshAtStep Target birth)

/-- The lifted map commutes with every canonical extension between natural-number depths. -/
theorem liftMap_embedFrom
    {Source : Type uSource}
    {Target : Type uTarget}
    (initial : Source → Target)
    {sourceDepth targetDepth : Nat}
    (extension : DepthExtension sourceDepth targetDepth)
    (identity : IteratedCarrier Source sourceDepth) :
    liftMap initial targetDepth
        (IteratedCarrier.embedFrom extension identity) =
      IteratedCarrier.embedFrom extension
        (liftMap initial sourceDepth identity) := by
  induction extension with
  | refl =>
      rfl
  | step prior inductionHypothesis =>
      exact congrArg Sum.inl inductionHypothesis

/-- Every lifted map preserves the genesis strata, independently of injectivity. -/
theorem liftMap_preservesGenesis
    {Source : Type uSource}
    {Target : Type uTarget}
    (initial : Source → Target)
    (depth : Nat) :
    PreservesDirectionalGenesis (liftMap initial depth) := by
  intro birth extension
  calc
    liftMap initial depth
        (IteratedCarrier.embedFrom extension
          (@IteratedCarrier.freshAtStep Source birth)) =
      IteratedCarrier.embedFrom extension
        (liftMap initial (birth + 1)
          (@IteratedCarrier.freshAtStep Source birth)) :=
      liftMap_embedFrom initial extension _
    _ = IteratedCarrier.embedFrom extension
          (@IteratedCarrier.freshAtStep Target birth) := by
      rfl

/-- Witness-carrying directional embedding at an arbitrary natural depth, preserving genesis. -/
structure FiniteGenesisEmbedding
    (Source : Type uSource)
    (Target : Type uTarget)
    (depth : Nat) where
  map : IteratedCarrier Source depth → IteratedCarrier Target depth
  injective : Function.Injective map
  preservesGenesis : PreservesDirectionalGenesis map

/-- Construct the genesis embedding at an arbitrary natural depth induced by an injective initial map. -/
def FiniteGenesisEmbedding.ofInjective
    {Source : Type uSource}
    {Target : Type uTarget}
    (initial : Source → Target)
    (initialInjective : Function.Injective initial)
    (depth : Nat) :
    FiniteGenesisEmbedding Source Target depth :=
  { map := liftMap initial depth
    injective := liftMap_injective initial initialInjective depth
    preservesGenesis := liftMap_preservesGenesis initial depth }

/-- A forward anchored matching persists as an injective genesis embedding. -/
def finiteForwardEmbeddingOfMatching
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    {context : AnchoredRelationContext Source Target Anchor Value}
    (matching : ForwardAnchoredMatching context)
    (depth : Nat) :
    FiniteGenesisEmbedding Source Target depth :=
  FiniteGenesisEmbedding.ofInjective
    matching.forward matching.forward_injective depth

/-- A backward anchored matching persists symmetrically from target to source. -/
def finiteBackwardEmbeddingOfMatching
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    {context : AnchoredRelationContext Source Target Anchor Value}
    (matching : BackwardAnchoredMatching context)
    (depth : Nat) :
    FiniteGenesisEmbedding Target Source depth :=
  FiniteGenesisEmbedding.ofInjective
    matching.backward matching.backward_injective depth

/-- Profile separation makes any two forward structural matchings pointwise equal. -/
theorem forwardMatching_pointwise_unique
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    {context : AnchoredRelationContext Source Target Anchor Value}
    (first second : ForwardAnchoredMatching context)
    (source : Source) :
    first.forward source = second.forward source :=
  context.target_unique
    source
    (first.forward source)
    (second.forward source)
    (first.forward_matches source)
    (second.forward_matches source)

/-- Profile separation makes any two backward structural matchings pointwise equal. -/
theorem backwardMatching_pointwise_unique
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    {context : AnchoredRelationContext Source Target Anchor Value}
    (first second : BackwardAnchoredMatching context)
    (target : Target) :
    first.backward target = second.backward target :=
  context.source_unique
    target
    (first.backward target)
    (second.backward target)
    (first.backward_matches target)
    (second.backward_matches target)

/-- The forward genesis embedding at any natural depth is canonical for a fixed anchored context. -/
theorem finiteForwardEmbedding_pointwise_unique
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    {context : AnchoredRelationContext Source Target Anchor Value}
    (first second : ForwardAnchoredMatching context)
    (depth : Nat)
    (identity : IteratedCarrier Source depth) :
    (finiteForwardEmbeddingOfMatching first depth).map identity =
      (finiteForwardEmbeddingOfMatching second depth).map identity := by
  change
    liftMap first.forward depth identity =
      liftMap second.forward depth identity
  exact
    liftMap_congr
      first.forward second.forward
      (forwardMatching_pointwise_unique first second)
      depth identity

/-- The backward genesis embedding at any natural depth is canonical for a fixed anchored context. -/
theorem finiteBackwardEmbedding_pointwise_unique
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    {context : AnchoredRelationContext Source Target Anchor Value}
    (first second : BackwardAnchoredMatching context)
    (depth : Nat)
    (identity : IteratedCarrier Target depth) :
    (finiteBackwardEmbeddingOfMatching first depth).map identity =
      (finiteBackwardEmbeddingOfMatching second depth).map identity := by
  change
    liftMap first.backward depth identity =
      liftMap second.backward depth identity
  exact
    liftMap_congr
      first.backward second.backward
      (backwardMatching_pointwise_unique first second)
      depth identity

/--
Extract the forward genesis embedding at the requested natural depth exactly from classifications that
contain forward structural totality.
-/
def finiteForwardEmbedding?
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    {context : AnchoredRelationContext Source Target Anchor Value}
    (classification : FiniteAlignmentClassification.Classification context)
    (depth : Nat) :
    Option (FiniteGenesisEmbedding Source Target depth) :=
  match classification with
  | .exact matching =>
      some (finiteForwardEmbeddingOfMatching matching.toForwardMatching depth)
  | .forwardOnly certificate =>
      some (finiteForwardEmbeddingOfMatching certificate.matching depth)
  | .backwardOnly _ => none
  | .noDirectionalMatching _ => none

/--
Extract the backward genesis embedding at the requested natural depth exactly from classifications that
contain reverse structural totality.
-/
def finiteBackwardEmbedding?
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    {context : AnchoredRelationContext Source Target Anchor Value}
    (classification : FiniteAlignmentClassification.Classification context)
    (depth : Nat) :
    Option (FiniteGenesisEmbedding Target Source depth) :=
  match classification with
  | .exact matching =>
      some (finiteBackwardEmbeddingOfMatching matching.toBackwardMatching depth)
  | .forwardOnly _ => none
  | .backwardOnly certificate =>
      some (finiteBackwardEmbeddingOfMatching certificate.matching depth)
  | .noDirectionalMatching _ => none

/--
For exact total matching, the directional forward lift agrees pointwise with
the forward map of the reconstructed exact transport at that natural depth.
-/
theorem totalMatching_directional_forward_agrees
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    {context : AnchoredRelationContext Source Target Anchor Value}
    (matching : TotalAnchoredMatching context)
    (depth : Nat)
    (identity : IteratedCarrier Source depth) :
    (finiteForwardEmbeddingOfMatching matching.toForwardMatching depth).map identity =
      (matching.finiteTransport depth).forward identity := by
  induction depth with
  | zero =>
      rfl
  | succ depth inductionHypothesis =>
      cases identity with
      | inl old =>
          exact congrArg Sum.inl (inductionHypothesis old)
      | inr fresh =>
          cases fresh
          rfl

/-- The symmetric directional lift agrees with the exact backward transport at that natural depth. -/
theorem totalMatching_directional_backward_agrees
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    {context : AnchoredRelationContext Source Target Anchor Value}
    (matching : TotalAnchoredMatching context)
    (depth : Nat)
    (identity : IteratedCarrier Target depth) :
    (finiteBackwardEmbeddingOfMatching matching.toBackwardMatching depth).map identity =
      (matching.finiteTransport depth).backward identity := by
  induction depth with
  | zero =>
      rfl
  | succ depth inductionHypothesis =>
      cases identity with
      | inl old =>
          exact congrArg Sum.inl (inductionHypothesis old)
      | inr fresh =>
          cases fresh
          rfl

end DirectionalGenesisPersistence
end GenesisReconstruction
end Alignment

/- AXIOM_AUDIT_BEGIN -/
#print axioms Alignment.GenesisReconstruction.DirectionalGenesisPersistence.liftMap
#print axioms Alignment.GenesisReconstruction.DirectionalGenesisPersistence.liftMap_injective
#print axioms Alignment.GenesisReconstruction.DirectionalGenesisPersistence.liftMap_congr
#print axioms Alignment.GenesisReconstruction.DirectionalGenesisPersistence.PreservesDirectionalGenesis
#print axioms Alignment.GenesisReconstruction.DirectionalGenesisPersistence.liftMap_embedFrom
#print axioms Alignment.GenesisReconstruction.DirectionalGenesisPersistence.liftMap_preservesGenesis
#print axioms Alignment.GenesisReconstruction.DirectionalGenesisPersistence.FiniteGenesisEmbedding
#print axioms Alignment.GenesisReconstruction.DirectionalGenesisPersistence.FiniteGenesisEmbedding.ofInjective
#print axioms Alignment.GenesisReconstruction.DirectionalGenesisPersistence.finiteForwardEmbeddingOfMatching
#print axioms Alignment.GenesisReconstruction.DirectionalGenesisPersistence.finiteBackwardEmbeddingOfMatching
#print axioms Alignment.GenesisReconstruction.DirectionalGenesisPersistence.forwardMatching_pointwise_unique
#print axioms Alignment.GenesisReconstruction.DirectionalGenesisPersistence.backwardMatching_pointwise_unique
#print axioms Alignment.GenesisReconstruction.DirectionalGenesisPersistence.finiteForwardEmbedding_pointwise_unique
#print axioms Alignment.GenesisReconstruction.DirectionalGenesisPersistence.finiteBackwardEmbedding_pointwise_unique
#print axioms Alignment.GenesisReconstruction.DirectionalGenesisPersistence.finiteForwardEmbedding?
#print axioms Alignment.GenesisReconstruction.DirectionalGenesisPersistence.finiteBackwardEmbedding?
#print axioms Alignment.GenesisReconstruction.DirectionalGenesisPersistence.totalMatching_directional_forward_agrees
#print axioms Alignment.GenesisReconstruction.DirectionalGenesisPersistence.totalMatching_directional_backward_agrees
/- AXIOM_AUDIT_END -/
