import Alignment.DirectionalGenesisPersistence
import Tests.FiniteAnchoredMatchSearchRegression
import Tests.FiniteAlignmentClassificationRegression

namespace Alignment.Tests.DirectionalGenesisPersistenceRegression

open GenesisReconstruction
open GenesisReconstruction.DirectionalGenesisPersistence

/-- The exact finite matching yields a forward genesis embedding at every depth. -/
def exactForwardDepthThree :
    FiniteGenesisEmbedding
      FiniteAnchoredMatchSearchRegression.SourceNode
      FiniteAnchoredMatchSearchRegression.TargetNode
      3 :=
  finiteForwardEmbeddingOfMatching
    FiniteAnchoredMatchSearchRegression.computedMatching.toForwardMatching 3

/-- The exact finite matching also yields the symmetric backward embedding. -/
def exactBackwardDepthThree :
    FiniteGenesisEmbedding
      FiniteAnchoredMatchSearchRegression.TargetNode
      FiniteAnchoredMatchSearchRegression.SourceNode
      3 :=
  finiteBackwardEmbeddingOfMatching
    FiniteAnchoredMatchSearchRegression.computedMatching.toBackwardMatching 3

/-- Reconstruct the same forward structural matching independently through finite search. -/
def searchedForwardMatching :
    ForwardAnchoredMatching FiniteAnchoredMatchSearchRegression.context :=
  FiniteAnchoredMatchSearch.forwardMatchingOfCheck
    FiniteAnchoredMatchSearchRegression.context
    FiniteAnchoredMatchSearchRegression.anchorListing
    FiniteAnchoredMatchSearchRegression.sourceListing
    FiniteAnchoredMatchSearchRegression.targetListing
    FiniteAnchoredMatchSearchRegression.forward_check_succeeds

/-- Directional lifting preserves injectivity in the exact case. -/
theorem exact_forward_injective :
    Function.Injective exactForwardDepthThree.map :=
  exactForwardDepthThree.injective

/-- Directional lifting preserves every finite fresh-generation stratum. -/
theorem exact_forward_preservesGenesis :
    PreservesDirectionalGenesis exactForwardDepthThree.map :=
  exactForwardDepthThree.preservesGenesis

/-- Independently reconstructed forward matchings have the same finite lift. -/
theorem exact_forward_lift_canonical_against_search
    (identity :
      IteratedCarrier FiniteAnchoredMatchSearchRegression.SourceNode 3) :
    exactForwardDepthThree.map identity =
      (finiteForwardEmbeddingOfMatching searchedForwardMatching 3).map identity :=
  finiteForwardEmbedding_pointwise_unique
    FiniteAnchoredMatchSearchRegression.computedMatching.toForwardMatching
    searchedForwardMatching
    3 identity

/-- On exact matching, the weaker directional lift agrees with exact forward transport. -/
theorem exact_forward_agrees_with_transport
    (identity :
      IteratedCarrier FiniteAnchoredMatchSearchRegression.SourceNode 3) :
    exactForwardDepthThree.map identity =
      (FiniteAnchoredMatchSearchRegression.computedMatching.finiteTransport 3).forward identity :=
  totalMatching_directional_forward_agrees
    FiniteAnchoredMatchSearchRegression.computedMatching 3 identity

/-- The symmetric directional lift agrees with exact backward transport. -/
theorem exact_backward_agrees_with_transport
    (identity :
      IteratedCarrier FiniteAnchoredMatchSearchRegression.TargetNode 3) :
    exactBackwardDepthThree.map identity =
      (FiniteAnchoredMatchSearchRegression.computedMatching.finiteTransport 3).backward identity :=
  totalMatching_directional_backward_agrees
    FiniteAnchoredMatchSearchRegression.computedMatching 3 identity

/-- Exact classification exposes both directional genesis embeddings. -/
theorem exact_classification_has_forward_embedding :
    finiteForwardEmbedding?
      FiniteAnchoredMatchSearchRegression.computedClassification 3 ≠ none := by
  intro impossible
  change some _ = none at impossible
  cases impossible

/-- Exact classification exposes the reverse directional embedding as well. -/
theorem exact_classification_has_backward_embedding :
    finiteBackwardEmbedding?
      FiniteAnchoredMatchSearchRegression.computedClassification 3 ≠ none := by
  intro impossible
  change some _ = none at impossible
  cases impossible

/-- A forward-only initial matching still persists injectively through finite genesis. -/
def forwardOnlyDepthFour :
    FiniteGenesisEmbedding Unit FiniteAnchoredMatchSearchRegression.PartialTarget 4 :=
  finiteForwardEmbeddingOfMatching
    FiniteAnchoredMatchSearchRegression.partialForwardMatching 4

/-- Forward-only persistence does not need a reverse map. -/
theorem forwardOnly_depth_four_injective :
    Function.Injective forwardOnlyDepthFour.map :=
  forwardOnlyDepthFour.injective

/-- The forward-only lift still preserves all generated fresh strata. -/
theorem forwardOnly_depth_four_preservesGenesis :
    PreservesDirectionalGenesis forwardOnlyDepthFour.map :=
  forwardOnlyDepthFour.preservesGenesis

/-- The forward-only classification exposes the forward genesis embedding. -/
theorem forwardOnly_classification_has_forward_embedding :
    finiteForwardEmbedding?
      FiniteAnchoredMatchSearchRegression.partialClassification 4 ≠ none := by
  intro impossible
  change some _ = none at impossible
  cases impossible

/-- The same classification does not manufacture a backward genesis embedding. -/
theorem forwardOnly_classification_has_no_backward_embedding :
    finiteBackwardEmbedding?
      FiniteAnchoredMatchSearchRegression.partialClassification 4 = none := by
  rfl

/-- The backward-only classification exposes only the reverse genesis embedding. -/
theorem backwardOnly_classification_has_backward_embedding :
    finiteBackwardEmbedding?
      FiniteAlignmentClassificationRegression.backwardOnlyClassification 4 ≠ none := by
  intro impossible
  change some _ = none at impossible
  cases impossible

/-- No forward embedding is manufactured in the backward-only regime. -/
theorem backwardOnly_classification_has_no_forward_embedding :
    finiteForwardEmbedding?
      FiniteAlignmentClassificationRegression.backwardOnlyClassification 4 = none := by
  rfl

/-- The weakest negative regime exposes no forward finite genesis embedding. -/
theorem noDirectional_classification_has_no_forward_embedding :
    finiteForwardEmbedding?
      FiniteAlignmentClassificationRegression.noDirectionalClassification 4 = none := by
  rfl

/-- The weakest negative regime exposes no backward finite genesis embedding either. -/
theorem noDirectional_classification_has_no_backward_embedding :
    finiteBackwardEmbedding?
      FiniteAlignmentClassificationRegression.noDirectionalClassification 4 = none := by
  rfl

end Alignment.Tests.DirectionalGenesisPersistenceRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms Alignment.Tests.DirectionalGenesisPersistenceRegression.exactForwardDepthThree
#print axioms Alignment.Tests.DirectionalGenesisPersistenceRegression.exactBackwardDepthThree
#print axioms Alignment.Tests.DirectionalGenesisPersistenceRegression.searchedForwardMatching
#print axioms Alignment.Tests.DirectionalGenesisPersistenceRegression.exact_forward_injective
#print axioms Alignment.Tests.DirectionalGenesisPersistenceRegression.exact_forward_preservesGenesis
#print axioms Alignment.Tests.DirectionalGenesisPersistenceRegression.exact_forward_lift_canonical_against_search
#print axioms Alignment.Tests.DirectionalGenesisPersistenceRegression.exact_forward_agrees_with_transport
#print axioms Alignment.Tests.DirectionalGenesisPersistenceRegression.exact_backward_agrees_with_transport
#print axioms Alignment.Tests.DirectionalGenesisPersistenceRegression.exact_classification_has_forward_embedding
#print axioms Alignment.Tests.DirectionalGenesisPersistenceRegression.exact_classification_has_backward_embedding
#print axioms Alignment.Tests.DirectionalGenesisPersistenceRegression.forwardOnlyDepthFour
#print axioms Alignment.Tests.DirectionalGenesisPersistenceRegression.forwardOnly_depth_four_injective
#print axioms Alignment.Tests.DirectionalGenesisPersistenceRegression.forwardOnly_depth_four_preservesGenesis
#print axioms Alignment.Tests.DirectionalGenesisPersistenceRegression.forwardOnly_classification_has_forward_embedding
#print axioms Alignment.Tests.DirectionalGenesisPersistenceRegression.forwardOnly_classification_has_no_backward_embedding
#print axioms Alignment.Tests.DirectionalGenesisPersistenceRegression.backwardOnly_classification_has_backward_embedding
#print axioms Alignment.Tests.DirectionalGenesisPersistenceRegression.backwardOnly_classification_has_no_forward_embedding
#print axioms Alignment.Tests.DirectionalGenesisPersistenceRegression.noDirectional_classification_has_no_forward_embedding
#print axioms Alignment.Tests.DirectionalGenesisPersistenceRegression.noDirectional_classification_has_no_backward_embedding
/- AXIOM_AUDIT_END -/
