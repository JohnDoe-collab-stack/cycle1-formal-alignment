import Alignment.IntrinsicRelationalAmbiguity
import Tests.IntrinsicRelationalMediatorRegression

namespace Alignment.Tests.IntrinsicRelationalAmbiguityRegression

open GenesisReconstruction
open IntrinsicRelationalMediatorRegression

/-- The mediator-induced exact transport preserves the complete directed relation. -/
theorem mediator_alignment_preserves_full_relation
    (first second : SourceNode) :
    context.targetRelation
        (mediator.toIntrinsicCompatibleExactAlignment.transport.forward first)
        (mediator.toIntrinsicCompatibleExactAlignment.transport.forward second) =
      context.sourceRelation first second :=
  mediator.toIntrinsicCompatibleExactAlignment.preservesRelation first second

/-- The Boolean swap packages as a genuine target relation automorphism. -/
def swapAutomorphism : RelationAutomorphism symmetricRelation :=
  { transport := swapTransport
    preservesRelation := swap_preserves_symmetricRelation }

/-- Postcomposing identity alignment by the swap gives the swap alignment forward map. -/
theorem identity_postcompose_swap_forward
    (identity : Bool) :
    (identityAlignment.postcompose swapAutomorphism).transport.forward identity =
      swapAlignment.transport.forward identity := by
  cases identity <;> rfl

/-- The backward map agrees as well. -/
theorem identity_postcompose_swap_backward
    (identity : Bool) :
    (identityAlignment.postcompose swapAutomorphism).transport.backward identity =
      swapAlignment.transport.backward identity := by
  cases identity <;> rfl

/-- The difference automorphism between identity and swap is exactly the swap. -/
theorem identity_swap_difference_is_swap
    (identity : Bool) :
    (identityAlignment.differenceAutomorphism swapAlignment).transport.forward
        identity =
      swapAutomorphism.transport.forward identity := by
  cases identity <;> rfl

/-- The general torsor law reconstructs the competing swap alignment pointwise. -/
theorem torsor_law_reconstructs_swap_forward
    (identity : Bool) :
    (identityAlignment.postcompose
        (identityAlignment.differenceAutomorphism swapAlignment)).transport.forward
        identity =
      swapAlignment.transport.forward identity :=
  identityAlignment.postcompose_difference_forward swapAlignment identity

/-- The same exact reconstruction holds backwards. -/
theorem torsor_law_reconstructs_swap_backward
    (identity : Bool) :
    (identityAlignment.postcompose
        (identityAlignment.differenceAutomorphism swapAlignment)).transport.backward
        identity =
      swapAlignment.transport.backward identity :=
  identityAlignment.postcompose_difference_backward swapAlignment identity

/-- A nontrivial automorphism necessarily generates a distinct alignment. -/
theorem swap_generates_distinct_alignment :
    (identityAlignment.postcompose swapAutomorphism).transport.forward false ≠
      identityAlignment.transport.forward false := by
  exact identityAlignment.postcompose_differs_of_moves_target
    swapAutomorphism false (by
      change true ≠ false
      intro equality
      cases equality)

end Alignment.Tests.IntrinsicRelationalAmbiguityRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms Alignment.Tests.IntrinsicRelationalAmbiguityRegression.mediator_alignment_preserves_full_relation
#print axioms Alignment.Tests.IntrinsicRelationalAmbiguityRegression.swapAutomorphism
#print axioms Alignment.Tests.IntrinsicRelationalAmbiguityRegression.identity_postcompose_swap_forward
#print axioms Alignment.Tests.IntrinsicRelationalAmbiguityRegression.identity_postcompose_swap_backward
#print axioms Alignment.Tests.IntrinsicRelationalAmbiguityRegression.identity_swap_difference_is_swap
#print axioms Alignment.Tests.IntrinsicRelationalAmbiguityRegression.torsor_law_reconstructs_swap_forward
#print axioms Alignment.Tests.IntrinsicRelationalAmbiguityRegression.torsor_law_reconstructs_swap_backward
#print axioms Alignment.Tests.IntrinsicRelationalAmbiguityRegression.swap_generates_distinct_alignment
/- AXIOM_AUDIT_END -/