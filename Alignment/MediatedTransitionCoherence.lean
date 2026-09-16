import Alignment.FinitePersistence
import MediatedTransitionCoherence

/-!
# Finite alignment as mediated transition coherence

This module does not alter the finite alignment core.  It proves that the
existing finite naturality square is an instance of the independent mediated
transition theorem.

The common mediator is `IteratedCarrier`.  Concrete extension realizes
`IteratedCarrier.embedFrom`, and concrete change of realization preserves the
same index.  Exact spokes make the terminal observation injective.
-/

namespace Alignment
namespace FiniteConstitutiveAlignment
namespace Realization

universe uInitial uCarrier uConcrete

/--
The two routes of the finite naturality square already agree after observation
in the target `IteratedCarrier`.  This is the non-faithful stage of mediated
transition coherence.
-/
theorem extend_transport_observed_commutation
    {Initial : Type uInitial}
    {sourceDepth targetDepth : Nat}
    {sourceAlignment : FiniteConstitutiveAlignment Initial sourceDepth}
    {targetAlignment : FiniteConstitutiveAlignment Initial targetDepth}
    (sourceA sourceB : sourceAlignment.Realization)
    (targetA targetB : targetAlignment.Realization)
    (depth : DepthExtension sourceDepth targetDepth)
    (identity : sourceA.Concrete) :
    targetB.indexedSpoke.backward
        ((targetA.transport targetB).forward
          (sourceA.extend targetA depth identity)) =
      targetB.indexedSpoke.backward
        (sourceB.extend targetB depth
          ((sourceA.transport sourceB).forward identity)) := by
  apply MediatedTransitionCoherence.observed_commutation
    (f := sourceA.extend targetA depth)
    (g := sourceB.extend targetB depth)
    (p := (sourceA.transport sourceB).forward)
    (q := (targetA.transport targetB).forward)
    (step := IteratedCarrier.embedFrom depth)
    (a0 := sourceA.indexedSpoke.backward)
    (a1 := targetA.indexedSpoke.backward)
    (b0 := sourceB.indexedSpoke.backward)
    (b1 := targetB.indexedSpoke.backward)
  · intro concrete
    change
      targetA.indexedSpoke.backward
          (targetA.indexedSpoke.forward
            (IteratedCarrier.embedFrom depth
              (sourceA.indexedSpoke.backward concrete))) =
        IteratedCarrier.embedFrom depth
          (sourceA.indexedSpoke.backward concrete)
    exact targetA.indexedSpoke.forwardBackward _
  · intro concrete
    change
      targetB.indexedSpoke.backward
          (targetB.indexedSpoke.forward
            (IteratedCarrier.embedFrom depth
              (sourceB.indexedSpoke.backward concrete))) =
        IteratedCarrier.embedFrom depth
          (sourceB.indexedSpoke.backward concrete)
    exact targetB.indexedSpoke.forwardBackward _
  · intro concrete
    change
      sourceB.indexedSpoke.backward
          (sourceB.indexedSpoke.forward
            (sourceA.indexedSpoke.backward concrete)) =
        sourceA.indexedSpoke.backward concrete
    exact sourceB.indexedSpoke.forwardBackward _
  · intro concrete
    change
      targetB.indexedSpoke.backward
          (targetB.indexedSpoke.forward
            (targetA.indexedSpoke.backward concrete)) =
        targetA.indexedSpoke.backward concrete
    exact targetB.indexedSpoke.forwardBackward _

/--
The existing finite naturality square follows from the generic mediated
transition theorem.  No new assumption is added to the alignment layer.
-/
theorem extend_transport_natural_via_mediated_coherence
    {Initial : Type uInitial}
    {sourceDepth targetDepth : Nat}
    {sourceAlignment : FiniteConstitutiveAlignment Initial sourceDepth}
    {targetAlignment : FiniteConstitutiveAlignment Initial targetDepth}
    (sourceA sourceB : sourceAlignment.Realization)
    (targetA targetB : targetAlignment.Realization)
    (depth : DepthExtension sourceDepth targetDepth)
    (identity : sourceA.Concrete) :
    (targetA.transport targetB).forward
        (sourceA.extend targetA depth identity) =
      sourceB.extend targetB depth
        ((sourceA.transport sourceB).forward identity) := by
  apply MediatedTransitionCoherence.commute
    (f := sourceA.extend targetA depth)
    (g := sourceB.extend targetB depth)
    (p := (sourceA.transport sourceB).forward)
    (q := (targetA.transport targetB).forward)
    (step := IteratedCarrier.embedFrom depth)
    (a0 := sourceA.indexedSpoke.backward)
    (a1 := targetA.indexedSpoke.backward)
    (b0 := sourceB.indexedSpoke.backward)
    (b1 := targetB.indexedSpoke.backward)
  · intro concrete
    change
      targetA.indexedSpoke.backward
          (targetA.indexedSpoke.forward
            (IteratedCarrier.embedFrom depth
              (sourceA.indexedSpoke.backward concrete))) =
        IteratedCarrier.embedFrom depth
          (sourceA.indexedSpoke.backward concrete)
    exact targetA.indexedSpoke.forwardBackward _
  · intro concrete
    change
      targetB.indexedSpoke.backward
          (targetB.indexedSpoke.forward
            (IteratedCarrier.embedFrom depth
              (sourceB.indexedSpoke.backward concrete))) =
        IteratedCarrier.embedFrom depth
          (sourceB.indexedSpoke.backward concrete)
    exact targetB.indexedSpoke.forwardBackward _
  · intro concrete
    change
      sourceB.indexedSpoke.backward
          (sourceB.indexedSpoke.forward
            (sourceA.indexedSpoke.backward concrete)) =
        sourceA.indexedSpoke.backward concrete
    exact sourceB.indexedSpoke.forwardBackward _
  · intro concrete
    change
      targetB.indexedSpoke.backward
          (targetB.indexedSpoke.forward
            (targetA.indexedSpoke.backward concrete)) =
        targetA.indexedSpoke.backward concrete
    exact targetB.indexedSpoke.forwardBackward _
  · exact indexedSpoke_backward_injective targetB

end Realization
end FiniteConstitutiveAlignment
end Alignment

/- AXIOM_AUDIT_BEGIN -/
#print axioms Alignment.FiniteConstitutiveAlignment.Realization.extend_transport_observed_commutation
#print axioms Alignment.FiniteConstitutiveAlignment.Realization.extend_transport_natural_via_mediated_coherence
/- AXIOM_AUDIT_END -/
