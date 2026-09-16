import Alignment.MediatedTransitionCoherence

/-!
# Two-step finite alignment by mediated pasting

This module tests sequential composition of the mediated-coherence principle in
the existing finite alignment.  It does not alter `Alignment/*`.

Two adjacent finite naturality squares are pasted through their shared
`IteratedCarrier` mediator.  No injectivity is used at the intermediate depth;
exactness is needed only at the terminal spoke to recover literal equality.
-/

namespace Alignment
namespace FiniteConstitutiveAlignment
namespace Realization

universe uInitial

private theorem pasting_indexedSpoke_backward_injective
    {Initial : Type uInitial}
    {depth : Nat}
    {alignment : FiniteConstitutiveAlignment Initial depth}
    (realization : alignment.Realization) :
    Function.Injective realization.indexedSpoke.backward := by
  intro first second equality
  calc
    first =
        realization.indexedSpoke.forward
          (realization.indexedSpoke.backward first) :=
      (realization.indexedSpoke.backwardForward first).symm
    _ =
        realization.indexedSpoke.forward
          (realization.indexedSpoke.backward second) :=
      congrArg realization.indexedSpoke.forward equality
    _ = second :=
      realization.indexedSpoke.backwardForward second

/--
Two consecutive extension squares paste after observation in the terminal
`IteratedCarrier`.
-/
theorem extend_transport_twoStep_observed_pasting
    {Initial : Type uInitial}
    {sourceDepth middleDepth targetDepth : Nat}
    {sourceAlignment : FiniteConstitutiveAlignment Initial sourceDepth}
    {middleAlignment : FiniteConstitutiveAlignment Initial middleDepth}
    {targetAlignment : FiniteConstitutiveAlignment Initial targetDepth}
    (sourceA sourceB : sourceAlignment.Realization)
    (middleA middleB : middleAlignment.Realization)
    (targetA targetB : targetAlignment.Realization)
    (sourceToMiddle : DepthExtension sourceDepth middleDepth)
    (middleToTarget : DepthExtension middleDepth targetDepth)
    (identity : sourceA.Concrete) :
    targetB.indexedSpoke.backward
        ((targetA.transport targetB).forward
          (middleA.extend targetA middleToTarget
            (sourceA.extend middleA sourceToMiddle identity))) =
      targetB.indexedSpoke.backward
        (middleB.extend targetB middleToTarget
          (sourceB.extend middleB sourceToMiddle
            ((sourceA.transport sourceB).forward identity))) := by
  apply MediatedTransitionCoherence.observed_commutation_paste
    (f01 := sourceA.extend middleA sourceToMiddle)
    (f12 := middleA.extend targetA middleToTarget)
    (g01 := sourceB.extend middleB sourceToMiddle)
    (g12 := middleB.extend targetB middleToTarget)
    (p0 := (sourceA.transport sourceB).forward)
    (p1 := (middleA.transport middleB).forward)
    (p2 := (targetA.transport targetB).forward)
    (step01 := IteratedCarrier.embedFrom sourceToMiddle)
    (step12 := IteratedCarrier.embedFrom middleToTarget)
    (a0 := sourceA.indexedSpoke.backward)
    (a1 := middleA.indexedSpoke.backward)
    (a2 := targetA.indexedSpoke.backward)
    (b0 := sourceB.indexedSpoke.backward)
    (b1 := middleB.indexedSpoke.backward)
    (b2 := targetB.indexedSpoke.backward)
  · intro concrete
    change
      middleA.indexedSpoke.backward
          (middleA.indexedSpoke.forward
            (IteratedCarrier.embedFrom sourceToMiddle
              (sourceA.indexedSpoke.backward concrete))) =
        IteratedCarrier.embedFrom sourceToMiddle
          (sourceA.indexedSpoke.backward concrete)
    exact middleA.indexedSpoke.forwardBackward _
  · intro concrete
    change
      middleB.indexedSpoke.backward
          (middleB.indexedSpoke.forward
            (IteratedCarrier.embedFrom sourceToMiddle
              (sourceB.indexedSpoke.backward concrete))) =
        IteratedCarrier.embedFrom sourceToMiddle
          (sourceB.indexedSpoke.backward concrete)
    exact middleB.indexedSpoke.forwardBackward _
  · intro concrete
    change
      targetA.indexedSpoke.backward
          (targetA.indexedSpoke.forward
            (IteratedCarrier.embedFrom middleToTarget
              (middleA.indexedSpoke.backward concrete))) =
        IteratedCarrier.embedFrom middleToTarget
          (middleA.indexedSpoke.backward concrete)
    exact targetA.indexedSpoke.forwardBackward _
  · intro concrete
    change
      targetB.indexedSpoke.backward
          (targetB.indexedSpoke.forward
            (IteratedCarrier.embedFrom middleToTarget
              (middleB.indexedSpoke.backward concrete))) =
        IteratedCarrier.embedFrom middleToTarget
          (middleB.indexedSpoke.backward concrete)
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
      middleB.indexedSpoke.backward
          (middleB.indexedSpoke.forward
            (middleA.indexedSpoke.backward concrete)) =
        middleA.indexedSpoke.backward concrete
    exact middleB.indexedSpoke.forwardBackward _
  · intro concrete
    change
      targetB.indexedSpoke.backward
          (targetB.indexedSpoke.forward
            (targetA.indexedSpoke.backward concrete)) =
        targetA.indexedSpoke.backward concrete
    exact targetB.indexedSpoke.forwardBackward _

/--
Terminal exactness lifts the pasted observed rectangle to a literal two-step
naturality law.  No intermediate injectivity assumption is used.
-/
theorem extend_transport_twoStep_natural_via_mediated_pasting
    {Initial : Type uInitial}
    {sourceDepth middleDepth targetDepth : Nat}
    {sourceAlignment : FiniteConstitutiveAlignment Initial sourceDepth}
    {middleAlignment : FiniteConstitutiveAlignment Initial middleDepth}
    {targetAlignment : FiniteConstitutiveAlignment Initial targetDepth}
    (sourceA sourceB : sourceAlignment.Realization)
    (middleA middleB : middleAlignment.Realization)
    (targetA targetB : targetAlignment.Realization)
    (sourceToMiddle : DepthExtension sourceDepth middleDepth)
    (middleToTarget : DepthExtension middleDepth targetDepth)
    (identity : sourceA.Concrete) :
    (targetA.transport targetB).forward
        (middleA.extend targetA middleToTarget
          (sourceA.extend middleA sourceToMiddle identity)) =
      middleB.extend targetB middleToTarget
        (sourceB.extend middleB sourceToMiddle
          ((sourceA.transport sourceB).forward identity)) := by
  exact
    pasting_indexedSpoke_backward_injective targetB
      (extend_transport_twoStep_observed_pasting
        sourceA sourceB middleA middleB targetA targetB
        sourceToMiddle middleToTarget identity)

end Realization
end FiniteConstitutiveAlignment
end Alignment

/- AXIOM_AUDIT_BEGIN -/
#print axioms Alignment.FiniteConstitutiveAlignment.Realization.extend_transport_twoStep_observed_pasting
#print axioms Alignment.FiniteConstitutiveAlignment.Realization.extend_transport_twoStep_natural_via_mediated_pasting
/- AXIOM_AUDIT_END -/
