import Cycle1.MediatedTransitionCoherence

/-!
# Regression tests for mediated transition coherence

The first test checks that terminal faithfulness is genuinely stronger than
observed commutation: all mediator equations can hold while the literal square
fails when the terminal observation is non-injective.

The second test checks that the finite alignment specialization has exactly the
same statement as the established naturality law.
-/

namespace StrongPerimetralTurning
namespace Tests.MediatedTransitionCoherenceRegression

universe uInitial uCarrier uConcrete

def nonFaithfulStep : Unit → Unit := fun _ => ()
def nonFaithfulA : Unit → Bool := fun _ => false
def nonFaithfulB : Unit → Bool := fun _ => true
def nonFaithfulVerticalSource : Unit → Unit := fun _ => ()
def nonFaithfulVerticalTarget : Bool → Bool := fun value => value
def nonFaithfulSourceObservation : Unit → Unit := fun _ => ()
def nonFaithfulTargetObservation : Bool → Unit := fun _ => ()

theorem nonFaithful_observed_square_commutes :
    nonFaithfulTargetObservation
        (nonFaithfulVerticalTarget (nonFaithfulA ())) =
      nonFaithfulTargetObservation
        (nonFaithfulB (nonFaithfulVerticalSource ())) := by
  exact MediatedTransitionCoherence.observed_commutation
    nonFaithfulA
    nonFaithfulB
    nonFaithfulVerticalSource
    nonFaithfulVerticalTarget
    nonFaithfulStep
    nonFaithfulSourceObservation
    nonFaithfulTargetObservation
    nonFaithfulSourceObservation
    nonFaithfulTargetObservation
    (fun _ => rfl)
    (fun _ => rfl)
    (fun _ => rfl)
    (fun _ => rfl)
    ()

theorem nonFaithful_literal_square_fails :
    nonFaithfulVerticalTarget (nonFaithfulA ()) ≠
      nonFaithfulB (nonFaithfulVerticalSource ()) := by
  intro equality
  cases equality

theorem finite_specialization_reproves_existing_square
    {Initial : Type uInitial}
    {sourceDepth targetDepth : Nat}
    {sourceAlignment :
      FiniteConstitutiveAlignment Initial sourceDepth}
    {targetAlignment :
      FiniteConstitutiveAlignment Initial targetDepth}
    (sourceA sourceB : sourceAlignment.Realization)
    (targetA targetB : targetAlignment.Realization)
    (depth : DepthExtension sourceDepth targetDepth)
    (identity : sourceA.Concrete) :
    (targetA.transport targetB).forward
        (sourceA.extend targetA depth identity) =
      sourceB.extend targetB depth
        ((sourceA.transport sourceB).forward identity) := by
  exact
    FiniteConstitutiveAlignment.Realization.extend_transport_natural_via_mediated_coherence
      sourceA sourceB targetA targetB depth identity

end Tests.MediatedTransitionCoherenceRegression
end StrongPerimetralTurning

/- AXIOM_AUDIT_BEGIN -/
#print axioms StrongPerimetralTurning.Tests.MediatedTransitionCoherenceRegression.nonFaithful_observed_square_commutes
#print axioms StrongPerimetralTurning.Tests.MediatedTransitionCoherenceRegression.nonFaithful_literal_square_fails
#print axioms StrongPerimetralTurning.Tests.MediatedTransitionCoherenceRegression.finite_specialization_reproves_existing_square
/- AXIOM_AUDIT_END -/
