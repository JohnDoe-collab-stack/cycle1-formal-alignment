import Init

/-!
# Mediated transition coherence

A minimal constructive theorem for commuting transition squares.

Two concrete paths need not be identified directly.  It is enough that both
realize the same transition in a common mediator.  Without faithfulness of the
terminal observation this yields equality only after observation; injectivity of
the terminal observation upgrades that equality to literal commutation.

This module is independent of any particular constitutive alignment, admission
regime, specification, or external theorem.
-/

namespace StrongPerimetralTurning
namespace MediatedTransitionCoherence

universe uA0 uA1 uB0 uB1 uM0 uM1

/--
Two paths that realize the same transition in a common mediator have the same
terminal observation.  No faithfulness or inverse is required at this stage.
-/
theorem observed_commutation
    {A0 : Type uA0}
    {A1 : Type uA1}
    {B0 : Type uB0}
    {B1 : Type uB1}
    {M0 : Type uM0}
    {M1 : Type uM1}
    (f : A0 → A1)
    (g : B0 → B1)
    (p : A0 → B0)
    (q : A1 → B1)
    (step : M0 → M1)
    (a0 : A0 → M0)
    (a1 : A1 → M1)
    (b0 : B0 → M0)
    (b1 : B1 → M1)
    (stepA : (x : A0) → a1 (f x) = step (a0 x))
    (stepB : (y : B0) → b1 (g y) = step (b0 y))
    (sourceCompatibility : (x : A0) → b0 (p x) = a0 x)
    (targetCompatibility : (z : A1) → b1 (q z) = a1 z)
    (x : A0) :
    b1 (q (f x)) = b1 (g (p x)) := by
  calc
    b1 (q (f x)) = a1 (f x) := targetCompatibility (f x)
    _ = step (a0 x) := stepA x
    _ = step (b0 (p x)) :=
      congrArg step (sourceCompatibility x).symm
    _ = b1 (g (p x)) := (stepB (p x)).symm

/--
If the terminal observation is injective, equality in the mediator lifts to
literal commutation of the two concrete paths.
-/
theorem commute
    {A0 : Type uA0}
    {A1 : Type uA1}
    {B0 : Type uB0}
    {B1 : Type uB1}
    {M0 : Type uM0}
    {M1 : Type uM1}
    (f : A0 → A1)
    (g : B0 → B1)
    (p : A0 → B0)
    (q : A1 → B1)
    (step : M0 → M1)
    (a0 : A0 → M0)
    (a1 : A1 → M1)
    (b0 : B0 → M0)
    (b1 : B1 → M1)
    (stepA : (x : A0) → a1 (f x) = step (a0 x))
    (stepB : (y : B0) → b1 (g y) = step (b0 y))
    (sourceCompatibility : (x : A0) → b0 (p x) = a0 x)
    (targetCompatibility : (z : A1) → b1 (q z) = a1 z)
    (faithful : Function.Injective b1)
    (x : A0) :
    q (f x) = g (p x) := by
  apply faithful
  exact observed_commutation
    f g p q step a0 a1 b0 b1
    stepA stepB sourceCompatibility targetCompatibility x

end MediatedTransitionCoherence
end StrongPerimetralTurning

/- AXIOM_AUDIT_BEGIN -/
#print axioms StrongPerimetralTurning.MediatedTransitionCoherence.observed_commutation
#print axioms StrongPerimetralTurning.MediatedTransitionCoherence.commute
/- AXIOM_AUDIT_END -/
