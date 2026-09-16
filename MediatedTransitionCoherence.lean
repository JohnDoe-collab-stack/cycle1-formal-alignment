import Init

/-!
# Mediated transition coherence

A small constructive theory for commuting transition squares.

Two concrete paths need not be identified directly. It is enough that both
realize the same transition in a common mediator. Without faithfulness of the
terminal observation this yields equality only after observation. A local
reflection principle on the two terminal path outputs is enough to recover
literal commutation; global injectivity is a stronger convenient corollary.

Sequential realization laws compose, and adjacent mediated squares can be
pasted without any faithfulness assumption at their intermediate boundary.
Only terminal reflection is needed to lift the pasted observed rectangle to a
literal commuting rectangle.

This module is independent of any particular constitutive alignment, admission
regime, specification, or external theorem.
-/

namespace MediatedTransitionCoherence

universe uA0 uA1 uA2 uB0 uB1 uB2 uM0 uM1 uM2

/-- Identity is realized by identity at the mediator level. -/
theorem realization_identity
    {A : Type uA0}
    {M : Type uM0}
    (observe : A → M)
    (x : A) :
    observe ((fun value => value) x) =
      (fun value => value) (observe x) := by
  rfl

/--
Realization of transitions is closed under sequential composition.
-/
theorem realization_comp
    {A0 : Type uA0}
    {A1 : Type uA1}
    {A2 : Type uA2}
    {M0 : Type uM0}
    {M1 : Type uM1}
    {M2 : Type uM2}
    (f01 : A0 → A1)
    (f12 : A1 → A2)
    (step01 : M0 → M1)
    (step12 : M1 → M2)
    (a0 : A0 → M0)
    (a1 : A1 → M1)
    (a2 : A2 → M2)
    (firstRealization :
      (x : A0) → a1 (f01 x) = step01 (a0 x))
    (secondRealization :
      (y : A1) → a2 (f12 y) = step12 (a1 y))
    (x : A0) :
    a2 (f12 (f01 x)) =
      step12 (step01 (a0 x)) := by
  calc
    a2 (f12 (f01 x)) = step12 (a1 (f01 x)) :=
      secondRealization (f01 x)
    _ = step12 (step01 (a0 x)) :=
      congrArg step12 (firstRealization x)

/--
Two paths that realize the same transition in a common mediator have the same
terminal observation. No faithfulness or inverse is required at this stage.
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
A pointwise reflection principle for the two terminal outputs is sufficient to
lift observed commutation to literal commutation. This is weaker than assuming
that the terminal observation is globally injective.
-/
theorem commute_of_local_reflection
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
    (localReflection :
      (x : A0) →
        b1 (q (f x)) = b1 (g (p x)) →
          q (f x) = g (p x))
    (x : A0) :
    q (f x) = g (p x) :=
  localReflection x
    (observed_commutation
      f g p q step a0 a1 b0 b1
      stepA stepB sourceCompatibility targetCompatibility x)

/--
Global injectivity of the terminal observation is a stronger, reusable form of
terminal faithfulness. It implies the local reflection needed above.
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
  apply commute_of_local_reflection
    f g p q step a0 a1 b0 b1
    stepA stepB sourceCompatibility targetCompatibility
  · intro _ equality
    exact faithful equality

/--
Sequential realization of two mediator steps already gives observed
commutation of the outer rectangle.  This theorem works directly at the
mediator level and does not use any equality of intermediate concrete outputs.
-/
theorem observed_commutation_comp
    {A0 : Type uA0}
    {A1 : Type uA1}
    {A2 : Type uA2}
    {B0 : Type uB0}
    {B1 : Type uB1}
    {B2 : Type uB2}
    {M0 : Type uM0}
    {M1 : Type uM1}
    {M2 : Type uM2}
    (f01 : A0 → A1)
    (f12 : A1 → A2)
    (g01 : B0 → B1)
    (g12 : B1 → B2)
    (p0 : A0 → B0)
    (p2 : A2 → B2)
    (step01 : M0 → M1)
    (step12 : M1 → M2)
    (a0 : A0 → M0)
    (a1 : A1 → M1)
    (a2 : A2 → M2)
    (b0 : B0 → M0)
    (b1 : B1 → M1)
    (b2 : B2 → M2)
    (stepA01 : (x : A0) → a1 (f01 x) = step01 (a0 x))
    (stepA12 : (y : A1) → a2 (f12 y) = step12 (a1 y))
    (stepB01 : (x : B0) → b1 (g01 x) = step01 (b0 x))
    (stepB12 : (y : B1) → b2 (g12 y) = step12 (b1 y))
    (sourceCompatibility : (x : A0) → b0 (p0 x) = a0 x)
    (targetCompatibility : (z : A2) → b2 (p2 z) = a2 z)
    (x : A0) :
    b2 (p2 (f12 (f01 x))) =
      b2 (g12 (g01 (p0 x))) := by
  calc
    b2 (p2 (f12 (f01 x))) = a2 (f12 (f01 x)) :=
      targetCompatibility (f12 (f01 x))
    _ = step12 (step01 (a0 x)) :=
      realization_comp
        f01 f12 step01 step12 a0 a1 a2 stepA01 stepA12 x
    _ = step12 (step01 (b0 (p0 x))) :=
      congrArg (fun state => step12 (step01 state))
        (sourceCompatibility x).symm
    _ = b2 (g12 (g01 (p0 x))) :=
      (realization_comp
        g01 g12 step01 step12 b0 b1 b2
        stepB01 stepB12 (p0 x)).symm

/--
Two adjacent mediated squares paste to an observed commuting outer rectangle.
No injectivity or reflection is required at the intermediate observation.
-/
theorem observed_commutation_paste
    {A0 : Type uA0}
    {A1 : Type uA1}
    {A2 : Type uA2}
    {B0 : Type uB0}
    {B1 : Type uB1}
    {B2 : Type uB2}
    {M0 : Type uM0}
    {M1 : Type uM1}
    {M2 : Type uM2}
    (f01 : A0 → A1)
    (f12 : A1 → A2)
    (g01 : B0 → B1)
    (g12 : B1 → B2)
    (p0 : A0 → B0)
    (p1 : A1 → B1)
    (p2 : A2 → B2)
    (step01 : M0 → M1)
    (step12 : M1 → M2)
    (a0 : A0 → M0)
    (a1 : A1 → M1)
    (a2 : A2 → M2)
    (b0 : B0 → M0)
    (b1 : B1 → M1)
    (b2 : B2 → M2)
    (stepA01 : (x : A0) → a1 (f01 x) = step01 (a0 x))
    (stepB01 : (x : B0) → b1 (g01 x) = step01 (b0 x))
    (stepA12 : (y : A1) → a2 (f12 y) = step12 (a1 y))
    (stepB12 : (y : B1) → b2 (g12 y) = step12 (b1 y))
    (sourceCompatibility : (x : A0) → b0 (p0 x) = a0 x)
    (middleCompatibility : (y : A1) → b1 (p1 y) = a1 y)
    (targetCompatibility : (z : A2) → b2 (p2 z) = a2 z)
    (x : A0) :
    b2 (p2 (f12 (f01 x))) =
      b2 (g12 (g01 (p0 x))) := by
  have firstObserved :
      b1 (p1 (f01 x)) = b1 (g01 (p0 x)) :=
    observed_commutation
      f01 g01 p0 p1 step01 a0 a1 b0 b1
      stepA01 stepB01 sourceCompatibility middleCompatibility x
  have secondObserved :
      b2 (p2 (f12 (f01 x))) =
        b2 (g12 (p1 (f01 x))) :=
    observed_commutation
      f12 g12 p1 p2 step12 a1 a2 b1 b2
      stepA12 stepB12 middleCompatibility targetCompatibility (f01 x)
  calc
    b2 (p2 (f12 (f01 x))) =
        b2 (g12 (p1 (f01 x))) := secondObserved
    _ = step12 (b1 (p1 (f01 x))) :=
      stepB12 (p1 (f01 x))
    _ = step12 (b1 (g01 (p0 x))) :=
      congrArg step12 firstObserved
    _ = b2 (g12 (g01 (p0 x))) :=
      (stepB12 (g01 (p0 x))).symm

/--
Terminal pointwise reflection lifts a pasted observed rectangle to literal
commutation.  No reflection is required at the intermediate stage.
-/
theorem commute_paste_of_local_reflection
    {A0 : Type uA0}
    {A1 : Type uA1}
    {A2 : Type uA2}
    {B0 : Type uB0}
    {B1 : Type uB1}
    {B2 : Type uB2}
    {M0 : Type uM0}
    {M1 : Type uM1}
    {M2 : Type uM2}
    (f01 : A0 → A1)
    (f12 : A1 → A2)
    (g01 : B0 → B1)
    (g12 : B1 → B2)
    (p0 : A0 → B0)
    (p1 : A1 → B1)
    (p2 : A2 → B2)
    (step01 : M0 → M1)
    (step12 : M1 → M2)
    (a0 : A0 → M0)
    (a1 : A1 → M1)
    (a2 : A2 → M2)
    (b0 : B0 → M0)
    (b1 : B1 → M1)
    (b2 : B2 → M2)
    (stepA01 : (x : A0) → a1 (f01 x) = step01 (a0 x))
    (stepB01 : (x : B0) → b1 (g01 x) = step01 (b0 x))
    (stepA12 : (y : A1) → a2 (f12 y) = step12 (a1 y))
    (stepB12 : (y : B1) → b2 (g12 y) = step12 (b1 y))
    (sourceCompatibility : (x : A0) → b0 (p0 x) = a0 x)
    (middleCompatibility : (y : A1) → b1 (p1 y) = a1 y)
    (targetCompatibility : (z : A2) → b2 (p2 z) = a2 z)
    (localReflection :
      (x : A0) →
        b2 (p2 (f12 (f01 x))) = b2 (g12 (g01 (p0 x))) →
          p2 (f12 (f01 x)) = g12 (g01 (p0 x)))
    (x : A0) :
    p2 (f12 (f01 x)) = g12 (g01 (p0 x)) :=
  localReflection x
    (observed_commutation_paste
      f01 f12 g01 g12 p0 p1 p2 step01 step12
      a0 a1 a2 b0 b1 b2
      stepA01 stepB01 stepA12 stepB12
      sourceCompatibility middleCompatibility targetCompatibility x)

/-- Global terminal injectivity is a reusable sufficient condition for pasted literal commutation. -/
theorem commute_paste
    {A0 : Type uA0}
    {A1 : Type uA1}
    {A2 : Type uA2}
    {B0 : Type uB0}
    {B1 : Type uB1}
    {B2 : Type uB2}
    {M0 : Type uM0}
    {M1 : Type uM1}
    {M2 : Type uM2}
    (f01 : A0 → A1)
    (f12 : A1 → A2)
    (g01 : B0 → B1)
    (g12 : B1 → B2)
    (p0 : A0 → B0)
    (p1 : A1 → B1)
    (p2 : A2 → B2)
    (step01 : M0 → M1)
    (step12 : M1 → M2)
    (a0 : A0 → M0)
    (a1 : A1 → M1)
    (a2 : A2 → M2)
    (b0 : B0 → M0)
    (b1 : B1 → M1)
    (b2 : B2 → M2)
    (stepA01 : (x : A0) → a1 (f01 x) = step01 (a0 x))
    (stepB01 : (x : B0) → b1 (g01 x) = step01 (b0 x))
    (stepA12 : (y : A1) → a2 (f12 y) = step12 (a1 y))
    (stepB12 : (y : B1) → b2 (g12 y) = step12 (b1 y))
    (sourceCompatibility : (x : A0) → b0 (p0 x) = a0 x)
    (middleCompatibility : (y : A1) → b1 (p1 y) = a1 y)
    (targetCompatibility : (z : A2) → b2 (p2 z) = a2 z)
    (faithful : Function.Injective b2)
    (x : A0) :
    p2 (f12 (f01 x)) = g12 (g01 (p0 x)) := by
  apply commute_paste_of_local_reflection
    f01 f12 g01 g12 p0 p1 p2 step01 step12
    a0 a1 a2 b0 b1 b2
    stepA01 stepB01 stepA12 stepB12
    sourceCompatibility middleCompatibility targetCompatibility
  · intro _ equality
    exact faithful equality

end MediatedTransitionCoherence

/- AXIOM_AUDIT_BEGIN -/
#print axioms MediatedTransitionCoherence.realization_identity
#print axioms MediatedTransitionCoherence.realization_comp
#print axioms MediatedTransitionCoherence.observed_commutation
#print axioms MediatedTransitionCoherence.commute_of_local_reflection
#print axioms MediatedTransitionCoherence.commute
#print axioms MediatedTransitionCoherence.observed_commutation_comp
#print axioms MediatedTransitionCoherence.observed_commutation_paste
#print axioms MediatedTransitionCoherence.commute_paste_of_local_reflection
#print axioms MediatedTransitionCoherence.commute_paste
/- AXIOM_AUDIT_END -/
