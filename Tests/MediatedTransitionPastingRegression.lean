import Cycle1.MediatedTransitionPasting

/-!
# Regression tests for mediated transition pasting

These tests target the new composition claim rather than the original one-step
square.  In particular, the abstract separator deliberately makes the middle
observation non-injective and the first literal square false, while the pasted
rectangle remains valid after a second transition collapses the lost
distinction.  This checks that intermediate faithfulness is not being smuggled
into the pasting theorem.

The finite tests then derive the same two-step rectangle once through mediated
pasting and once through the pre-existing one-step naturality laws.
-/

namespace StrongPerimetralTurning
namespace Tests.MediatedTransitionPastingRegression

universe uInitial

/-! ## Abstract sequential composition -/

theorem identity_realization_is_unit
    (value : Bool) :
    (fun x : Bool => x) ((fun x : Bool => x) value) =
      (fun x : Bool => x) ((fun x : Bool => x) value) := by
  exact MediatedTransitionCoherence.realization_identity
    (fun x : Bool => x) value

theorem two_successor_realization_composes
    (value : Nat) :
    Nat.succ (Nat.succ value) = Nat.succ (Nat.succ value) := by
  exact MediatedTransitionCoherence.realization_comp
    (f01 := Nat.succ)
    (f12 := Nat.succ)
    (step01 := Nat.succ)
    (step12 := Nat.succ)
    (a0 := fun x : Nat => x)
    (a1 := fun x : Nat => x)
    (a2 := fun x : Nat => x)
    (firstRealization := fun _ => rfl)
    (secondRealization := fun _ => rfl)
    value

/-! ## Pasting without middle faithfulness -/

def pasteF01 : Unit → Bool := fun _ => false
def pasteG01 : Unit → Bool := fun _ => true
def pasteP0 : Unit → Unit := fun _ => ()
def pasteP1 : Bool → Bool := fun value => value

def pasteF12 : Bool → Bool := fun _ => false
def pasteG12 : Bool → Bool := fun _ => false
def pasteP2 : Bool → Bool := fun value => value

def pasteStep01 : Unit → Unit := fun _ => ()
def pasteStep12 : Unit → Bool := fun _ => false

def pasteA0 : Unit → Unit := fun _ => ()
def pasteA1 : Bool → Unit := fun _ => ()
def pasteA2 : Bool → Bool := fun value => value

def pasteB0 : Unit → Unit := fun _ => ()
def pasteB1 : Bool → Unit := fun _ => ()
def pasteB2 : Bool → Bool := fun value => value

theorem paste_middle_observation_not_injective :
    ¬ Function.Injective pasteB1 := by
  intro injective
  have impossible : false = true := injective rfl
  cases impossible

theorem paste_first_literal_square_fails :
    pasteP1 (pasteF01 ()) ≠ pasteG01 (pasteP0 ()) := by
  intro equality
  cases equality

theorem pasted_observed_rectangle_survives_nonFaithful_middle :
    pasteB2 (pasteP2 (pasteF12 (pasteF01 ()))) =
      pasteB2 (pasteG12 (pasteG01 (pasteP0 ()))) := by
  exact MediatedTransitionCoherence.observed_commutation_paste
    (f01 := pasteF01)
    (f12 := pasteF12)
    (g01 := pasteG01)
    (g12 := pasteG12)
    (p0 := pasteP0)
    (p1 := pasteP1)
    (p2 := pasteP2)
    (step01 := pasteStep01)
    (step12 := pasteStep12)
    (a0 := pasteA0)
    (a1 := pasteA1)
    (a2 := pasteA2)
    (b0 := pasteB0)
    (b1 := pasteB1)
    (b2 := pasteB2)
    (stepA01 := fun _ => rfl)
    (stepB01 := fun _ => rfl)
    (stepA12 := fun _ => rfl)
    (stepB12 := fun _ => rfl)
    (sourceCompatibility := fun _ => rfl)
    (middleCompatibility := fun _ => rfl)
    (targetCompatibility := fun _ => rfl)
    ()

theorem pasted_literal_rectangle_needs_only_terminal_faithfulness :
    pasteP2 (pasteF12 (pasteF01 ())) =
      pasteG12 (pasteG01 (pasteP0 ())) := by
  exact MediatedTransitionCoherence.commute_paste
    (f01 := pasteF01)
    (f12 := pasteF12)
    (g01 := pasteG01)
    (g12 := pasteG12)
    (p0 := pasteP0)
    (p1 := pasteP1)
    (p2 := pasteP2)
    (step01 := pasteStep01)
    (step12 := pasteStep12)
    (a0 := pasteA0)
    (a1 := pasteA1)
    (a2 := pasteA2)
    (b0 := pasteB0)
    (b1 := pasteB1)
    (b2 := pasteB2)
    (stepA01 := fun _ => rfl)
    (stepB01 := fun _ => rfl)
    (stepA12 := fun _ => rfl)
    (stepB12 := fun _ => rfl)
    (sourceCompatibility := fun _ => rfl)
    (middleCompatibility := fun _ => rfl)
    (targetCompatibility := fun _ => rfl)
    (faithful := fun _ _ equality => equality)
    ()

/-! ## Finite alignment instance -/

theorem finite_twoStep_pasting_reproves_rectangle
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
    FiniteConstitutiveAlignment.Realization.extend_transport_twoStep_natural_via_mediated_pasting
      sourceA sourceB middleA middleB targetA targetB
      sourceToMiddle middleToTarget identity

/--
Independent rederivation of the same two-step rectangle using only the
pre-existing one-step naturality theorem twice.
-/
theorem existing_laws_rederive_same_twoStep_rectangle
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
  calc
    (targetA.transport targetB).forward
        (middleA.extend targetA middleToTarget
          (sourceA.extend middleA sourceToMiddle identity)) =
      middleB.extend targetB middleToTarget
        ((middleA.transport middleB).forward
          (sourceA.extend middleA sourceToMiddle identity)) := by
      exact
        FiniteConstitutiveAlignment.Realization.extend_transport_natural
          middleA middleB targetA targetB middleToTarget
          (sourceA.extend middleA sourceToMiddle identity)
    _ =
      middleB.extend targetB middleToTarget
        (sourceB.extend middleB sourceToMiddle
          ((sourceA.transport sourceB).forward identity)) := by
      rw [FiniteConstitutiveAlignment.Realization.extend_transport_natural
        sourceA sourceB middleA middleB sourceToMiddle identity]

end Tests.MediatedTransitionPastingRegression
end StrongPerimetralTurning

/- AXIOM_AUDIT_BEGIN -/
#print axioms StrongPerimetralTurning.Tests.MediatedTransitionPastingRegression.identity_realization_is_unit
#print axioms StrongPerimetralTurning.Tests.MediatedTransitionPastingRegression.two_successor_realization_composes
#print axioms StrongPerimetralTurning.Tests.MediatedTransitionPastingRegression.paste_middle_observation_not_injective
#print axioms StrongPerimetralTurning.Tests.MediatedTransitionPastingRegression.paste_first_literal_square_fails
#print axioms StrongPerimetralTurning.Tests.MediatedTransitionPastingRegression.pasted_observed_rectangle_survives_nonFaithful_middle
#print axioms StrongPerimetralTurning.Tests.MediatedTransitionPastingRegression.pasted_literal_rectangle_needs_only_terminal_faithfulness
#print axioms StrongPerimetralTurning.Tests.MediatedTransitionPastingRegression.finite_twoStep_pasting_reproves_rectangle
#print axioms StrongPerimetralTurning.Tests.MediatedTransitionPastingRegression.existing_laws_rederive_same_twoStep_rectangle
/- AXIOM_AUDIT_END -/
