import ConstitutiveSearch.ClosureSearchWidthControlled
import ConstitutiveSearch.SAT.ExplicitFamilyConstitutiveProfile
import ConstitutiveSearch.SAT.ParametricComposedClosure

/-!
# Width-controlled closure on the parametric composed SAT family

The generic width-controlled closure theorem is instantiated here on the actual
SAT composition phase.

For every n:
* the state type is GeneratedStructuralBranchContext (F(n));
* the explicit candidate list is [middle];
* fuel is two;
* both candidate count and fuel are bounded by the phase's constitutive width,
  which is exactly two.

Thus the sufficient closure-search regime is tied directly to a certified
constitutive profile coordinate rather than to an unrelated external cap.
-/

namespace ConstitutiveSearch
namespace SAT

/-- Dependent state family of the composed SAT benchmark. -/
abbrev ComposedClosureStateFamily
    (count : Nat) : Type :=
  GeneratedStructuralBranchContext
    (explicitStackedSymmetricFamily count)

/--
The actual composition benchmark, viewed as a width-controlled closure
schedule.
-/
def composedClosureWidthControlledSchedule :
    WidthControlledClosureSchedule
      ComposedClosureStateFamily
      composedClosureConstitutivePhaseProfile :=
  { candidates := fun count =>
      [composedMiddle count]
    fuel := fun _count =>
      2
    source := composedSource
    target := composedTarget
    candidateLeWidth := by
      intro count
      change 1 ≤ 2
      exact
        Nat.succ_le_succ
          (Nat.zero_le 1)
    fuelLeWidth := by
      intro count
      change 2 ≤ 2
      exact Nat.le_refl 2 }

/-- The composition phase has the uniform constitutive width cap two. -/
def composedClosureUniformWidthBound :
    UniformProfileWidthBound
      composedClosureConstitutivePhaseProfile
      2 :=
  { widthLe := by
      intro count
      change 2 ≤ 2
      exact Nat.le_refl 2 }

/--
The actual SAT closure schedule therefore inherits input-polynomial executable
counter bounds from its constitutive width.
-/
theorem composedClosureWidthControlledCounters :
    WidthControlledClosureSchedule.InputPolynomialCounters
      (fun count =>
        composedPrimitiveSearch count)
      composedClosureWidthControlledSchedule :=
  composedClosureWidthControlledSchedule.inputPolynomialCounters_of_uniformWidth
    (fun count =>
      composedPrimitiveSearch count)
    2
    composedClosureUniformWidthBound

/--
The generic width-controlled run is definitionally the already certified
fuel-two SAT closure run.
-/
theorem composedClosureWidthControlled_run_eq_fuelTwo
    (count : Nat) :
    searchTransportClosureBounded
        (composedPrimitiveSearch count)
        (composedClosureWidthControlledSchedule.candidates count)
        (composedClosureWidthControlledSchedule.fuel count)
        (composedClosureWidthControlledSchedule.source count)
        (composedClosureWidthControlledSchedule.target count) =
      composedClosureFuelTwo count := by
  rfl

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.ComposedClosureStateFamily
#print axioms ConstitutiveSearch.SAT.composedClosureWidthControlledSchedule
#print axioms ConstitutiveSearch.SAT.composedClosureUniformWidthBound
#print axioms ConstitutiveSearch.SAT.composedClosureWidthControlledCounters
#print axioms ConstitutiveSearch.SAT.composedClosureWidthControlled_run_eq_fuelTwo
/- AXIOM_AUDIT_END -/
