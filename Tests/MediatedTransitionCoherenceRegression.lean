import Alignment.MediatedTransitionCoherence

open Alignment

/-!
# Regression tests for mediated transition coherence

The first separator checks that observed commutation does not imply literal
commutation when terminal observation loses information.

The external-shape tests then reconstruct, with independent abstract data, the
two-stage pattern used by the semantic square studied outside the Lean project:
source/target state compatibility plus two realizations of the same `adjoin`
yield semantic commutation, while a local reflection law is needed only to lift
that equality to literal equality of terminal regimes.

The final test checks that the finite alignment specialization has exactly the
same statement as the established naturality law.
-/

namespace StrongPerimetralTurning
namespace Tests.MediatedTransitionCoherenceRegression

universe uInitial uCarrier uConcrete
universe uCorpus uRegime uMaterial uFormal uContent uState

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

/--
Abstract form of the external semantic square, without importing any external
notion.  The four equalities corresponding to source/target state compatibility
and the two `adjoin` realizations suffice for equality after observation.
-/
theorem external_shape_semantic_commutation
    {Corpus : Type uCorpus}
    {Regime : Type uRegime}
    {Material : Type uMaterial}
    {Formal : Type uFormal}
    {Content : Type uContent}
    {State : Type uState}
    (interpret : Corpus → Regime)
    (extend : Corpus → Material → Corpus)
    (incorporate : Regime → Formal → Regime)
    (corpusState : Corpus → State)
    (regimeState : Regime → State)
    (adjoin : State → Content → State)
    (source : Corpus)
    (material : Material)
    (formal : Formal)
    (content : Content)
    (sourceStateExact :
      regimeState (interpret source) = corpusState source)
    (targetStateExact :
      regimeState (interpret (extend source material)) =
        corpusState (extend source material))
    (materialUpdateExact :
      corpusState (extend source material) =
        adjoin (corpusState source) content)
    (formalUpdateExact :
      regimeState (incorporate (interpret source) formal) =
        adjoin (regimeState (interpret source)) content) :
    regimeState (interpret (extend source material)) =
      regimeState (incorporate (interpret source) formal) := by
  exact MediatedTransitionCoherence.observed_commutation
    (f := fun _ : Unit => ())
    (g := fun _ : Unit => incorporate (interpret source) formal)
    (p := fun _ : Unit => ())
    (q := fun _ : Unit => interpret (extend source material))
    (step := fun state => adjoin state content)
    (a0 := fun _ : Unit => corpusState source)
    (a1 := fun _ : Unit => corpusState (extend source material))
    (b0 := fun _ : Unit => regimeState (interpret source))
    (b1 := regimeState)
    (stepA := fun _ => materialUpdateExact)
    (stepB := fun _ => formalUpdateExact)
    (sourceCompatibility := fun _ => sourceStateExact)
    (targetCompatibility := fun _ => targetStateExact)
    ()

/--
The same external shape becomes a literal square when equality of the two
terminal semantic states is reflected locally to equality of the two terminal
regimes.  No global injectivity assumption is needed for this pointwise square.
-/
theorem external_shape_literal_commutation
    {Corpus : Type uCorpus}
    {Regime : Type uRegime}
    {Material : Type uMaterial}
    {Formal : Type uFormal}
    {Content : Type uContent}
    {State : Type uState}
    (interpret : Corpus → Regime)
    (extend : Corpus → Material → Corpus)
    (incorporate : Regime → Formal → Regime)
    (corpusState : Corpus → State)
    (regimeState : Regime → State)
    (adjoin : State → Content → State)
    (source : Corpus)
    (material : Material)
    (formal : Formal)
    (content : Content)
    (sourceStateExact :
      regimeState (interpret source) = corpusState source)
    (targetStateExact :
      regimeState (interpret (extend source material)) =
        corpusState (extend source material))
    (materialUpdateExact :
      corpusState (extend source material) =
        adjoin (corpusState source) content)
    (formalUpdateExact :
      regimeState (incorporate (interpret source) formal) =
        adjoin (regimeState (interpret source)) content)
    (localReflection :
      regimeState (interpret (extend source material)) =
          regimeState (incorporate (interpret source) formal) →
        interpret (extend source material) =
          incorporate (interpret source) formal) :
    interpret (extend source material) =
      incorporate (interpret source) formal := by
  exact MediatedTransitionCoherence.commute_of_local_reflection
    (f := fun _ : Unit => ())
    (g := fun _ : Unit => incorporate (interpret source) formal)
    (p := fun _ : Unit => ())
    (q := fun _ : Unit => interpret (extend source material))
    (step := fun state => adjoin state content)
    (a0 := fun _ : Unit => corpusState source)
    (a1 := fun _ : Unit => corpusState (extend source material))
    (b0 := fun _ : Unit => regimeState (interpret source))
    (b1 := regimeState)
    (stepA := fun _ => materialUpdateExact)
    (stepB := fun _ => formalUpdateExact)
    (sourceCompatibility := fun _ => sourceStateExact)
    (targetCompatibility := fun _ => targetStateExact)
    (localReflection := fun _ equality => localReflection equality)
    ()

/-! ## Load-bearing hypotheses -/

/-- `stepA` cannot be dropped from a theorem of the same generality. -/
theorem stepA_cannot_be_dropped :
    ¬ (∀
      {A0 A1 B0 B1 M0 M1 : Type}
      (f : A0 → A1)
      (g : B0 → B1)
      (p : A0 → B0)
      (q : A1 → B1)
      (step : M0 → M1)
      (a0 : A0 → M0)
      (a1 : A1 → M1)
      (b0 : B0 → M0)
      (b1 : B1 → M1),
      ((y : B0) → b1 (g y) = step (b0 y)) →
      ((x : A0) → b0 (p x) = a0 x) →
      ((z : A1) → b1 (q z) = a1 z) →
      Function.Injective b1 →
      (x : A0) → q (f x) = g (p x)) := by
  intro claim
  have impossible := claim
    (A0 := Unit) (A1 := Bool)
    (B0 := Unit) (B1 := Bool)
    (M0 := Unit) (M1 := Bool)
    (fun _ => true)
    (fun _ => false)
    (fun _ => ())
    (fun value => value)
    (fun _ => false)
    (fun _ => ())
    (fun value => value)
    (fun _ => ())
    (fun value => value)
    (fun _ => rfl)
    (fun _ => rfl)
    (fun _ => rfl)
    (fun _ _ equality => equality)
    ()
  cases impossible

/-- `stepB` cannot be dropped from a theorem of the same generality. -/
theorem stepB_cannot_be_dropped :
    ¬ (∀
      {A0 A1 B0 B1 M0 M1 : Type}
      (f : A0 → A1)
      (g : B0 → B1)
      (p : A0 → B0)
      (q : A1 → B1)
      (step : M0 → M1)
      (a0 : A0 → M0)
      (a1 : A1 → M1)
      (b0 : B0 → M0)
      (b1 : B1 → M1),
      ((x : A0) → a1 (f x) = step (a0 x)) →
      ((x : A0) → b0 (p x) = a0 x) →
      ((z : A1) → b1 (q z) = a1 z) →
      Function.Injective b1 →
      (x : A0) → q (f x) = g (p x)) := by
  intro claim
  have impossible := claim
    (A0 := Unit) (A1 := Bool)
    (B0 := Unit) (B1 := Bool)
    (M0 := Unit) (M1 := Bool)
    (fun _ => false)
    (fun _ => true)
    (fun _ => ())
    (fun value => value)
    (fun _ => false)
    (fun _ => ())
    (fun value => value)
    (fun _ => ())
    (fun value => value)
    (fun _ => rfl)
    (fun _ => rfl)
    (fun _ => rfl)
    (fun _ _ equality => equality)
    ()
  cases impossible

/-- Source compatibility cannot be dropped from a theorem of the same generality. -/
theorem sourceCompatibility_cannot_be_dropped :
    ¬ (∀
      {A0 A1 B0 B1 M0 M1 : Type}
      (f : A0 → A1)
      (g : B0 → B1)
      (p : A0 → B0)
      (q : A1 → B1)
      (step : M0 → M1)
      (a0 : A0 → M0)
      (a1 : A1 → M1)
      (b0 : B0 → M0)
      (b1 : B1 → M1),
      ((x : A0) → a1 (f x) = step (a0 x)) →
      ((y : B0) → b1 (g y) = step (b0 y)) →
      ((z : A1) → b1 (q z) = a1 z) →
      Function.Injective b1 →
      (x : A0) → q (f x) = g (p x)) := by
  intro claim
  have impossible := claim
    (A0 := Unit) (A1 := Bool)
    (B0 := Unit) (B1 := Bool)
    (M0 := Bool) (M1 := Bool)
    (fun _ => true)
    (fun _ => false)
    (fun _ => ())
    (fun value => value)
    (fun value => value)
    (fun _ => true)
    (fun value => value)
    (fun _ => false)
    (fun value => value)
    (fun _ => rfl)
    (fun _ => rfl)
    (fun _ => rfl)
    (fun _ _ equality => equality)
    ()
  cases impossible

/-- Target compatibility cannot be dropped from a theorem of the same generality. -/
theorem targetCompatibility_cannot_be_dropped :
    ¬ (∀
      {A0 A1 B0 B1 M0 M1 : Type}
      (f : A0 → A1)
      (g : B0 → B1)
      (p : A0 → B0)
      (q : A1 → B1)
      (step : M0 → M1)
      (a0 : A0 → M0)
      (a1 : A1 → M1)
      (b0 : B0 → M0)
      (b1 : B1 → M1),
      ((x : A0) → a1 (f x) = step (a0 x)) →
      ((y : B0) → b1 (g y) = step (b0 y)) →
      ((x : A0) → b0 (p x) = a0 x) →
      Function.Injective b1 →
      (x : A0) → q (f x) = g (p x)) := by
  intro claim
  have impossible := claim
    (A0 := Unit) (A1 := Bool)
    (B0 := Unit) (B1 := Bool)
    (M0 := Unit) (M1 := Bool)
    (fun _ => false)
    (fun _ => false)
    (fun _ => ())
    Bool.not
    (fun _ => false)
    (fun _ => ())
    (fun value => value)
    (fun _ => ())
    (fun value => value)
    (fun _ => rfl)
    (fun _ => rfl)
    (fun _ => rfl)
    (fun _ _ equality => equality)
    ()
  cases impossible

/-- Global injectivity is strictly stronger than the local reflection needed for a fixed square. -/
theorem constantObservation_not_injective :
    ¬ Function.Injective (fun _ : Bool => ()) := by
  intro injective
  have impossible : false = true := injective rfl
  cases impossible

theorem localReflection_can_close_nonInjective_square :
    (fun value : Bool => value)
        ((fun _ : Unit => false) ()) =
      (fun _ : Unit => false) ((fun _ : Unit => ()) ()) := by
  exact MediatedTransitionCoherence.commute_of_local_reflection
    (f := fun _ : Unit => false)
    (g := fun _ : Unit => false)
    (p := fun _ : Unit => ())
    (q := fun value : Bool => value)
    (step := fun _ : Unit => ())
    (a0 := fun _ : Unit => ())
    (a1 := fun _ : Bool => ())
    (b0 := fun _ : Unit => ())
    (b1 := fun _ : Bool => ())
    (stepA := fun _ => rfl)
    (stepB := fun _ => rfl)
    (sourceCompatibility := fun _ => rfl)
    (targetCompatibility := fun _ => rfl)
    (localReflection := fun _ _ => rfl)
    ()

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
#print axioms StrongPerimetralTurning.Tests.MediatedTransitionCoherenceRegression.external_shape_semantic_commutation
#print axioms StrongPerimetralTurning.Tests.MediatedTransitionCoherenceRegression.external_shape_literal_commutation
#print axioms StrongPerimetralTurning.Tests.MediatedTransitionCoherenceRegression.stepA_cannot_be_dropped
#print axioms StrongPerimetralTurning.Tests.MediatedTransitionCoherenceRegression.stepB_cannot_be_dropped
#print axioms StrongPerimetralTurning.Tests.MediatedTransitionCoherenceRegression.sourceCompatibility_cannot_be_dropped
#print axioms StrongPerimetralTurning.Tests.MediatedTransitionCoherenceRegression.targetCompatibility_cannot_be_dropped
#print axioms StrongPerimetralTurning.Tests.MediatedTransitionCoherenceRegression.constantObservation_not_injective
#print axioms StrongPerimetralTurning.Tests.MediatedTransitionCoherenceRegression.localReflection_can_close_nonInjective_square
#print axioms StrongPerimetralTurning.Tests.MediatedTransitionCoherenceRegression.finite_specialization_reproves_existing_square
/- AXIOM_AUDIT_END -/
