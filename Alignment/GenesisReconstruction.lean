import Alignment.FinitePersistence

/-!
# Reconstruction of finite constitutive alignment

This module studies when an exact transport between two independently indexed
finite constitutive carriers can be reconstructed from an alignment of their
initial carriers.

The key condition is genesis preservation: every identity introduced as fresh
at a finite depth must be transported to the identity introduced at the same
depth on the target side. No common initial carrier is assumed in advance.

Under that condition, the terminal exact transport determines an exact
transport between the two initial carriers. Re-extending that reconstructed
initial transport through the canonical finite old/fresh splits recovers the
original terminal transport pointwise.

This is a relative reconstruction result. It does not determine which initial
identities ought to correspond without structural information about the
initial carriers themselves.
-/

namespace Alignment
namespace GenesisReconstruction

universe uSource uTarget

/-- Every exact transport is injective in the forward direction. -/
theorem forward_injective
    {Source : Type uSource}
    {Target : Type uTarget}
    (transport : ExactTypeTransport Source Target) :
    Function.Injective transport.forward := by
  intro first second equality
  calc
    first = transport.backward (transport.forward first) :=
      (transport.forwardBackward first).symm
    _ = transport.backward (transport.forward second) :=
      congrArg transport.backward equality
    _ = second := transport.forwardBackward second

/-- Every exact transport is injective in the backward direction. -/
theorem backward_injective
    {Source : Type uSource}
    {Target : Type uTarget}
    (transport : ExactTypeTransport Source Target) :
    Function.Injective transport.backward := by
  intro first second equality
  calc
    first = transport.forward (transport.backward first) :=
      (transport.backwardForward first).symm
    _ = transport.forward (transport.backward second) :=
      congrArg transport.forward equality
    _ = second := transport.backwardForward second

/--
If the distinguished fresh point is preserved, no old source point can be
sent to the target fresh point.
-/
theorem forward_old_ne_fresh
    {Source : Type uSource}
    {Target : Type uTarget}
    (transport : ExactTypeTransport (Source ⊕ Unit) (Target ⊕ Unit))
    (freshPreserved :
      transport.forward (.inr ()) = (.inr () : Target ⊕ Unit))
    (source : Source) :
    transport.forward (.inl source) ≠ (.inr () : Target ⊕ Unit) := by
  intro equality
  have impossible :
      (Sum.inl source : Source ⊕ Unit) = Sum.inr () :=
    forward_injective transport (equality.trans freshPreserved.symm)
  cases impossible

/-- Forward preservation of the fresh point forces backward preservation too. -/
theorem backward_fresh
    {Source : Type uSource}
    {Target : Type uTarget}
    (transport : ExactTypeTransport (Source ⊕ Unit) (Target ⊕ Unit))
    (freshPreserved :
      transport.forward (.inr ()) = (.inr () : Target ⊕ Unit)) :
    transport.backward (.inr ()) = (.inr () : Source ⊕ Unit) := by
  apply forward_injective transport
  calc
    transport.forward (transport.backward (.inr ())) =
        (.inr () : Target ⊕ Unit) :=
      transport.backwardForward (.inr ())
    _ = transport.forward (.inr ()) := freshPreserved.symm

/--
If the distinguished fresh point is preserved, no old target point can be
sent backward to the source fresh point.
-/
theorem backward_old_ne_fresh
    {Source : Type uSource}
    {Target : Type uTarget}
    (transport : ExactTypeTransport (Source ⊕ Unit) (Target ⊕ Unit))
    (freshPreserved :
      transport.forward (.inr ()) = (.inr () : Target ⊕ Unit))
    (target : Target) :
    transport.backward (.inl target) ≠ (.inr () : Source ⊕ Unit) := by
  intro equality
  have impossible :
      (Sum.inl target : Target ⊕ Unit) = Sum.inr () :=
    backward_injective transport
      (equality.trans (backward_fresh transport freshPreserved).symm)
  cases impossible

/--
Constructively classify the forward image of an old source identity as an old
target identity, retaining the classification equation as data.
-/
def classifyForwardOld
    {Source : Type uSource}
    {Target : Type uTarget}
    (transport : ExactTypeTransport (Source ⊕ Unit) (Target ⊕ Unit))
    (freshPreserved :
      transport.forward (.inr ()) = (.inr () : Target ⊕ Unit))
    (source : Source) :
    { target : Target //
      transport.forward (.inl source) =
        (Sum.inl target : Target ⊕ Unit) } :=
  match equality : transport.forward (.inl source) with
  | .inl target => ⟨target, equality⟩
  | .inr witness => by
      cases witness
      exact False.elim
        (forward_old_ne_fresh transport freshPreserved source equality)

/--
Constructively classify the backward image of an old target identity as an old
source identity, retaining the classification equation as data.
-/
def classifyBackwardOld
    {Source : Type uSource}
    {Target : Type uTarget}
    (transport : ExactTypeTransport (Source ⊕ Unit) (Target ⊕ Unit))
    (freshPreserved :
      transport.forward (.inr ()) = (.inr () : Target ⊕ Unit))
    (target : Target) :
    { source : Source //
      transport.backward (.inl target) =
        (Sum.inl source : Source ⊕ Unit) } :=
  match equality : transport.backward (.inl target) with
  | .inl source => ⟨source, equality⟩
  | .inr witness => by
      cases witness
      exact False.elim
        (backward_old_ne_fresh transport freshPreserved target equality)

/-- Extract the old-to-old forward map from the constructive classifier. -/
def restrictOldForward
    {Source : Type uSource}
    {Target : Type uTarget}
    (transport : ExactTypeTransport (Source ⊕ Unit) (Target ⊕ Unit))
    (freshPreserved :
      transport.forward (.inr ()) = (.inr () : Target ⊕ Unit)) :
    Source → Target :=
  fun source => (classifyForwardOld transport freshPreserved source).1

/-- Extract the old-to-old backward map from the constructive classifier. -/
def restrictOldBackward
    {Source : Type uSource}
    {Target : Type uTarget}
    (transport : ExactTypeTransport (Source ⊕ Unit) (Target ⊕ Unit))
    (freshPreserved :
      transport.forward (.inr ()) = (.inr () : Target ⊕ Unit)) :
    Target → Source :=
  fun target => (classifyBackwardOld transport freshPreserved target).1

theorem restrictOldForward_spec
    {Source : Type uSource}
    {Target : Type uTarget}
    (transport : ExactTypeTransport (Source ⊕ Unit) (Target ⊕ Unit))
    (freshPreserved :
      transport.forward (.inr ()) = (.inr () : Target ⊕ Unit))
    (source : Source) :
    transport.forward (.inl source) =
      (Sum.inl
        (restrictOldForward transport freshPreserved source) :
        Target ⊕ Unit) :=
  (classifyForwardOld transport freshPreserved source).2

theorem restrictOldBackward_spec
    {Source : Type uSource}
    {Target : Type uTarget}
    (transport : ExactTypeTransport (Source ⊕ Unit) (Target ⊕ Unit))
    (freshPreserved :
      transport.forward (.inr ()) = (.inr () : Target ⊕ Unit))
    (target : Target) :
    transport.backward (.inl target) =
      (Sum.inl
        (restrictOldBackward transport freshPreserved target) :
        Source ⊕ Unit) :=
  (classifyBackwardOld transport freshPreserved target).2

/--
Restrict a fresh-preserving exact transport to the old carriers. No choice
principle is used: the exact old/fresh split supplies the classification.
-/
def restrictOld
    {Source : Type uSource}
    {Target : Type uTarget}
    (transport : ExactTypeTransport (Source ⊕ Unit) (Target ⊕ Unit))
    (freshPreserved :
      transport.forward (.inr ()) = (.inr () : Target ⊕ Unit)) :
    ExactTypeTransport Source Target :=
  { forward := restrictOldForward transport freshPreserved
    backward := restrictOldBackward transport freshPreserved
    forwardBackward := by
      intro source
      have lifted :
          (Sum.inl
              (restrictOldBackward transport freshPreserved
                (restrictOldForward transport freshPreserved source)) :
              Source ⊕ Unit) =
            Sum.inl source := by
        calc
          (Sum.inl
                (restrictOldBackward transport freshPreserved
                  (restrictOldForward transport freshPreserved source)) :
              Source ⊕ Unit) =
              transport.backward
                (Sum.inl
                  (restrictOldForward transport freshPreserved source)) :=
            (restrictOldBackward_spec transport freshPreserved
              (restrictOldForward transport freshPreserved source)).symm
          _ = transport.backward (transport.forward (Sum.inl source)) := by
            rw [restrictOldForward_spec transport freshPreserved source]
          _ = Sum.inl source := transport.forwardBackward _
      exact Sum.inl.inj lifted
    backwardForward := by
      intro target
      have lifted :
          (Sum.inl
              (restrictOldForward transport freshPreserved
                (restrictOldBackward transport freshPreserved target)) :
              Target ⊕ Unit) =
            Sum.inl target := by
        calc
          (Sum.inl
                (restrictOldForward transport freshPreserved
                  (restrictOldBackward transport freshPreserved target)) :
              Target ⊕ Unit) =
              transport.forward
                (Sum.inl
                  (restrictOldBackward transport freshPreserved target)) :=
            (restrictOldForward_spec transport freshPreserved
              (restrictOldBackward transport freshPreserved target)).symm
          _ = transport.forward (transport.backward (Sum.inl target)) := by
            rw [restrictOldBackward_spec transport freshPreserved target]
          _ = Sum.inl target := transport.backwardForward _
      exact Sum.inl.inj lifted }

/--
Lift an exact alignment of initial carriers through the canonical finite
old/fresh construction.
-/
def liftToDepth
    {Source : Type uSource}
    {Target : Type uTarget}
    (initial : ExactTypeTransport Source Target) :
    (depth : Nat) →
      ExactTypeTransport
        (IteratedCarrier Source depth)
        (IteratedCarrier Target depth)
  | 0 => initial
  | depth + 1 => (liftToDepth initial depth).sumUnit

/--
The lifted transport commutes with every canonical finite extension.
-/
theorem liftToDepth_embedFrom
    {Source : Type uSource}
    {Target : Type uTarget}
    (initial : ExactTypeTransport Source Target)
    {sourceDepth targetDepth : Nat}
    (depth : DepthExtension sourceDepth targetDepth)
    (identity : IteratedCarrier Source sourceDepth) :
    (liftToDepth initial targetDepth).forward
        (IteratedCarrier.embedFrom depth identity) =
      IteratedCarrier.embedFrom depth
        ((liftToDepth initial sourceDepth).forward identity) := by
  induction depth with
  | refl =>
      rfl
  | step prior inductionHypothesis =>
      exact congrArg Sum.inl inductionHypothesis

/-- Every finite fresh-generation stratum is preserved by a transport. -/
def PreservesGenesis
    {Source : Type uSource}
    {Target : Type uTarget}
    {depth : Nat}
    (transport :
      ExactTypeTransport
        (IteratedCarrier Source depth)
        (IteratedCarrier Target depth)) : Prop :=
  ∀ {birth : Nat}
      (extension : DepthExtension (birth + 1) depth),
    transport.forward
        (IteratedCarrier.embedFrom extension
          (@IteratedCarrier.freshAtStep Source birth)) =
      IteratedCarrier.embedFrom extension
        (@IteratedCarrier.freshAtStep Target birth)

theorem liftToDepth_preservesGenesis
    {Source : Type uSource}
    {Target : Type uTarget}
    (initial : ExactTypeTransport Source Target)
    (depth : Nat) :
    PreservesGenesis (liftToDepth initial depth) := by
  intro birth extension
  calc
    (liftToDepth initial depth).forward
        (IteratedCarrier.embedFrom extension
          (@IteratedCarrier.freshAtStep Source birth)) =
      IteratedCarrier.embedFrom extension
        ((liftToDepth initial (birth + 1)).forward
          (@IteratedCarrier.freshAtStep Source birth)) :=
      liftToDepth_embedFrom initial extension _
    _ = IteratedCarrier.embedFrom extension
          (@IteratedCarrier.freshAtStep Target birth) := by
      rfl

/-- Genesis preservation at a successor depth includes the latest fresh point. -/
theorem latestFresh_preserved
    {Source : Type uSource}
    {Target : Type uTarget}
    {depth : Nat}
    (transport :
      ExactTypeTransport
        (IteratedCarrier Source (depth + 1))
        (IteratedCarrier Target (depth + 1)))
    (preserves : PreservesGenesis transport) :
    transport.forward (@IteratedCarrier.freshAtStep Source depth) =
      @IteratedCarrier.freshAtStep Target depth := by
  have preserved :=
    preserves
      (birth := depth)
      (DepthExtension.refl (depth + 1))
  change
    transport.forward (@IteratedCarrier.freshAtStep Source depth) =
      @IteratedCarrier.freshAtStep Target depth at preserved
  exact preserved

/--
Restricting a genesis-preserving successor transport to its old part preserves
all earlier generation strata.
-/
theorem restrictOld_preservesGenesis
    {Source : Type uSource}
    {Target : Type uTarget}
    {depth : Nat}
    (transport :
      ExactTypeTransport
        (IteratedCarrier Source (depth + 1))
        (IteratedCarrier Target (depth + 1)))
    (preserves : PreservesGenesis transport)
    (freshPreserved :
      transport.forward (@IteratedCarrier.freshAtStep Source depth) =
        @IteratedCarrier.freshAtStep Target depth) :
    PreservesGenesis (restrictOld transport freshPreserved) := by
  intro birth extension
  have global :=
    preserves
      (birth := birth)
      (DepthExtension.step extension)
  have oldSpec :=
    restrictOldForward_spec transport freshPreserved
      (IteratedCarrier.embedFrom extension
        (@IteratedCarrier.freshAtStep Source birth))
  have lifted :
      (Sum.inl
          ((restrictOld transport freshPreserved).forward
            (IteratedCarrier.embedFrom extension
              (@IteratedCarrier.freshAtStep Source birth))) :
        IteratedCarrier Target depth ⊕ Unit) =
        Sum.inl
          (IteratedCarrier.embedFrom extension
            (@IteratedCarrier.freshAtStep Target birth)) := by
    calc
      (Sum.inl
            ((restrictOld transport freshPreserved).forward
              (IteratedCarrier.embedFrom extension
                (@IteratedCarrier.freshAtStep Source birth))) :
          IteratedCarrier Target depth ⊕ Unit) =
          transport.forward
            (Sum.inl
              (IteratedCarrier.embedFrom extension
                (@IteratedCarrier.freshAtStep Source birth))) :=
        oldSpec.symm
      _ = transport.forward
            (IteratedCarrier.embedFrom
              (DepthExtension.step extension)
              (@IteratedCarrier.freshAtStep Source birth)) := by
        rfl
      _ = IteratedCarrier.embedFrom
            (DepthExtension.step extension)
            (@IteratedCarrier.freshAtStep Target birth) :=
        global
      _ = (Sum.inl
            (IteratedCarrier.embedFrom extension
              (@IteratedCarrier.freshAtStep Target birth)) :
          IteratedCarrier Target depth ⊕ Unit) := by
        rfl
  exact Sum.inl.inj lifted

/-- The previous-depth transport reconstructed from the latest old/fresh split. -/
def previousTransport
    {Source : Type uSource}
    {Target : Type uTarget}
    {depth : Nat}
    (transport :
      ExactTypeTransport
        (IteratedCarrier Source (depth + 1))
        (IteratedCarrier Target (depth + 1)))
    (preserves : PreservesGenesis transport) :
    ExactTypeTransport
      (IteratedCarrier Source depth)
      (IteratedCarrier Target depth) :=
  restrictOld transport (latestFresh_preserved transport preserves)

theorem previousTransport_preservesGenesis
    {Source : Type uSource}
    {Target : Type uTarget}
    {depth : Nat}
    (transport :
      ExactTypeTransport
        (IteratedCarrier Source (depth + 1))
        (IteratedCarrier Target (depth + 1)))
    (preserves : PreservesGenesis transport) :
    PreservesGenesis (previousTransport transport preserves) :=
  restrictOld_preservesGenesis
    transport preserves (latestFresh_preserved transport preserves)

/--
Reconstruct the exact alignment of the initial carriers from a terminal
genesis-preserving transport.
-/
def reconstructInitial
    {Source : Type uSource}
    {Target : Type uTarget} :
    {depth : Nat} →
      (transport :
        ExactTypeTransport
          (IteratedCarrier Source depth)
          (IteratedCarrier Target depth)) →
      PreservesGenesis transport →
      ExactTypeTransport Source Target
  | 0, transport, _ => transport
  | depth + 1, transport, preserves =>
      reconstructInitial
        (previousTransport transport preserves)
        (previousTransport_preservesGenesis transport preserves)

/--
A genesis-preserving terminal transport is forced by the reconstructed initial
alignment. Equality is pointwise and constructive.
-/
theorem reconstruct_forward
    {Source : Type uSource}
    {Target : Type uTarget} :
    (depth : Nat) →
    (transport :
      ExactTypeTransport
        (IteratedCarrier Source depth)
        (IteratedCarrier Target depth)) →
    (preserves : PreservesGenesis transport) →
    (identity : IteratedCarrier Source depth) →
    transport.forward identity =
      (liftToDepth (reconstructInitial transport preserves) depth).forward
        identity
  | 0, _, _, _ => rfl
  | depth + 1, transport, preserves, identity => by
      cases identity with
      | inl prior =>
          have oldSpec :=
            restrictOldForward_spec transport
              (latestFresh_preserved transport preserves) prior
          have recursive :=
            reconstruct_forward
              depth
              (previousTransport transport preserves)
              (previousTransport_preservesGenesis transport preserves)
              prior
          calc
            transport.forward (Sum.inl prior) =
                Sum.inl
                  ((previousTransport transport preserves).forward prior) :=
              oldSpec
            _ = Sum.inl
                  ((liftToDepth
                    (reconstructInitial
                      (previousTransport transport preserves)
                      (previousTransport_preservesGenesis transport preserves))
                    depth).forward prior) :=
              congrArg
                (fun value =>
                  (Sum.inl value : IteratedCarrier Target (depth + 1)))
                recursive
            _ = (liftToDepth
                  (reconstructInitial transport preserves)
                  (depth + 1)).forward (Sum.inl prior) := by
              rfl
      | inr witness =>
          cases witness
          change
            transport.forward
                (@IteratedCarrier.freshAtStep Source depth) =
              @IteratedCarrier.freshAtStep Target depth
          exact latestFresh_preserved transport preserves

/-- The backward map is forced as well once the forward map is reconstructed. -/
theorem reconstruct_backward
    {Source : Type uSource}
    {Target : Type uTarget}
    (depth : Nat)
    (transport :
      ExactTypeTransport
        (IteratedCarrier Source depth)
        (IteratedCarrier Target depth))
    (preserves : PreservesGenesis transport)
    (identity : IteratedCarrier Target depth) :
    transport.backward identity =
      (liftToDepth (reconstructInitial transport preserves) depth).backward
        identity :=
  ExactTypeTransport.backward_eq_of_forward_eq
    transport
    (liftToDepth (reconstructInitial transport preserves) depth)
    (reconstruct_forward depth transport preserves)
    identity

end GenesisReconstruction
end Alignment

/- AXIOM_AUDIT_BEGIN -/
#print axioms Alignment.GenesisReconstruction.restrictOld
#print axioms Alignment.GenesisReconstruction.liftToDepth
#print axioms Alignment.GenesisReconstruction.liftToDepth_preservesGenesis
#print axioms Alignment.GenesisReconstruction.reconstructInitial
#print axioms Alignment.GenesisReconstruction.reconstruct_forward
#print axioms Alignment.GenesisReconstruction.reconstruct_backward
/- AXIOM_AUDIT_END -/
