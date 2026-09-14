import ExactTypeTransport

/- Independent carrier universes are intentional in the exact correspondences. -/
set_option linter.checkUnivs false

/-!
# Exact one-step constitutive alignment

This module isolates the content-independent structure extracted from the
canonical one-step persistence proof.  A constitutive transition and its
realizations remain distinct: the transition first separates prior identities
from one fresh identity, and each realization then supplies exact spokes from
those identities to its own carriers.

Admission, norms, specifications, and readout values are intentionally absent.
-/

namespace StrongPerimetralTurning

universe uInitial uExtended

/--
An exact one-step constitutive transition.  The extended carrier consists of
all prior identities together with one distinguished fresh identity.
-/
structure ExactOneStepConstitutiveAlignment where
  Initial : Type uInitial
  Extended : Type uExtended
  extension : ExactTypeTransport (Initial ⊕ Unit) Extended

namespace ExactOneStepConstitutiveAlignment

/-- The image of a prior identity in the extended carrier. -/
def old
    (alignment : ExactOneStepConstitutiveAlignment) :
    alignment.Initial → alignment.Extended :=
  fun identity => alignment.extension.forward (.inl identity)

/-- The distinguished fresh identity of the extended carrier. -/
def fresh
    (alignment : ExactOneStepConstitutiveAlignment) :
    alignment.Extended :=
  alignment.extension.forward (.inr ())

theorem old_injective
    (alignment : ExactOneStepConstitutiveAlignment) :
    Function.Injective alignment.old := by
  intro first second equality
  have classified := congrArg alignment.extension.backward equality
  unfold old at classified
  rw [alignment.extension.forwardBackward,
    alignment.extension.forwardBackward] at classified
  exact Sum.inl.inj classified

theorem old_ne_fresh
    (alignment : ExactOneStepConstitutiveAlignment)
    (identity : alignment.Initial) :
    alignment.old identity ≠ alignment.fresh := by
  intro equality
  have classified := congrArg alignment.extension.backward equality
  unfold old fresh at classified
  rw [alignment.extension.forwardBackward,
    alignment.extension.forwardBackward] at classified
  cases classified

universe uInitialConcrete uExtendedConcrete

/--
One exact carrier realization of a constitutive transition.  The two spokes
preserve the distinction between the transition and its realization.  This
content-independent structure transports identities only; it does not by
itself assert preservation of labels, order, or step semantics.
-/
structure Realization
    (alignment : ExactOneStepConstitutiveAlignment) where
  InitialConcrete : Type uInitialConcrete
  ExtendedConcrete : Type uExtendedConcrete
  initialSpoke :
    ExactTypeTransport alignment.Initial InitialConcrete
  extendedSpoke :
    ExactTypeTransport alignment.Extended ExtendedConcrete

namespace Realization

/-- The realized image of a prior concrete identity. -/
def old
    {alignment : ExactOneStepConstitutiveAlignment}
    (realization : alignment.Realization) :
    realization.InitialConcrete → realization.ExtendedConcrete :=
  fun concreteIdentity =>
    realization.extendedSpoke.forward
      (alignment.old
        (realization.initialSpoke.backward concreteIdentity))

/-- The realized fresh identity. -/
def fresh
    {alignment : ExactOneStepConstitutiveAlignment}
    (realization : alignment.Realization) :
    realization.ExtendedConcrete :=
  realization.extendedSpoke.forward alignment.fresh

/-- Every exact realization inherits the exact old/fresh split. -/
def concreteSplit
    {alignment : ExactOneStepConstitutiveAlignment}
    (realization : alignment.Realization) :
    ExactTypeTransport
      (realization.InitialConcrete ⊕ Unit)
      realization.ExtendedConcrete :=
  (realization.initialSpoke.reverse.sumUnit)
    |>.compose alignment.extension
    |>.compose realization.extendedSpoke

/-- Transport initial concrete identities through their common index. -/
def initialTransport
    {alignment : ExactOneStepConstitutiveAlignment}
    (source target : alignment.Realization) :
    ExactTypeTransport
      source.InitialConcrete target.InitialConcrete :=
  source.initialSpoke.reverse.compose target.initialSpoke

/-- Transport extended concrete identities through their common index. -/
def extendedTransport
    {alignment : ExactOneStepConstitutiveAlignment}
    (source target : alignment.Realization) :
    ExactTypeTransport
      source.ExtendedConcrete target.ExtendedConcrete :=
  source.extendedSpoke.reverse.compose target.extendedSpoke

/-- Prior identities commute with change of exact realization. -/
theorem old_natural
    {alignment : ExactOneStepConstitutiveAlignment}
    (source target : alignment.Realization)
    (identity : source.InitialConcrete) :
    (source.extendedTransport target).forward (source.old identity) =
      target.old ((source.initialTransport target).forward identity) := by
  change
    target.extendedSpoke.forward
        (source.extendedSpoke.backward
          (source.extendedSpoke.forward
            (alignment.old (source.initialSpoke.backward identity)))) =
      target.extendedSpoke.forward
        (alignment.old
          (target.initialSpoke.backward
            (target.initialSpoke.forward
              (source.initialSpoke.backward identity))))
  rw [source.extendedSpoke.forwardBackward]
  rw [target.initialSpoke.forwardBackward]

/-- The fresh identity commutes with change of exact realization. -/
theorem fresh_natural
    {alignment : ExactOneStepConstitutiveAlignment}
    (source target : alignment.Realization) :
    (source.extendedTransport target).forward source.fresh = target.fresh := by
  change
    target.extendedSpoke.forward
        (source.extendedSpoke.backward
          (source.extendedSpoke.forward alignment.fresh)) =
      target.extendedSpoke.forward alignment.fresh
  rw [source.extendedSpoke.forwardBackward]

theorem initialTransport_refl
    {alignment : ExactOneStepConstitutiveAlignment}
    (realization : alignment.Realization)
    (identity : realization.InitialConcrete) :
    (realization.initialTransport realization).forward identity = identity :=
  realization.initialSpoke.backwardForward identity

theorem extendedTransport_refl
    {alignment : ExactOneStepConstitutiveAlignment}
    (realization : alignment.Realization)
    (identity : realization.ExtendedConcrete) :
    (realization.extendedTransport realization).forward identity = identity :=
  realization.extendedSpoke.backwardForward identity

theorem initialTransport_forward_comp
    {alignment : ExactOneStepConstitutiveAlignment}
    (source middle target : alignment.Realization)
    (identity : source.InitialConcrete) :
    (middle.initialTransport target).forward
        ((source.initialTransport middle).forward identity) =
      (source.initialTransport target).forward identity := by
  change
    target.initialSpoke.forward
        (middle.initialSpoke.backward
          (middle.initialSpoke.forward
            (source.initialSpoke.backward identity))) =
      target.initialSpoke.forward (source.initialSpoke.backward identity)
  rw [middle.initialSpoke.forwardBackward]

theorem extendedTransport_forward_comp
    {alignment : ExactOneStepConstitutiveAlignment}
    (source middle target : alignment.Realization)
    (identity : source.ExtendedConcrete) :
    (middle.extendedTransport target).forward
        ((source.extendedTransport middle).forward identity) =
      (source.extendedTransport target).forward identity := by
  change
    target.extendedSpoke.forward
        (middle.extendedSpoke.backward
          (middle.extendedSpoke.forward
            (source.extendedSpoke.backward identity))) =
      target.extendedSpoke.forward (source.extendedSpoke.backward identity)
  rw [middle.extendedSpoke.forwardBackward]

/--
Pointwise uniqueness relative to agreement on every old identity and on the
fresh identity.
-/
theorem extendedTransport_unique_at
    {alignment : ExactOneStepConstitutiveAlignment}
    (source target : alignment.Realization)
    (candidate : source.ExtendedConcrete → target.ExtendedConcrete)
    (onOld :
      (identity : source.InitialConcrete) →
        candidate (source.old identity) =
          target.old ((source.initialTransport target).forward identity))
    (onFresh : candidate source.fresh = target.fresh)
    (identity : source.ExtendedConcrete) :
    candidate identity =
      (source.extendedTransport target).forward identity := by
  have reconstruction := source.concreteSplit.backwardForward identity
  generalize classificationEquality :
      source.concreteSplit.backward identity = classification
  at reconstruction
  cases classification with
  | inl oldIdentity =>
      change source.old oldIdentity = identity at reconstruction
      calc
        candidate identity = candidate (source.old oldIdentity) :=
          congrArg candidate reconstruction.symm
        _ = target.old
              ((source.initialTransport target).forward oldIdentity) :=
          onOld oldIdentity
        _ = (source.extendedTransport target).forward
              (source.old oldIdentity) :=
          (source.old_natural target oldIdentity).symm
        _ = (source.extendedTransport target).forward identity :=
          congrArg (source.extendedTransport target).forward reconstruction
  | inr residual =>
      cases residual
      change source.fresh = identity at reconstruction
      calc
        candidate identity = candidate source.fresh :=
          congrArg candidate reconstruction.symm
        _ = target.fresh := onFresh
        _ = (source.extendedTransport target).forward source.fresh :=
          (source.fresh_natural target).symm
        _ = (source.extendedTransport target).forward identity :=
          congrArg (source.extendedTransport target).forward reconstruction

end Realization
end ExactOneStepConstitutiveAlignment
end StrongPerimetralTurning

/- AXIOM_AUDIT_BEGIN -/
#print axioms StrongPerimetralTurning.ExactOneStepConstitutiveAlignment
#print axioms StrongPerimetralTurning.ExactOneStepConstitutiveAlignment.old_injective
#print axioms StrongPerimetralTurning.ExactOneStepConstitutiveAlignment.old_ne_fresh
#print axioms StrongPerimetralTurning.ExactOneStepConstitutiveAlignment.Realization
#print axioms StrongPerimetralTurning.ExactOneStepConstitutiveAlignment.Realization.concreteSplit
#print axioms StrongPerimetralTurning.ExactOneStepConstitutiveAlignment.Realization.old_natural
#print axioms StrongPerimetralTurning.ExactOneStepConstitutiveAlignment.Realization.fresh_natural
#print axioms StrongPerimetralTurning.ExactOneStepConstitutiveAlignment.Realization.initialTransport_forward_comp
#print axioms StrongPerimetralTurning.ExactOneStepConstitutiveAlignment.Realization.extendedTransport_forward_comp
#print axioms StrongPerimetralTurning.ExactOneStepConstitutiveAlignment.Realization.extendedTransport_unique_at
/- AXIOM_AUDIT_END -/
