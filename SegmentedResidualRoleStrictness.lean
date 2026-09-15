import SegmentedResidualRole

/-!
# Strictness of the residual dependency kernel

This module gives a positive constructive separator.  The weak residual kernel
is inhabited and produces an actual unique residual occurrence, while no exact
internal realization exists on the same internal-role and old-occurrence
types.  The separator uses the freedom of the weak kernel to identify two old
occurrences through `embedOld`; it is not an instance of the rich contract.
-/

namespace SegmentedResidualRole.Strictness

inductive SeparatorOldOccurrence where
  | represented
  | extra

inductive SeparatorExtendedOccurrence where
  | old
  | new

def separatorResidualRole : ContractibleRole PUnit :=
  { center := PUnit.unit
    contracts := fun role => by cases role; rfl }

def separatorKernel :
    ResidualUniquenessKernel
      PUnit PUnit SeparatorOldOccurrence PUnit
      SeparatorExtendedOccurrence separatorResidualRole :=
  { roleToOccurrence := fun _ => .represented
    embedOld := fun _ => .old
    embedNew := fun _ => .new
    oldNewDisjoint := by
      intro oldOccurrence newOccurrence equality
      cases newOccurrence
      cases equality
    embedNewInjective := by
      intro first second equality
      cases first
      cases second
      rfl
    label := fun occurrence =>
      match occurrence with
      | .old => .inl PUnit.unit
      | .new => .inr PUnit.unit
    preservesInternal := by
      intro role
      cases role
      rfl
    labelFaithful := by
      intro first second labelEquality
      cases first <;> cases second
      · rfl
      · cases labelEquality
      · cases labelEquality
      · rfl }

def separatorPositive : PositiveNewPart PUnit :=
  { occurrence := PUnit.unit }

def separatorUniqueResidualOccurrence :
    KernelUniqueResidualOccurrence separatorKernel :=
  positiveKernel_hasUniqueResidualOccurrence
    separatorKernel separatorPositive

theorem separator_oldOccurrences_distinct :
    SeparatorOldOccurrence.represented ≠ SeparatorOldOccurrence.extra := by
  intro equality
  cases equality

theorem separator_noExactInternalRealization :
    ExactInternalRealization PUnit SeparatorOldOccurrence → False := by
  intro internal
  have roleEquality :
      internal.occurrenceToRole SeparatorOldOccurrence.represented =
        internal.occurrenceToRole SeparatorOldOccurrence.extra := by
    cases internal.occurrenceToRole SeparatorOldOccurrence.represented
    cases internal.occurrenceToRole SeparatorOldOccurrence.extra
    rfl
  have occurrenceEquality :
      SeparatorOldOccurrence.represented =
        SeparatorOldOccurrence.extra :=
    (internal.occurrenceRoundTrip
      SeparatorOldOccurrence.represented).symm.trans
      ((congrArg internal.roleToOccurrence roleEquality).trans
        (internal.occurrenceRoundTrip SeparatorOldOccurrence.extra))
  exact separator_oldOccurrences_distinct occurrenceEquality

/-! ## A cardinality-neutral correspondence separator

The underlying types `Nat` and `Nat` support an exact internal realization.
The obstruction below is therefore not cardinality-theoretic: it is caused
by the particular forward correspondence fixed by the kernel, namely
`Nat.succ`, which cannot be completed to an exact inverse on all historical
occurrences.
-/

abbrev SharpResidualRole := Unit
abbrev SharpNewOccurrence := Unit
abbrev SharpExtendedOccurrence := Nat ⊕ Unit

def incompatibleForward : Nat → Nat :=
  Nat.succ

def sharpResidualContractible :
    ContractibleRole SharpResidualRole :=
  { center := Unit.unit
    contracts := fun _ => rfl }

def incompatibleKernel :
    ResidualUniquenessKernel
      Nat
      SharpResidualRole
      Nat
      SharpNewOccurrence
      SharpExtendedOccurrence
      sharpResidualContractible :=
  { roleToOccurrence := incompatibleForward
    embedOld := fun n => .inl (Nat.pred n)
    embedNew := fun _ => .inr Unit.unit
    oldNewDisjoint := by
      intro oldOccurrence newOccurrence equality
      cases equality
    embedNewInjective := by
      intro first second equality
      cases first
      cases second
      rfl
    label := id
    preservesInternal := by
      intro role
      rfl
    labelFaithful := by
      intro first second equality
      exact equality }

theorem incompatibleKernel_roleToOccurrence_apply
    (n : Nat) :
    incompatibleKernel.roleToOccurrence n = incompatibleForward n :=
  rfl

def richRealizationOnUnderlyingTypes :
    ExactInternalRealization Nat Nat :=
  { roleToOccurrence := id
    occurrenceToRole := id
    occurrenceRoundTrip := by
      intro occurrence
      rfl
    roleRoundTrip := by
      intro role
      rfl }

theorem richForward_at_zero :
    richRealizationOnUnderlyingTypes.roleToOccurrence 0 = 0 :=
  rfl

theorem incompatibleForward_at_zero :
    incompatibleForward 0 = 1 :=
  rfl

theorem richForward_differs_from_incompatible :
    richRealizationOnUnderlyingTypes.roleToOccurrence 0 ≠
      incompatibleForward 0 := by
  intro equality
  cases equality

theorem noCompatibleCompletion :
    ExactInternalCompletion incompatibleKernel → False := by
  intro completion
  have roundTrip := completion.occurrenceRoundTrip 0
  cases roundTrip

theorem noReconstructionConditions :
    ExactReconstructionConditions incompatibleKernel → False := by
  intro conditions
  have embeddedEqual :
      incompatibleKernel.embedOld 0 = incompatibleKernel.embedOld 1 := by
    rfl
  have zeroEqualsOne : (0 : Nat) = 1 :=
    conditions.embedOldInjective embeddedEqual
  cases zeroEqualsOne

end SegmentedResidualRole.Strictness

/- AXIOM_AUDIT_BEGIN -/
#print axioms SegmentedResidualRole.Strictness.SeparatorOldOccurrence
#print axioms SegmentedResidualRole.Strictness.SeparatorExtendedOccurrence
#print axioms SegmentedResidualRole.Strictness.separatorResidualRole
#print axioms SegmentedResidualRole.Strictness.separatorKernel
#print axioms SegmentedResidualRole.Strictness.separatorPositive
#print axioms SegmentedResidualRole.Strictness.separatorUniqueResidualOccurrence
#print axioms SegmentedResidualRole.Strictness.separator_oldOccurrences_distinct
#print axioms SegmentedResidualRole.Strictness.separator_noExactInternalRealization
#print axioms SegmentedResidualRole.Strictness.incompatibleForward
#print axioms SegmentedResidualRole.Strictness.incompatibleKernel
#print axioms SegmentedResidualRole.Strictness.richRealizationOnUnderlyingTypes
#print axioms SegmentedResidualRole.Strictness.richForward_differs_from_incompatible
#print axioms SegmentedResidualRole.Strictness.noCompatibleCompletion
#print axioms SegmentedResidualRole.Strictness.noReconstructionConditions
/- AXIOM_AUDIT_END -/
