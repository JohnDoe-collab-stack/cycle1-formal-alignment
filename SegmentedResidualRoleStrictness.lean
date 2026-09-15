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

end SegmentedResidualRole.Strictness

/- AXIOM_AUDIT_BEGIN -/
#print axioms SegmentedResidualRole.Strictness.separatorKernel
#print axioms SegmentedResidualRole.Strictness.separatorUniqueResidualOccurrence
#print axioms SegmentedResidualRole.Strictness.separator_noExactInternalRealization
/- AXIOM_AUDIT_END -/
