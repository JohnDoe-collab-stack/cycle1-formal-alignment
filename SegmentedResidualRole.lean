import Init

/-!
# Unique residual role in a faithfully segmented realization

This module isolates the occurrence argument used by
`StrongPerimetralTurning`.  It has no dependency on circular presentations,
differences, provenance, loops, junctions, or totalizations.

The abstract input consists of an exact realization of the internal roles,
disjoint embeddings of the old and new occurrences into an extended
realization, an injective labelling by internal or residual roles, and a
contractible residual role type.  The output is that every new occurrence has
the residual label and that any two new occurrences coincide.  A positive new
part therefore has one distinguished occurrence and no other one.
-/

namespace SegmentedResidualRole

universe uInternal uResidual uOld uNew uExtended

/- A contractible residual role is constructively inhabited and has exactly
   one value.  No decidable equality or classical choice is required. -/
structure ContractibleRole (Role : Type uResidual) where
  center : Role
  contracts : (role : Role) → role = center

/- Exact realization is stored as two explicit maps with both round trips.
   The residual-role proof below only consumes the forward realization; the
   stronger structure records the exact scientific interface intended for
   later instantiations. -/
structure ExactInternalRealization
    (InternalRole : Type uInternal)
    (OldOccurrence : Type uOld) where
  roleToOccurrence : InternalRole → OldOccurrence
  occurrenceToRole : OldOccurrence → InternalRole
  occurrenceRoundTrip :
    (occurrence : OldOccurrence) →
      roleToOccurrence (occurrenceToRole occurrence) = occurrence
  roleRoundTrip :
    (role : InternalRole) →
      occurrenceToRole (roleToOccurrence role) = role

/- `FaithfulExtension` contains precisely the dependency boundary of the
   residual-role argument.  `embedOld` and `embedNew` need not arise from a
   particular history representation; only their disjointness and the
   injectivity of the new embedding are used. -/
structure FaithfulExtension
    (InternalRole : Type uInternal)
    (ResidualRole : Type uResidual)
    (OldOccurrence : Type uOld)
    (NewOccurrence : Type uNew)
    (ExtendedOccurrence : Type uExtended)
    (internal : ExactInternalRealization InternalRole OldOccurrence)
    (residual : ContractibleRole ResidualRole) where
  embedOld : OldOccurrence → ExtendedOccurrence
  embedNew : NewOccurrence → ExtendedOccurrence
  oldNewDisjoint :
    (oldOccurrence : OldOccurrence) →
    (newOccurrence : NewOccurrence) →
      embedOld oldOccurrence ≠ embedNew newOccurrence
  embedNewInjective : Function.Injective embedNew
  label : ExtendedOccurrence → InternalRole ⊕ ResidualRole
  preservesInternal :
    (role : InternalRole) →
      label (embedOld (internal.roleToOccurrence role)) = .inl role
  labelFaithful :
    (first second : ExtendedOccurrence) →
      label first = label second → first = second

namespace FaithfulExtension

theorem newOccurrence_cannotReuseInternalRole
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {OldOccurrence : Type uOld}
    {NewOccurrence : Type uNew}
    {ExtendedOccurrence : Type uExtended}
    {internal : ExactInternalRealization InternalRole OldOccurrence}
    {residual : ContractibleRole ResidualRole}
    (extension : FaithfulExtension
      InternalRole ResidualRole OldOccurrence NewOccurrence
      ExtendedOccurrence internal residual)
    (newOccurrence : NewOccurrence)
    (role : InternalRole)
    (labelEquality :
      extension.label (extension.embedNew newOccurrence) = .inl role) :
    False := by
  have sameLabel :
      extension.label
          (extension.embedOld (internal.roleToOccurrence role)) =
        extension.label (extension.embedNew newOccurrence) :=
    (extension.preservesInternal role).trans labelEquality.symm
  have sameOccurrence := extension.labelFaithful
    (extension.embedOld (internal.roleToOccurrence role))
    (extension.embedNew newOccurrence) sameLabel
  exact extension.oldNewDisjoint
    (internal.roleToOccurrence role) newOccurrence sameOccurrence

theorem newOccurrence_label_is_residual
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {OldOccurrence : Type uOld}
    {NewOccurrence : Type uNew}
    {ExtendedOccurrence : Type uExtended}
    {internal : ExactInternalRealization InternalRole OldOccurrence}
    {residual : ContractibleRole ResidualRole}
    (extension : FaithfulExtension
      InternalRole ResidualRole OldOccurrence NewOccurrence
      ExtendedOccurrence internal residual)
    (newOccurrence : NewOccurrence) :
    extension.label (extension.embedNew newOccurrence) =
      .inr residual.center := by
  cases labelEquality : extension.label (extension.embedNew newOccurrence) with
  | inl role =>
      exact False.elim
        (extension.newOccurrence_cannotReuseInternalRole
          newOccurrence role labelEquality)
  | inr role =>
      exact congrArg Sum.inr (residual.contracts role)

theorem newOccurrences_unique
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {OldOccurrence : Type uOld}
    {NewOccurrence : Type uNew}
    {ExtendedOccurrence : Type uExtended}
    {internal : ExactInternalRealization InternalRole OldOccurrence}
    {residual : ContractibleRole ResidualRole}
    (extension : FaithfulExtension
      InternalRole ResidualRole OldOccurrence NewOccurrence
      ExtendedOccurrence internal residual)
    (first second : NewOccurrence) : first = second := by
  have sameLabel :
      extension.label (extension.embedNew first) =
        extension.label (extension.embedNew second) :=
    (extension.newOccurrence_label_is_residual first).trans
      (extension.newOccurrence_label_is_residual second).symm
  exact extension.embedNewInjective
    (extension.labelFaithful
      (extension.embedNew first) (extension.embedNew second) sameLabel)

end FaithfulExtension

/- A positive new part supplies an actual new occurrence. -/
structure PositiveNewPart (NewOccurrence : Type uNew) where
  occurrence : NewOccurrence

/- The constructive output packages existence, the exact residual label, and
   uniqueness. -/
structure UniqueResidualOccurrence
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {OldOccurrence : Type uOld}
    {NewOccurrence : Type uNew}
    {ExtendedOccurrence : Type uExtended}
    {internal : ExactInternalRealization InternalRole OldOccurrence}
    {residual : ContractibleRole ResidualRole}
    (extension : FaithfulExtension
      InternalRole ResidualRole OldOccurrence NewOccurrence
      ExtendedOccurrence internal residual) where
  occurrence : NewOccurrence
  labelIsResidual :
    extension.label (extension.embedNew occurrence) = .inr residual.center
  unique : (other : NewOccurrence) → other = occurrence

def positiveExtension_hasUniqueResidualOccurrence
    {InternalRole : Type uInternal}
    {ResidualRole : Type uResidual}
    {OldOccurrence : Type uOld}
    {NewOccurrence : Type uNew}
    {ExtendedOccurrence : Type uExtended}
    {internal : ExactInternalRealization InternalRole OldOccurrence}
    {residual : ContractibleRole ResidualRole}
    (extension : FaithfulExtension
      InternalRole ResidualRole OldOccurrence NewOccurrence
      ExtendedOccurrence internal residual)
    (positive : PositiveNewPart NewOccurrence) :
    UniqueResidualOccurrence extension :=
  { occurrence := positive.occurrence
    labelIsResidual :=
      extension.newOccurrence_label_is_residual positive.occurrence
    unique := fun other =>
      extension.newOccurrences_unique other positive.occurrence }

end SegmentedResidualRole

/- AXIOM_AUDIT_BEGIN -/
#print axioms SegmentedResidualRole.ExactInternalRealization
#print axioms SegmentedResidualRole.FaithfulExtension.newOccurrence_cannotReuseInternalRole
#print axioms SegmentedResidualRole.FaithfulExtension.newOccurrence_label_is_residual
#print axioms SegmentedResidualRole.FaithfulExtension.newOccurrences_unique
#print axioms SegmentedResidualRole.positiveExtension_hasUniqueResidualOccurrence
/- AXIOM_AUDIT_END -/
