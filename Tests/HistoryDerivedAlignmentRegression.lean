import Alignment.HistoryDerivedAlignment

namespace Alignment.Tests.HistoryDerivedAlignmentRegression

open GenesisReconstruction
open GenesisReconstruction.HistoryDerivedAlignment
open StrongPerimetralTurning

inductive SourceState
  | zero
  | one
  | two

inductive TargetState
  | alpha
  | beta
  | gamma

abbrev SourceStep (_ _ : SourceState) : Type := Unit
abbrev TargetStep (_ _ : TargetState) : Type := Unit

def sourceOne :
    History SourceStep SourceState.zero SourceState.one :=
  .extend .root ()

def targetOne :
    History TargetStep TargetState.alpha TargetState.beta :=
  .extend .root ()

def sourceTwo :
    History SourceStep SourceState.zero SourceState.two :=
  .extend sourceOne ()

def targetTwo :
    History TargetStep TargetState.alpha TargetState.gamma :=
  .extend targetOne ()

/--
No relation, value type, anchor, transport, or occurrence listing is supplied:
two one-step constitutions decide positively by computation.
-/
theorem oneStep_decides_aligned :
    (decide sourceOne targetOne).isAligned = true := by
  rfl

/-- The same holds at a larger finite history length. -/
theorem twoStep_decides_aligned :
    (decide sourceTwo targetTwo).isAligned = true := by
  rfl

/--
Different finite constitutive lengths are constructively rejected from the
derived occurrence structure alone.
-/
theorem oneAgainstTwo_decides_impossible :
    (decide sourceOne targetTwo).isAligned = false := by
  rfl

/-- The derived source relation is exactly structural chronology. -/
theorem derivedRelation_detects_old_before_fresh :
    (historyRelation
      (History.Occurrence.earlier
        (History.Occurrence.last :
          History.Occurrence sourceOne))
      (History.Occurrence.last :
        History.Occurrence sourceTwo)).precedes = true := by
  rfl

end Alignment.Tests.HistoryDerivedAlignmentRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms Alignment.Tests.HistoryDerivedAlignmentRegression.SourceState
#print axioms Alignment.Tests.HistoryDerivedAlignmentRegression.TargetState
#print axioms Alignment.Tests.HistoryDerivedAlignmentRegression.sourceOne
#print axioms Alignment.Tests.HistoryDerivedAlignmentRegression.targetOne
#print axioms Alignment.Tests.HistoryDerivedAlignmentRegression.sourceTwo
#print axioms Alignment.Tests.HistoryDerivedAlignmentRegression.targetTwo
#print axioms Alignment.Tests.HistoryDerivedAlignmentRegression.oneStep_decides_aligned
#print axioms Alignment.Tests.HistoryDerivedAlignmentRegression.twoStep_decides_aligned
#print axioms Alignment.Tests.HistoryDerivedAlignmentRegression.oneAgainstTwo_decides_impossible
#print axioms Alignment.Tests.HistoryDerivedAlignmentRegression.derivedRelation_detects_old_before_fresh
/- AXIOM_AUDIT_END -/
