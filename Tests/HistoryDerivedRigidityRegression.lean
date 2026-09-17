import Alignment.HistoryDerivedRigidity
import Tests.HistoryDerivedAlignmentRegression

namespace Alignment.Tests.HistoryDerivedRigidityRegression

open GenesisReconstruction
open GenesisReconstruction.HistoryDerivedAlignment
open StrongPerimetralTurning
open HistoryDerivedAlignmentRegression

theorem sourceTwo_history_relation_is_rigid :
    RelationalPatternRigid
      (@historyRelation
        SourceState SourceStep
        SourceState.zero SourceState.two sourceTwo) :=
  historyRelation_patternRigid

def sourceTwoIdentityAlignment :
    ConstitutiveAlignment sourceTwo sourceTwo :=
  { initial :=
      { transport := ExactTypeTransport.reflexive _
        preservesPattern := by
          intro first second third fourth
          rfl } }

/-- Rigidity forces every compatible self-alignment to be the identity. -/
theorem sourceTwo_any_alignment_is_identity
    (candidate : ConstitutiveAlignment sourceTwo sourceTwo)
    (occurrence : History.Occurrence sourceTwo) :
    candidate.initial.transport.forward occurrence = occurrence := by
  exact
    candidate.constitutiveAlignment_forward_unique
      sourceTwo sourceTwo sourceTwoIdentityAlignment occurrence

end Alignment.Tests.HistoryDerivedRigidityRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms Alignment.Tests.HistoryDerivedRigidityRegression.sourceTwo_history_relation_is_rigid
#print axioms Alignment.Tests.HistoryDerivedRigidityRegression.sourceTwoIdentityAlignment
#print axioms Alignment.Tests.HistoryDerivedRigidityRegression.sourceTwo_any_alignment_is_identity
/- AXIOM_AUDIT_END -/
