import ConstitutiveSearch.NPAndOrP.ConstitutiveFullStep

namespace ConstitutiveSearch.NPAndOrP

open SAT

/-- The four roles are projections of one produced stage, not four unrelated
algorithms and not complexity-class identifications. -/
structure ConstitutiveRoleStage {depth : Nat} {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) where
  npState : GeneratedStructuralBranchContext
    (distinctGrowingDiscoveryFormula (constructStage (depth + 1)).searchIndex)
  npStateExact : npState = (constructStage (depth + 1)).operationalRoot
  orOpening : AcceptingExactBinarySplit
    (generatedStructuralBranchSystem (distinctGrowingDiscoveryFormula (constructStage (depth + 1)).searchIndex))
    npState
    (npState.child run.discovery.var false (by rw [npStateExact]; exact run.discovery.fresh))
    (npState.child run.discovery.var true (by rw [npStateExact]; exact run.discovery.fresh))
  andDecision : StructuralBranchDecision
  andDecisionExact : andDecision = ⟨run.discovery.var, true⟩
  pRelation : GeneratedStructuralFlipAtRelation run.storedSchedule.entry.var
    run.storedSchedule.entry.source run.storedSchedule.entry.target
  pRelationExact : pRelation = run.storedSchedule.entry.relation
  completeExecution : FullStageExecution run
  outputBecomesNextCondition : completeExecution.output.1 = run.next.assignment

def constitutiveRoleStage {depth : Nat} {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) : ConstitutiveRoleStage run :=
  let npState := (constructStage (depth + 1)).operationalRoot
  { npState := npState
    npStateExact := rfl
    orOpening := generatedStructuralSplit npState run.discovery.var run.discovery.fresh
    andDecision := ⟨run.discovery.var, true⟩
    andDecisionExact := rfl
    pRelation := run.storedSchedule.entry.relation
    pRelationExact := rfl
    completeExecution := fullStageExecution run
    outputBecomesNextCondition := (fullStageExecution run).nextAssignmentExact }

/-- Every tail is indexed by the preceding stage's produced `next`, so the
cycle cannot consume an independently supplied replacement state. -/
inductive ConstitutiveRoleHistory : {depth count : Nat} → {input : SequentialAssignment depth} →
    SequentialHistory depth input count → Type where
  | nil (depth : Nat) (input : SequentialAssignment depth) :
      ConstitutiveRoleHistory (.nil depth input)
  | step {depth count : Nat} {input : SequentialAssignment depth}
      (head : SequentialStageRun depth input)
      (tail : SequentialHistory (depth + 1) head.next count)
      (roles : ConstitutiveRoleStage head)
      (nextRoles : ConstitutiveRoleHistory tail) :
      ConstitutiveRoleHistory (.step head tail)

def buildConstitutiveRoleHistory : {depth count : Nat} → {input : SequentialAssignment depth} →
    (history : SequentialHistory depth input count) → ConstitutiveRoleHistory history
  | _, _, _, .nil depth input => .nil depth input
  | _, _, _, .step head tail =>
      .step head tail (constitutiveRoleStage head) (buildConstitutiveRoleHistory tail)

theorem roleStage_relation_is_discovered {depth : Nat} {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) :
    HEq (constitutiveRoleStage run).pRelation run.discovery.relation := by
  rw [(constitutiveRoleStage run).pRelationExact]
  rw [run.storedSchedule.entryExact]
  rfl

theorem roleStage_complete_operation_is_next {depth : Nat} {input : SequentialAssignment depth}
    (run : SequentialStageRun depth input) :
    (constitutiveRoleStage run).completeExecution.output.1 = run.next.assignment :=
  (constitutiveRoleStage run).outputBecomesNextCondition

end ConstitutiveSearch.NPAndOrP

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NPAndOrP.constitutiveRoleStage
#print axioms ConstitutiveSearch.NPAndOrP.buildConstitutiveRoleHistory
#print axioms ConstitutiveSearch.NPAndOrP.roleStage_relation_is_discovered
#print axioms ConstitutiveSearch.NPAndOrP.roleStage_complete_operation_is_next
/- AXIOM_AUDIT_END -/
