import ConstitutiveSearch.SAT.AcceptedBinaryBranch

namespace ConstitutiveSearch.Tests.SATAcceptedBinaryBranchRegression

open ConstitutiveSearch
open SAT

abbrev clause : Clause :=
  [Literal.positive 0]

abbrev formula : Cnf :=
  [clause]

def allTrue : Assignment :=
  fun _ => true

def allFalse : Assignment :=
  fun _ => false

theorem allTrue_accept :
    Satisfies allTrue formula :=
  .cons rfl .nil

def splitter :=
  structuralVariableBranchSplit formula 0

/--
A rejected assignment is still split structurally into the false child.
-/
def rejectedChild :
    structuralVariableBranchSystem.Continuation
      (.fixedFalse formula 0) :=
  ⟨allFalse, rfl⟩

theorem rejectedChild_not_accepted :
    structuralVariableBranchSystem.Accept
        (.fixedFalse formula 0)
        rejectedChild →
      False := by
  intro accepted
  cases accepted with
  | cons headSatisfied _tailSatisfied =>
      cases headSatisfied

theorem parent_viable :
    structuralVariableBranchSystem.Viable
      (.parent formula 0) :=
  ⟨allTrue, allTrue_accept⟩

theorem parent_viable_iff :
    structuralVariableBranchSystem.Viable
        (.parent formula 0) ↔
      structuralVariableBranchSystem.Viable
          (.fixedFalse formula 0) ∨
        structuralVariableBranchSystem.Viable
          (.fixedTrue formula 0) :=
  structural_branch_viable_iff formula 0

def expansion :
    AcceptedFrontierPreservation
      structuralVariableBranchSystem
      [.parent formula 0]
      [.fixedFalse formula 0, .fixedTrue formula 0] :=
  AcceptedFrontierPreservation.expandHead splitter

theorem expansion_viable_iff :
    FrontierViable
        structuralVariableBranchSystem
        [.parent formula 0] ↔
      FrontierViable
        structuralVariableBranchSystem
        [.fixedFalse formula 0, .fixedTrue formula 0] :=
  expansion.viable_iff

def parentAccepted :
    structuralVariableBranchSystem.frontierSystem.AcceptedContinuation
      [.parent formula 0] :=
  ⟨.head allTrue, allTrue_accept⟩

/-- The accepted parent assignment is routed to the true branch. -/
def expandedAccepted :
    structuralVariableBranchSystem.frontierSystem.AcceptedContinuation
      [.fixedFalse formula 0, .fixedTrue formula 0] :=
  expansion.forward.toAcceptedTransport.map parentAccepted

end ConstitutiveSearch.Tests.SATAcceptedBinaryBranchRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATAcceptedBinaryBranchRegression.allTrue_accept
#print axioms ConstitutiveSearch.Tests.SATAcceptedBinaryBranchRegression.splitter
#print axioms ConstitutiveSearch.Tests.SATAcceptedBinaryBranchRegression.rejectedChild
#print axioms ConstitutiveSearch.Tests.SATAcceptedBinaryBranchRegression.rejectedChild_not_accepted
#print axioms ConstitutiveSearch.Tests.SATAcceptedBinaryBranchRegression.parent_viable
#print axioms ConstitutiveSearch.Tests.SATAcceptedBinaryBranchRegression.parent_viable_iff
#print axioms ConstitutiveSearch.Tests.SATAcceptedBinaryBranchRegression.expansion
#print axioms ConstitutiveSearch.Tests.SATAcceptedBinaryBranchRegression.expansion_viable_iff
#print axioms ConstitutiveSearch.Tests.SATAcceptedBinaryBranchRegression.expandedAccepted
/- AXIOM_AUDIT_END -/
