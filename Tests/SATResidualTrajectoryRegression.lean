import ConstitutiveSearch.SAT.ResidualTrajectory

namespace ConstitutiveSearch.Tests.SATResidualTrajectoryRegression

open SAT

abbrev clause0 : Clause := [Literal.positive 0]
abbrev clause1 : Clause := [Literal.positive 1]
abbrev clause2 : Clause := [Literal.positive 2]

abbrev baseFormula : Cnf := [clause0, clause1, clause2]

abbrev afterFirst : Cnf :=
  firstResidual baseFormula 0 true

abbrev afterSecond : Cnf :=
  secondResidual baseFormula 0 true 1 true

/-- The two residuals are produced purely by branch syntax. -/
theorem afterFirst_exact :
    afterFirst = [clause1, clause2] := by
  rfl

theorem afterSecond_exact :
    afterSecond = [clause2] := by
  rfl

/-- The concrete three-state trajectory is exactly source → residual → residual. -/
theorem trajectory_exact :
    twoStepResidualTrajectory baseFormula 0 true 1 true =
      [baseFormula, afterFirst, afterSecond] := by
  rfl

/-- Each edge has an explicit constructive weakening witness. -/
def firstWitness : CnfWeakening baseFormula afterFirst :=
  firstResidualWeakening baseFormula 0 true

def secondWitness : CnfWeakening afterFirst afterSecond :=
  secondResidualWeakening baseFormula 0 true 1 true

/-- The full trajectory normalizes to its final residual. -/
def reducedTrajectory :=
  reduceTwoStepResidualTrajectory baseFormula 0 true 1 true

theorem reducedTrajectory_retained :
    reducedTrajectory.retained = [afterSecond] := by
  rfl

theorem reducedTrajectory_width :
    reducedTrajectory.width = 1 := by
  rfl

/-- A concrete source completion is transported through the normalized frontier. -/
def allTrue : Assignment := fun _ => true

def baseCompletion : Completion baseFormula :=
  ⟨allTrue,
    .cons rfl (.cons rfl (.cons rfl .nil))⟩

def sourceFrontierCompletion :
    FrontierCompletion Completion
      (twoStepResidualTrajectory baseFormula 0 true 1 true) :=
  .head baseCompletion

def retainedFrontierCompletion :
    FrontierCompletion Completion reducedTrajectory.retained :=
  reducedTrajectory.transport.map sourceFrontierCompletion

example :
    Nonempty (FrontierCompletion Completion reducedTrajectory.retained) :=
  ⟨retainedFrontierCompletion⟩

end ConstitutiveSearch.Tests.SATResidualTrajectoryRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATResidualTrajectoryRegression.afterFirst_exact
#print axioms ConstitutiveSearch.Tests.SATResidualTrajectoryRegression.afterSecond_exact
#print axioms ConstitutiveSearch.Tests.SATResidualTrajectoryRegression.trajectory_exact
#print axioms ConstitutiveSearch.Tests.SATResidualTrajectoryRegression.firstWitness
#print axioms ConstitutiveSearch.Tests.SATResidualTrajectoryRegression.secondWitness
#print axioms ConstitutiveSearch.Tests.SATResidualTrajectoryRegression.reducedTrajectory
#print axioms ConstitutiveSearch.Tests.SATResidualTrajectoryRegression.reducedTrajectory_retained
#print axioms ConstitutiveSearch.Tests.SATResidualTrajectoryRegression.reducedTrajectory_width
#print axioms ConstitutiveSearch.Tests.SATResidualTrajectoryRegression.baseCompletion
#print axioms ConstitutiveSearch.Tests.SATResidualTrajectoryRegression.retainedFrontierCompletion
/- AXIOM_AUDIT_END -/
