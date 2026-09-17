import ConstitutiveSearch.SAT.ResidualFlipTransport

namespace ConstitutiveSearch.Tests.SATResidualFlipTransportRegression

open SAT

abbrev leftClause : Clause :=
  [Literal.positive 0, Literal.positive 1]

abbrev rightClause : Clause :=
  [Literal.negative 0, Literal.positive 1]

abbrev symmetricFormula : Cnf :=
  [leftClause, rightClause]

/-- False and true branches retain opposite residual clauses. -/
theorem falseResidual_exact :
    branchResidual symmetricFormula 0 false = [leftClause] := by
  rfl

theorem trueResidual_exact :
    branchResidual symmetricFormula 0 true = [rightClause] := by
  rfl

/-- Flipping variable zero carries the false residual syntax to the true residual. -/
theorem residualFlip_exact :
    branchResidual symmetricFormula 0 true =
      Cnf.flipAt 0 (branchResidual symmetricFormula 0 false) := by
  rfl

/-- Concrete structural relation between the two branches. -/
def falseToTrueRelation :
    ResidualFlipRelation symmetricFormula 0 false true :=
  { targetIsOpposite := rfl
    residualIsFlip := residualFlip_exact }

/-- The executable relation search finds the same structural transport. -/
theorem falseToTrue_search_found :
    (residualFlipSearch symmetricFormula 0).find false true ≠ none := by
  intro impossible
  change some _ = none at impossible
  cases impossible

/-- The two residual branches reduce to one representative, so width is one. -/
def reducedResiduals :=
  reduceResidualBranches symmetricFormula 0

theorem residual_width_one :
    reducedResiduals.width = 1 := by
  rfl

/-- A concrete false-branch residual completion. -/
def falseAssignment : Assignment
  | 0 => false
  | _ + 1 => true

def falseResidualCompletion :
    ResidualBranchCompletion symmetricFormula 0 false :=
  { assignment := falseAssignment
    valueExact := rfl
    residualSatisfaction := .cons rfl .nil }

/-- The structural flip transports that completion to the true branch. -/
def trueResidualCompletion :
    ResidualBranchCompletion symmetricFormula 0 true :=
  falseToTrueRelation.mapCompletion falseResidualCompletion

example : trueResidualCompletion.assignment 0 = true :=
  trueResidualCompletion.valueExact

example :
    Satisfies trueResidualCompletion.assignment
      (branchResidual symmetricFormula 0 true) :=
  trueResidualCompletion.residualSatisfaction

/-- The frontier reduction transports an actual false-side completion to the retained side. -/
def sourceFrontierCompletion :
    FrontierCompletion
      (ResidualCompletionFamily symmetricFormula 0)
      [false, true] :=
  .head falseResidualCompletion

def retainedFrontierCompletion :
    FrontierCompletion
      (ResidualCompletionFamily symmetricFormula 0)
      reducedResiduals.retained :=
  reducedResiduals.transport.map sourceFrontierCompletion

example :
    Nonempty
      (FrontierCompletion
        (ResidualCompletionFamily symmetricFormula 0)
        reducedResiduals.retained) :=
  ⟨retainedFrontierCompletion⟩

end ConstitutiveSearch.Tests.SATResidualFlipTransportRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATResidualFlipTransportRegression.falseResidual_exact
#print axioms ConstitutiveSearch.Tests.SATResidualFlipTransportRegression.trueResidual_exact
#print axioms ConstitutiveSearch.Tests.SATResidualFlipTransportRegression.residualFlip_exact
#print axioms ConstitutiveSearch.Tests.SATResidualFlipTransportRegression.falseToTrueRelation
#print axioms ConstitutiveSearch.Tests.SATResidualFlipTransportRegression.falseToTrue_search_found
#print axioms ConstitutiveSearch.Tests.SATResidualFlipTransportRegression.reducedResiduals
#print axioms ConstitutiveSearch.Tests.SATResidualFlipTransportRegression.residual_width_one
#print axioms ConstitutiveSearch.Tests.SATResidualFlipTransportRegression.falseResidualCompletion
#print axioms ConstitutiveSearch.Tests.SATResidualFlipTransportRegression.trueResidualCompletion
#print axioms ConstitutiveSearch.Tests.SATResidualFlipTransportRegression.retainedFrontierCompletion
/- AXIOM_AUDIT_END -/