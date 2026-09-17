import ConstitutiveSearch.SAT.BranchContextTransport

namespace ConstitutiveSearch.Tests.SATBranchContextTransportRegression

open SAT

abbrev c0p : Clause :=
  [Literal.positive 0, Literal.positive 2]

abbrev c0n : Clause :=
  [Literal.negative 0, Literal.positive 2]

abbrev c1p : Clause :=
  [Literal.positive 1, Literal.positive 2]

abbrev c1n : Clause :=
  [Literal.negative 1, Literal.positive 2]

abbrev branchingFormula : Cnf :=
  [c0p, c0n, c1p, c1n]

abbrev root : BranchContext :=
  rootContext branchingFormula

abbrev rootReconstruction : BranchContextReconstruction root :=
  rootContextReconstruction branchingFormula

abbrev firstTrue : BranchContext :=
  childContext root 0 true

abbrev firstTrueReconstruction : BranchContextReconstruction firstTrue :=
  childContextReconstruction rootReconstruction 0 true

abbrev secondFalse : BranchContext :=
  childContext firstTrue 1 false

abbrev secondTrue : BranchContext :=
  childContext firstTrue 1 true

/-- The second split variable is fresh relative to the first decision. -/
theorem secondVariable_fresh :
    DecisionsAvoid 1 firstTrue.decisions := by
  constructor
  · decide
  · exact True.intro

/-- The two second-level residuals are related by the existing polarity flip. -/
theorem secondResidualFlip_exact :
    branchResidual firstTrue.formula 1 true =
      Cnf.flipAt 1 (branchResidual firstTrue.formula 1 false) := by
  rfl

/-- Structural relation between the two actual second-level branch contexts. -/
def secondFalseToTrueRelation :
    ContextFlipRelation firstTrue 1 false true :=
  { residual :=
      { targetIsOpposite := rfl
        residualIsFlip := secondResidualFlip_exact }
    fresh := secondVariable_fresh }

/-- Concrete source assignment with first decision true and second decision false. -/
def sourceAssignment : Assignment
  | 0 => true
  | 1 => false
  | _ => true

/-- The assignment satisfies the original formula. -/
def rootCompletion : root.Carrier :=
  ⟨sourceAssignment,
    .cons rfl
      (.cons rfl
        (.cons rfl
          (.cons rfl .nil)))⟩

/-- Reify the first true decision from the root completion. -/
def firstTrueCompletion : firstTrue.Carrier :=
  { underlying := rootCompletion
    valueExact := rfl }

/-- Reify the second false decision. -/
def secondFalseCompletion : secondFalse.Carrier :=
  { underlying := firstTrueCompletion
    valueExact := rfl }

/-- Lift the residual flip to an actual completion of the opposite child context. -/
def secondTrueCompletion : secondTrue.Carrier :=
  secondFalseToTrueRelation.mapCompletion
    firstTrueReconstruction
    secondFalseCompletion

/-- The transported completion realizes the flipped second decision. -/
theorem transported_secondDecision_true :
    secondTrue.assignment secondTrueCompletion 1 = true :=
  childContext_newDecisionExact
    firstTrue 1 true secondTrueCompletion

/-- The already constituted first decision survives the transport. -/
theorem transported_firstDecision_preserved :
    secondTrue.assignment secondTrueCompletion 0 = true := by
  exact
    (childContext_parentDecisionsExact
      firstTrue 1 true secondTrueCompletion).1

/-- The complete target decision history remains exact. -/
theorem transported_history_exact :
    DecisionsHold
      (secondTrue.assignment secondTrueCompletion)
      secondTrue.decisions :=
  secondTrue.decisionsExact secondTrueCompletion

/-- The parent carrier reconstructed under the target child still satisfies its formula. -/
theorem transported_parent_satisfies :
    Satisfies
      (firstTrue.assignment secondTrueCompletion.underlying)
      firstTrue.formula :=
  firstTrue.satisfaction secondTrueCompletion.underlying

/-- Executable context search finds the same second-level structural relation. -/
theorem secondContext_search_found :
    (contextFlipSearch firstTrue 1).find false true ≠ none := by
  intro impossible
  change some _ = none at impossible
  cases impossible

/-- The actual second-level branch-context frontier reduces to one representative. -/
def reducedSecondContexts :=
  reduceContextBranches
    firstTrue firstTrueReconstruction 1

/-- Width is now derived at the level of provenance-carrying branch contexts. -/
theorem secondContext_width_one :
    reducedSecondContexts.width = 1 := by
  rfl

/-- A concrete source frontier completion is transported through that reduction. -/
def sourceFrontierCompletion :
    FrontierCompletion
      (ChildContextCompletionFamily firstTrue 1)
      [false, true] :=
  .head secondFalseCompletion

/-- The retained frontier receives a genuine transported branch completion. -/
def retainedFrontierCompletion :
    FrontierCompletion
      (ChildContextCompletionFamily firstTrue 1)
      reducedSecondContexts.retained :=
  reducedSecondContexts.transport.map sourceFrontierCompletion

example :
    Nonempty
      (FrontierCompletion
        (ChildContextCompletionFamily firstTrue 1)
        reducedSecondContexts.retained) :=
  ⟨retainedFrontierCompletion⟩

end ConstitutiveSearch.Tests.SATBranchContextTransportRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATBranchContextTransportRegression.secondVariable_fresh
#print axioms ConstitutiveSearch.Tests.SATBranchContextTransportRegression.secondResidualFlip_exact
#print axioms ConstitutiveSearch.Tests.SATBranchContextTransportRegression.secondFalseToTrueRelation
#print axioms ConstitutiveSearch.Tests.SATBranchContextTransportRegression.rootCompletion
#print axioms ConstitutiveSearch.Tests.SATBranchContextTransportRegression.secondFalseCompletion
#print axioms ConstitutiveSearch.Tests.SATBranchContextTransportRegression.secondTrueCompletion
#print axioms ConstitutiveSearch.Tests.SATBranchContextTransportRegression.transported_secondDecision_true
#print axioms ConstitutiveSearch.Tests.SATBranchContextTransportRegression.transported_firstDecision_preserved
#print axioms ConstitutiveSearch.Tests.SATBranchContextTransportRegression.transported_history_exact
#print axioms ConstitutiveSearch.Tests.SATBranchContextTransportRegression.transported_parent_satisfies
#print axioms ConstitutiveSearch.Tests.SATBranchContextTransportRegression.secondContext_search_found
#print axioms ConstitutiveSearch.Tests.SATBranchContextTransportRegression.reducedSecondContexts
#print axioms ConstitutiveSearch.Tests.SATBranchContextTransportRegression.secondContext_width_one
#print axioms ConstitutiveSearch.Tests.SATBranchContextTransportRegression.retainedFrontierCompletion
/- AXIOM_AUDIT_END -/
