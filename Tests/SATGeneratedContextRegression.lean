import ConstitutiveSearch.SAT.GeneratedContext

namespace ConstitutiveSearch.Tests.SATGeneratedContextRegression

open SAT

abbrev c0p : Clause :=
  [Literal.positive 0, Literal.positive 2]

abbrev c0n : Clause :=
  [Literal.negative 0, Literal.positive 2]

abbrev c1p : Clause :=
  [Literal.positive 1, Literal.positive 2]

abbrev c1n : Clause :=
  [Literal.negative 1, Literal.positive 2]

abbrev formula : Cnf :=
  [c0p, c0n, c1p, c1n]

abbrev root : GeneratedBranchContext formula :=
  GeneratedBranchContext.root formula

/-- Every variable is fresh at the generated root. -/
theorem rootVar0Fresh : DecisionsAvoid 0 root.context.decisions :=
  True.intro

abbrev firstFalse : GeneratedBranchContext formula :=
  GeneratedBranchContext.child root 0 false rootVar0Fresh

abbrev firstTrue : GeneratedBranchContext formula :=
  GeneratedBranchContext.child root 0 true rootVar0Fresh

/-- Variable one is fresh after deciding variable zero. -/
theorem firstTrueVar1Fresh : DecisionsAvoid 1 firstTrue.context.decisions := by
  constructor
  · decide
  · exact True.intro

abbrev secondFalse : GeneratedBranchContext formula :=
  GeneratedBranchContext.child firstTrue 1 false firstTrueVar1Fresh

abbrev secondTrue : GeneratedBranchContext formula :=
  GeneratedBranchContext.child firstTrue 1 true firstTrueVar1Fresh

/-- Generation depth is derived from the parent chain. -/
theorem secondTrue_depth_two :
    secondTrue.depth = 2 := by
  rfl

/-- The recursively constituted decision history remains explicit. -/
theorem secondTrue_decisions_exact :
    secondTrue.context.decisions =
      [ { var := 1, value := true },
        { var := 0, value := true } ] := by
  rfl

/-- States from different parents inhabit one uniform generated-state frontier. -/
def heterogeneousFrontier : List (GeneratedBranchContext formula) :=
  [firstFalse, secondFalse, secondTrue]

/-- One concrete satisfying root assignment. -/
def allTrue : Assignment :=
  fun _var => true

def rootCompletion : GeneratedBranchCompletion root :=
  ⟨allTrue,
    .cons rfl
      (.cons rfl
        (.cons rfl
          (.cons rfl .nil)))⟩

/-- Exact split in the generated-state type. -/
def firstSplit :=
  generatedSplit root 0 rootVar0Fresh

/-- The concrete root completion takes the true child. -/
def firstTrueCompletion : GeneratedBranchCompletion firstTrue :=
  { underlying := rootCompletion
    valueExact := rfl }

/-- A second true decision gives a completion of a deeper generated state. -/
def secondTrueCompletion : GeneratedBranchCompletion secondTrue :=
  { underlying := firstTrueCompletion
    valueExact := rfl }

/-- The generated split round-trips through the original root completion. -/
theorem firstSplit_roundTrip :
    firstSplit.merge (firstSplit.split rootCompletion) = rootCompletion :=
  firstSplit.mergeSplit rootCompletion

/-- Exact expansion now has preservation in both directions at generated-state level. -/
def firstExpansion :=
  generatedExpansion root 0 rootVar0Fresh

theorem firstExpansion_nonempty_iff :
    Nonempty (FrontierCompletion GeneratedBranchCompletion [root]) ↔
      Nonempty
        (FrontierCompletion GeneratedBranchCompletion [firstFalse, firstTrue]) :=
  firstExpansion.nonempty_iff

/-- A heterogeneous frontier can carry a completion from a deeper parent chain. -/
def heterogeneousCompletion :
    FrontierCompletion GeneratedBranchCompletion heterogeneousFrontier :=
  .tail (.tail (.head secondTrueCompletion))

example : Nonempty (FrontierCompletion GeneratedBranchCompletion heterogeneousFrontier) :=
  ⟨heterogeneousCompletion⟩

/-- Reconstruction is not supplied arbitrarily. It is derived from provenance. -/
def secondTrueReconstruction :
    BranchContextReconstruction secondTrue.context :=
  secondTrue.reconstruction

end ConstitutiveSearch.Tests.SATGeneratedContextRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATGeneratedContextRegression.rootVar0Fresh
#print axioms ConstitutiveSearch.Tests.SATGeneratedContextRegression.firstTrueVar1Fresh
#print axioms ConstitutiveSearch.Tests.SATGeneratedContextRegression.secondTrue_depth_two
#print axioms ConstitutiveSearch.Tests.SATGeneratedContextRegression.secondTrue_decisions_exact
#print axioms ConstitutiveSearch.Tests.SATGeneratedContextRegression.heterogeneousFrontier
#print axioms ConstitutiveSearch.Tests.SATGeneratedContextRegression.rootCompletion
#print axioms ConstitutiveSearch.Tests.SATGeneratedContextRegression.firstSplit_roundTrip
#print axioms ConstitutiveSearch.Tests.SATGeneratedContextRegression.firstExpansion
#print axioms ConstitutiveSearch.Tests.SATGeneratedContextRegression.firstExpansion_nonempty_iff
#print axioms ConstitutiveSearch.Tests.SATGeneratedContextRegression.heterogeneousCompletion
#print axioms ConstitutiveSearch.Tests.SATGeneratedContextRegression.secondTrueReconstruction
/- AXIOM_AUDIT_END -/
