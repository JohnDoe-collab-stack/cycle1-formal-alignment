import ConstitutiveSearch.SAT.ConstraintTransport

namespace ConstitutiveSearch.Tests.SATConstraintTransportRegression

open SAT

abbrev clauseA : Clause :=
  [Literal.positive 0]

abbrev clauseB : Clause :=
  [Literal.positive 1]

abbrev strongFormula : Cnf :=
  [clauseA, clauseB]

abbrev weakFormula : Cnf :=
  [clauseA]

/-- The structural weakening search finds that the weak formula is a sub-CNF of the strong one. -/
theorem forwardWeakeningFound :
    CnfWeakening.find strongFormula weakFormula ≠ none := by
  intro impossible
  cases impossible

/-- The reverse search does not manufacture a clause that is absent from the source. -/
theorem reverseWeakeningNotFound :
    CnfWeakening.find weakFormula strongFormula = none := by
  rfl

/-- The generic pair reducer therefore keeps only the weaker CNF. -/
def reducedPair :=
  reducePair weakeningSearch weakeningAction strongFormula weakFormula

example : reducedPair.retained = [weakFormula] := rfl

example : reducedPair.width = 1 := rfl

/-- A concrete source completion is transported without any satisfiability query. -/
def allTrue : Assignment :=
  fun _ => true

def strongCompletion : Completion strongFormula :=
  ⟨allTrue,
    .cons rfl (.cons rfl .nil)⟩

def sourceFrontierCompletion :
    FrontierCompletion Completion [strongFormula, weakFormula] :=
  .head strongCompletion

/-- The retained frontier receives a completion constructively from the source one. -/
def retainedCompletion :
    FrontierCompletion Completion reducedPair.retained :=
  reducedPair.transport.map sourceFrontierCompletion

example : Nonempty (FrontierCompletion Completion reducedPair.retained) :=
  ⟨retainedCompletion⟩

end ConstitutiveSearch.Tests.SATConstraintTransportRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATConstraintTransportRegression.forwardWeakeningFound
#print axioms ConstitutiveSearch.Tests.SATConstraintTransportRegression.reverseWeakeningNotFound
#print axioms ConstitutiveSearch.Tests.SATConstraintTransportRegression.reducedPair
#print axioms ConstitutiveSearch.Tests.SATConstraintTransportRegression.strongCompletion
#print axioms ConstitutiveSearch.Tests.SATConstraintTransportRegression.retainedCompletion
/- AXIOM_AUDIT_END -/