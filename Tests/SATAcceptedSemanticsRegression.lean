import ConstitutiveSearch.SAT.AcceptedSAT

namespace ConstitutiveSearch.Tests.SATAcceptedSemanticsRegression

open ConstitutiveSearch
open SAT

abbrev c0 : Clause :=
  [Literal.positive 0]

abbrev c1 : Clause :=
  [Literal.positive 1]

abbrev strong : Cnf :=
  [c0, c1]

abbrev weak : Cnf :=
  [c0]

def weakening :
    CnfWeakening strong weak :=
  .keep c0
    (.drop c1 .done)

def allTrue : Assignment :=
  fun _ => true

def allFalse : Assignment :=
  fun _ => false

theorem allTrue_strong :
    Satisfies allTrue strong :=
  .cons rfl
    (.cons rfl .nil)

/-- A rejected assignment is still a structural continuation of the source. -/
theorem allFalse_not_accepted :
    satSystem.Accept strong allFalse →
      False := by
  intro accepted
  cases accepted with
  | cons headSatisfied _tailSatisfied =>
      cases headSatisfied

def transport :
    AcceptingContinuationTransport satSystem strong weak :=
  weakening.toAcceptingTransport

/-- Accepted source assignment remains accepted after weakening. -/
theorem transported_accept :
    satSystem.Accept weak
      (transport.map allTrue) :=
  transport.preservesAccept
    allTrue
    allTrue_strong

/--
The rejected source assignment is nevertheless mapped because the structural
map is total on assignments.
-/
def mappedRejected :
    satSystem.Continuation weak :=
  transport.map allFalse

theorem mappedRejected_exact :
    mappedRejected = allFalse :=
  rfl

def absorbed :
    AcceptedFrontierPreservation
      satSystem
      [strong, weak]
      [weak] :=
  absorbByWeakening weakening

theorem strong_viable :
    satSystem.Viable strong :=
  ⟨allTrue, allTrue_strong⟩

/-- Frontier viability is preserved by structural weakening absorption. -/
theorem weakening_absorption_viable_iff :
    FrontierViable satSystem [strong, weak] ↔
      FrontierViable satSystem [weak] :=
  absorbed.viable_iff

end ConstitutiveSearch.Tests.SATAcceptedSemanticsRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATAcceptedSemanticsRegression.weakening
#print axioms ConstitutiveSearch.Tests.SATAcceptedSemanticsRegression.allTrue_strong
#print axioms ConstitutiveSearch.Tests.SATAcceptedSemanticsRegression.allFalse_not_accepted
#print axioms ConstitutiveSearch.Tests.SATAcceptedSemanticsRegression.transport
#print axioms ConstitutiveSearch.Tests.SATAcceptedSemanticsRegression.transported_accept
#print axioms ConstitutiveSearch.Tests.SATAcceptedSemanticsRegression.mappedRejected
#print axioms ConstitutiveSearch.Tests.SATAcceptedSemanticsRegression.mappedRejected_exact
#print axioms ConstitutiveSearch.Tests.SATAcceptedSemanticsRegression.absorbed
#print axioms ConstitutiveSearch.Tests.SATAcceptedSemanticsRegression.strong_viable
#print axioms ConstitutiveSearch.Tests.SATAcceptedSemanticsRegression.weakening_absorption_viable_iff
/- AXIOM_AUDIT_END -/
