import ConstitutiveSearch.AcceptedFrontierPreservation

namespace ConstitutiveSearch.Tests.AcceptedFrontierRegression

open ConstitutiveSearch

def StateContinuation (_state : Bool) : Type :=
  Unit

def StateAccept
    (_state : Bool)
    (_continuation : Unit) : Prop :=
  True

def system : SearchSystem :=
  { State := Bool
    Continuation := StateContinuation
    Accept := StateAccept }

def falseToTrue :
    AcceptingContinuationTransport system false true :=
  { map := fun _ => ()
    preservesAccept := by
      intro _continuation _accepted
      exact True.intro }

def absorbed :
    AcceptedFrontierPreservation
      system
      [false, true]
      [true] :=
  AcceptedFrontierPreservation.absorbFirstIntoSecond
    falseToTrue

/-- The source frontier is viable through its first state. -/
theorem source_viable :
    FrontierViable system [false, true] := by
  exact ⟨.head (), True.intro⟩

/-- The retained frontier is viable. -/
theorem retained_viable :
    FrontierViable system [true] := by
  exact ⟨.head (), True.intro⟩

/-- Absorption preserves viability in both directions. -/
theorem absorption_viable_iff :
    FrontierViable system [false, true] ↔
      FrontierViable system [true] :=
  absorbed.viable_iff

/-- One accepted source continuation transported to the retained frontier. -/
def sourceAccepted :
    system.frontierSystem.AcceptedContinuation [false, true] :=
  ⟨.head (), True.intro⟩

def retainedAccepted :
    system.frontierSystem.AcceptedContinuation [true] :=
  absorbed.forward.toAcceptedTransport.map sourceAccepted

/-- The retained witness can be embedded back into the source frontier. -/
def restoredAccepted :
    system.frontierSystem.AcceptedContinuation [false, true] :=
  absorbed.backward.toAcceptedTransport.map retainedAccepted

end ConstitutiveSearch.Tests.AcceptedFrontierRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.AcceptedFrontierRegression.falseToTrue
#print axioms ConstitutiveSearch.Tests.AcceptedFrontierRegression.absorbed
#print axioms ConstitutiveSearch.Tests.AcceptedFrontierRegression.source_viable
#print axioms ConstitutiveSearch.Tests.AcceptedFrontierRegression.retained_viable
#print axioms ConstitutiveSearch.Tests.AcceptedFrontierRegression.absorption_viable_iff
#print axioms ConstitutiveSearch.Tests.AcceptedFrontierRegression.retainedAccepted
#print axioms ConstitutiveSearch.Tests.AcceptedFrontierRegression.restoredAccepted
/- AXIOM_AUDIT_END -/
