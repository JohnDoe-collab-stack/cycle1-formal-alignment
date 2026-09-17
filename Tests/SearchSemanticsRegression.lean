import ConstitutiveSearch.AcceptingTransport

namespace ConstitutiveSearch.Tests.SearchSemanticsRegression

open ConstitutiveSearch

/-!
The first separator shows that a raw total map between continuation spaces does
not by itself justify branch absorption: acceptance preservation is an
independent obligation.
-/

inductive RawState where
  | source
  | target

def rawContinuation (_state : RawState) : Type :=
  Unit

def rawAccept
    (state : RawState)
    (_continuation : rawContinuation state) : Prop :=
  match state with
  | .source => True
  | .target => False

def rawSystem : SearchSystem :=
  { State := RawState
    Continuation := rawContinuation
    Accept := rawAccept }

/-- A raw structural continuation map exists. -/
def rawMap :
    rawSystem.Continuation RawState.source →
      rawSystem.Continuation RawState.target :=
  fun _ => ()

/-- The source is viable. -/
theorem raw_source_viable :
    rawSystem.Viable RawState.source :=
  ⟨(), True.intro⟩

/-- The target is not viable. -/
theorem raw_target_not_viable :
    ¬ rawSystem.Viable RawState.target := by
  intro viable
  rcases viable with ⟨_continuation, impossible⟩
  exact impossible

/--
Despite the raw map, no acceptance-preserving source-to-target transport can
exist.
-/
theorem raw_map_not_accepting :
    AcceptingContinuationTransport
      rawSystem RawState.source RawState.target →
      False := by
  intro transport
  exact transport.preservesAccept () True.intro

/-!
The second separator targets the old accepted-witness-only interface directly.
Both accepted-witness spaces are empty, so a vacuous ContinuationTransport
between them exists.  But the structural source continuation space is inhabited
while the structural target continuation space is empty, so no total structural
transport can exist.
-/

inductive VacuousState where
  | source
  | target

def vacuousContinuation : VacuousState → Type
  | .source => Unit
  | .target => Empty

def vacuousAccept
    (state : VacuousState)
    (_continuation : vacuousContinuation state) : Prop :=
  False

def vacuousSystem : SearchSystem :=
  { State := VacuousState
    Continuation := vacuousContinuation
    Accept := vacuousAccept }

/--
The accepted-only interface admits a vacuous transport because the source has
no accepted continuation.
-/
def acceptedOnlyTransport :
    ContinuationTransport
      vacuousSystem.AcceptedContinuation
      VacuousState.source
      VacuousState.target :=
  { map := fun accepted =>
      False.elim accepted.2 }

/--
No total structural transport exists from the inhabited source continuation
space to the empty target continuation space.
-/
theorem no_structural_accepting_transport :
    AcceptingContinuationTransport
      vacuousSystem VacuousState.source VacuousState.target →
      False := by
  intro transport
  exact Empty.elim (transport.map ())

end ConstitutiveSearch.Tests.SearchSemanticsRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SearchSemanticsRegression.rawMap
#print axioms ConstitutiveSearch.Tests.SearchSemanticsRegression.raw_source_viable
#print axioms ConstitutiveSearch.Tests.SearchSemanticsRegression.raw_target_not_viable
#print axioms ConstitutiveSearch.Tests.SearchSemanticsRegression.raw_map_not_accepting
#print axioms ConstitutiveSearch.Tests.SearchSemanticsRegression.acceptedOnlyTransport
#print axioms ConstitutiveSearch.Tests.SearchSemanticsRegression.no_structural_accepting_transport
/- AXIOM_AUDIT_END -/
