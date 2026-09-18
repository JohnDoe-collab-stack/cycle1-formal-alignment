import ConstitutiveSearch.ConstitutiveState

/-!
# Proof-relevant frontier trajectories

A trajectory is not merely a trace recorded after computation.  It is an
inductive composition of constitutive steps.  Each step carries both the
frontier viability preservation and the proof-relevant change in constituted
information.

The resulting trajectory therefore witnesses, constructively, that the final
frontier has the same viability status as the initial frontier.
-/

namespace ConstitutiveSearch

universe uConstitution uStep

/-- Finite constitutive computation between two search states. -/
inductive FrontierTrajectory
    (system : SearchSystem)
    {Constitution : Type uConstitution}
    (Constitutes : Constitution → Constitution → Type uStep) :
    ConstitutiveState system Constitution →
      ConstitutiveState system Constitution →
        Type _ where
  | refl
      (state : ConstitutiveState system Constitution) :
      FrontierTrajectory system Constitutes state state
  | snoc
      {start current next : ConstitutiveState system Constitution}
      (previous :
        FrontierTrajectory system Constitutes start current)
      (step :
        ConstitutiveStep system Constitutes current next) :
      FrontierTrajectory system Constitutes start next

namespace FrontierTrajectory

/-- Compose all frontier preservation witnesses carried by a trajectory. -/
def preservation
    {system : SearchSystem}
    {Constitution : Type uConstitution}
    {Constitutes : Constitution → Constitution → Type uStep}
    {start finish : ConstitutiveState system Constitution}
    (trajectory :
      FrontierTrajectory system Constitutes start finish) :
    AcceptedFrontierPreservation
      system
      start.frontier
      finish.frontier :=
  match trajectory with
  | .refl =>
      AcceptedFrontierPreservation.identity
        system
        start.frontier
  | .snoc previous step =>
      (preservation previous).trans
        step.preservation

/-- Initial and final frontiers of a trajectory are viability-equivalent. -/
theorem viable_iff
    {system : SearchSystem}
    {Constitution : Type uConstitution}
    {Constitutes : Constitution → Constitution → Type uStep}
    {start finish : ConstitutiveState system Constitution}
    (trajectory :
      FrontierTrajectory system Constitutes start finish) :
    FrontierViable system start.frontier ↔
      FrontierViable system finish.frontier :=
  trajectory.preservation.viable_iff

/-- Number of constitutive transitions in a trajectory. -/
def length
    {system : SearchSystem}
    {Constitution : Type uConstitution}
    {Constitutes : Constitution → Constitution → Type uStep}
    {start finish : ConstitutiveState system Constitution} :
    FrontierTrajectory system Constitutes start finish → Nat
  | .refl _ => 0
  | .snoc previous _ => previous.length + 1

/-- Widths of all frontiers visited by a trajectory, including both endpoints. -/
def widthTrace
    {system : SearchSystem}
    {Constitution : Type uConstitution}
    {Constitutes : Constitution → Constitution → Type uStep}
    {start finish : ConstitutiveState system Constitution}
    (trajectory :
      FrontierTrajectory system Constitutes start finish) :
    List Nat :=
  match trajectory with
  | .refl =>
      [start.frontier.length]
  | .snoc previous _step =>
      widthTrace previous ++
        [finish.frontier.length]

/-- Maximum frontier width observed along the concrete trajectory. -/
def maxWidth
    {system : SearchSystem}
    {Constitution : Type uConstitution}
    {Constitutes : Constitution → Constitution → Type uStep}
    {start finish : ConstitutiveState system Constitution}
    (trajectory :
      FrontierTrajectory system Constitutes start finish) : Nat :=
  trajectory.widthTrace.foldl Nat.max 0

/-- Append one constitutive step to a completed trajectory. -/
def appendStep
    {system : SearchSystem}
    {Constitution : Type uConstitution}
    {Constitutes : Constitution → Constitution → Type uStep}
    {start current next : ConstitutiveState system Constitution}
    (trajectory :
      FrontierTrajectory system Constitutes start current)
    (step :
      ConstitutiveStep system Constitutes current next) :
    FrontierTrajectory system Constitutes start next :=
  .snoc trajectory step

end FrontierTrajectory

end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.FrontierTrajectory
#print axioms ConstitutiveSearch.FrontierTrajectory.preservation
#print axioms ConstitutiveSearch.FrontierTrajectory.viable_iff
#print axioms ConstitutiveSearch.FrontierTrajectory.length
#print axioms ConstitutiveSearch.FrontierTrajectory.widthTrace
#print axioms ConstitutiveSearch.FrontierTrajectory.maxWidth
#print axioms ConstitutiveSearch.FrontierTrajectory.appendStep
/- AXIOM_AUDIT_END -/
