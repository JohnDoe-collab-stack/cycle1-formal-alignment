import ConstitutiveSearch.AcceptedFrontierPreservation

/-!
# Constitutive search states

A constitutive state separates the current search frontier from the information
constituted by the path so far.

The constitution component is intentionally abstract.  Concrete instances may
store decisions, anchors, derived relations, or another proof-relevant history.
The core does not assume that this information is recoverable from the current
frontier.
-/

namespace ConstitutiveSearch

universe uConstitution uStep

/--
Current frontier together with the information constituted by the path so far.
-/
structure ConstitutiveState
    (system : SearchSystem)
    (Constitution : Type uConstitution) where
  frontier : List system.State
  constitution : Constitution

/--
One constitutive transition.

The frontier component must preserve viability.  The constitution component is
a separate proof-relevant transition supplied by the concrete search process.
-/
structure ConstitutiveStep
    (system : SearchSystem)
    {Constitution : Type uConstitution}
    (Constitutes : Constitution → Constitution → Type uStep)
    (source target : ConstitutiveState system Constitution) where
  preservation :
    AcceptedFrontierPreservation
      system
      source.frontier
      target.frontier
  constitutes :
    Constitutes
      source.constitution
      target.constitution

namespace ConstitutiveStep

/-- Every constitutive step preserves frontier viability exactly. -/
theorem viable_iff
    {system : SearchSystem}
    {Constitution : Type uConstitution}
    {Constitutes : Constitution → Constitution → Type uStep}
    {source target : ConstitutiveState system Constitution}
    (step : ConstitutiveStep system Constitutes source target) :
    FrontierViable system source.frontier ↔
      FrontierViable system target.frontier :=
  step.preservation.viable_iff

end ConstitutiveStep

end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.ConstitutiveState
#print axioms ConstitutiveSearch.ConstitutiveStep
#print axioms ConstitutiveSearch.ConstitutiveStep.viable_iff
/- AXIOM_AUDIT_END -/
