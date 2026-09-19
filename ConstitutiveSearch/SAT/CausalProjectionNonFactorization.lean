import ConstitutiveSearch.ConstitutiveProjectionNonFactorization
import ConstitutiveSearch.SAT.SecondAuditCausalBenchmark

/-!
# Projection loss for the executed causal pipeline

The causal benchmark intentionally exposes an observable record only after a
proof-relevant certified run has been built.  This module connects that API to
the non-factorization vocabulary.

Inputs zero and two are both YES instances.  Their complete public records
(decision, terminal-produced flag, and every published phase counter) are
definitionally equal.  Their certified runs nevertheless discover different
variables.  Therefore the discovery constituted by the executed pipeline
cannot be reconstructed from its public result record alone.

This is a statement about information erased by the announced projection.  It
does not claim that another algorithm cannot compute either variable from the
original input.
-/

namespace ConstitutiveSearch
namespace SAT

/-- Public projection obtained only after constructing the certified run. -/
def causalCertifiedObservableProjection (input : Nat) :
    CausalDecisionProcedureRun :=
  (executeCausalDecisionCertified input).toObservable

/-- Constitutive discovery retained by the certified run before projection. -/
def causalCertifiedDiscoveryVariable (input : Nat) : Var :=
  (executeCausalDecisionCertified input).discovery.var

/-- The retained discovery is exactly the variable selected by actual discovery. -/
theorem causalCertifiedDiscoveryVariable_exact
    (input : Nat) :
    causalCertifiedDiscoveryVariable input =
      causalDecisionSplitVar input := by
  exact
    causalDecision_discovered_var
      input
      (executeCausalDecisionCertified input).discovery
      (executeCausalDecisionCertified input).discovery_from_actual_run

/--
The full public records of the first two YES instances coincide, including all
published phase-local counters.  This equality is computation, not an
assumption about the runs.
-/
theorem causalCertifiedObservableProjection_zero_two_same :
    causalCertifiedObservableProjection 0 =
      causalCertifiedObservableProjection 2 := by
  rfl

/-- The certified discoveries behind those equal public records are distinct. -/
theorem causalCertifiedDiscoveryVariable_zero_two_different :
    causalCertifiedDiscoveryVariable 0 ≠
      causalCertifiedDiscoveryVariable 2 := by
  intro same
  have selectedZero := causalCertifiedDiscoveryVariable_exact 0
  have selectedTwo := causalCertifiedDiscoveryVariable_exact 2
  have impossible : causalDecisionSplitVar 0 = causalDecisionSplitVar 2 :=
    Eq.trans selectedZero.symm (Eq.trans same selectedTwo)
  change 2 = 4 at impossible
  cases Nat.succ.inj (Nat.succ.inj impossible)

/--
The constitutively discovered variable does not factor through the complete
observable procedure record.
-/
theorem causalDiscoveryVariable_not_factor_through_observable :
    ¬ ValueFactorsThrough
        causalCertifiedObservableProjection
        causalCertifiedDiscoveryVariable := by
  exact
    value_not_factors_of_same_projection
      causalCertifiedObservableProjection
      causalCertifiedDiscoveryVariable
      0
      2
      causalCertifiedObservableProjection_zero_two_same
      causalCertifiedDiscoveryVariable_zero_two_different

/-- Exact causal projection-loss package prepared for adversarial audit. -/
structure CausalCertifiedProjectionLoss : Prop where
  publicRunEqual :
    causalCertifiedObservableProjection 0 =
      causalCertifiedObservableProjection 2
  discoveryDifferent :
    causalCertifiedDiscoveryVariable 0 ≠
      causalCertifiedDiscoveryVariable 2
  discoveryLoss :
    ¬ ValueFactorsThrough
        causalCertifiedObservableProjection
        causalCertifiedDiscoveryVariable

theorem causalCertifiedProjectionLoss :
    CausalCertifiedProjectionLoss :=
  { publicRunEqual :=
      causalCertifiedObservableProjection_zero_two_same
    discoveryDifferent :=
      causalCertifiedDiscoveryVariable_zero_two_different
    discoveryLoss :=
      causalDiscoveryVariable_not_factor_through_observable }

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.causalCertifiedObservableProjection
#print axioms ConstitutiveSearch.SAT.causalCertifiedDiscoveryVariable
#print axioms ConstitutiveSearch.SAT.causalCertifiedDiscoveryVariable_exact
#print axioms ConstitutiveSearch.SAT.causalCertifiedObservableProjection_zero_two_same
#print axioms ConstitutiveSearch.SAT.causalCertifiedDiscoveryVariable_zero_two_different
#print axioms ConstitutiveSearch.SAT.causalDiscoveryVariable_not_factor_through_observable
#print axioms ConstitutiveSearch.SAT.CausalCertifiedProjectionLoss
#print axioms ConstitutiveSearch.SAT.causalCertifiedProjectionLoss
/- AXIOM_AUDIT_END -/
