import ConstitutiveSearch.SAT.CausalProjectionNonFactorization

namespace ConstitutiveSearch.Tests.SATCausalProjectionNonFactorizationRegression

open ConstitutiveSearch
open SAT

/-- The public record erases a real difference between two certified runs. -/
theorem publicSameDiscoveryDifferent :
    causalCertifiedObservableProjection 0 =
        causalCertifiedObservableProjection 2 /\
      causalCertifiedDiscoveryVariable 0 ≠
        causalCertifiedDiscoveryVariable 2 :=
  ⟨causalCertifiedObservableProjection_zero_two_same,
    causalCertifiedDiscoveryVariable_zero_two_different⟩

/-- Even the complete published record cannot reconstruct the discovery field. -/
theorem discoveryDoesNotFactor :
    ¬ ValueFactorsThrough
        causalCertifiedObservableProjection
        causalCertifiedDiscoveryVariable :=
  causalDiscoveryVariable_not_factor_through_observable

/-- Complete causal projection-loss evidence package. -/
theorem closed :
    CausalCertifiedProjectionLoss :=
  causalCertifiedProjectionLoss

end ConstitutiveSearch.Tests.SATCausalProjectionNonFactorizationRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATCausalProjectionNonFactorizationRegression.publicSameDiscoveryDifferent
#print axioms ConstitutiveSearch.Tests.SATCausalProjectionNonFactorizationRegression.discoveryDoesNotFactor
#print axioms ConstitutiveSearch.Tests.SATCausalProjectionNonFactorizationRegression.closed
/- AXIOM_AUDIT_END -/
