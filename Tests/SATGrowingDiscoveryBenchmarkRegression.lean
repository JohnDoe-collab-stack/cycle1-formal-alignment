import ConstitutiveSearch.SAT.GrowingDiscoveryBenchmark

namespace ConstitutiveSearch.Tests.SATGrowingDiscoveryBenchmarkRegression

open ConstitutiveSearch
open SAT

/-- Five input units force six distinct failed decoys before the seventh try. -/
theorem concreteGrowingDiscovery :
    exists discovery,
      (runEndogenousFlipDiscovery
        (distinctGrowingDiscoveryRoot 5)).outcome.discovered? = some discovery /\
      discovery.var = 7 /\
      (runEndogenousFlipDiscovery
        (distinctGrowingDiscoveryRoot 5)).outcome.attempts = 7 := by
  rcases distinctGrowingDiscovery_found_after_exact_attempts 5 with
    ⟨discovery, found, selected, attempts⟩
  exact ⟨discovery, found, selected, attempts⟩

/-- The six preceding candidates are pairwise distinct, not repeated padding. -/
theorem concreteDistinctDecoys :
    (distinctDecoyVariables 6).Nodup /\
      (distinctDecoyVariables 6).length = 6 :=
  ⟨distinctDecoyVariables_nodup 6,
    distinctDecoyVariables_length 6⟩

/-- Extraction work is produced by traversal and visits all distinct literals. -/
theorem concreteGrowingExtraction :
    (runCandidateExtraction
        (distinctGrowingDiscoveryRoot 5)).stats.clauseVisits = 3 /\
      (runCandidateExtraction
        (distinctGrowingDiscoveryRoot 5)).stats.literalVisits = 10 :=
  distinctGrowingDiscovery_extraction_stats 5

/-- Appending one input unit moves the useful discovery one attempt later. -/
theorem discoveryAttemptsStrict
    (input : Nat) :
    (runEndogenousFlipDiscovery
        (distinctGrowingDiscoveryRoot input)).outcome.attempts <
      (runEndogenousFlipDiscovery
        (distinctGrowingDiscoveryRoot (input + 1))).outcome.attempts :=
  distinctGrowingDiscovery_attempts_strict input

end ConstitutiveSearch.Tests.SATGrowingDiscoveryBenchmarkRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATGrowingDiscoveryBenchmarkRegression.concreteGrowingDiscovery
#print axioms ConstitutiveSearch.Tests.SATGrowingDiscoveryBenchmarkRegression.concreteDistinctDecoys
#print axioms ConstitutiveSearch.Tests.SATGrowingDiscoveryBenchmarkRegression.concreteGrowingExtraction
#print axioms ConstitutiveSearch.Tests.SATGrowingDiscoveryBenchmarkRegression.discoveryAttemptsStrict
/- AXIOM_AUDIT_END -/
