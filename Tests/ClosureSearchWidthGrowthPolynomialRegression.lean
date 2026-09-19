import ConstitutiveSearch.ClosureSearchWidthGrowthPolynomial

namespace ConstitutiveSearch.Tests.ClosureSearchWidthGrowthPolynomialRegression

open ConstitutiveSearch

theorem candidateBitWidthMonoExample :
    closureCandidateBitWidth 2 ≤
      closureCandidateBitWidth 5 :=
  closureCandidateBitWidth_mono
    (by decide)

theorem growingWidthUnbounded :
    ∀ cap : Nat,
      ∃ n : Nat,
        cap <
          (jointGrowingWidthProfile n).maxFrontierWidth :=
  jointGrowingWidthProfile_width_unbounded

theorem growingFuelUnbounded :
    ∀ cap : Nat,
      ∃ n : Nat,
        cap <
          jointGrowingWidthSchedule.fuel n :=
  jointGrowingWidthSchedule_fuel_unbounded

theorem growingScheduleCountersPolynomial :
    WidthControlledClosureSchedule.InputPolynomialCounters
      jointGrowingWidthPrimitive
      jointGrowingWidthSchedule :=
  jointGrowingWidthSchedule_countersPolynomial

end ConstitutiveSearch.Tests.ClosureSearchWidthGrowthPolynomialRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.ClosureSearchWidthGrowthPolynomialRegression.candidateBitWidthMonoExample
#print axioms ConstitutiveSearch.Tests.ClosureSearchWidthGrowthPolynomialRegression.growingWidthUnbounded
#print axioms ConstitutiveSearch.Tests.ClosureSearchWidthGrowthPolynomialRegression.growingFuelUnbounded
#print axioms ConstitutiveSearch.Tests.ClosureSearchWidthGrowthPolynomialRegression.growingScheduleCountersPolynomial
/- AXIOM_AUDIT_END -/
