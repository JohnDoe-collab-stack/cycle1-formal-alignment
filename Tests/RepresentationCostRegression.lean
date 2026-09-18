import ConstitutiveSearch.RepresentationCost

namespace ConstitutiveSearch.Tests.RepresentationCostRegression

open BinaryRepresentation

theorem bits0 :
    natBitSize 0 = 1 := by
  rfl

theorem bits1 :
    natBitSize 1 = 1 := by
  rfl

theorem bits2 :
    natBitSize 2 = 2 := by
  rfl

theorem bits3 :
    natBitSize 3 = 2 := by
  rfl

theorem bits4 :
    natBitSize 4 = 3 := by
  rfl

theorem bits4_le :
    natBitSize 4 ≤ 5 :=
  natBitSize_le_succ 4

end ConstitutiveSearch.Tests.RepresentationCostRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.RepresentationCostRegression.bits0
#print axioms ConstitutiveSearch.Tests.RepresentationCostRegression.bits1
#print axioms ConstitutiveSearch.Tests.RepresentationCostRegression.bits2
#print axioms ConstitutiveSearch.Tests.RepresentationCostRegression.bits3
#print axioms ConstitutiveSearch.Tests.RepresentationCostRegression.bits4
#print axioms ConstitutiveSearch.Tests.RepresentationCostRegression.bits4_le
/- AXIOM_AUDIT_END -/
