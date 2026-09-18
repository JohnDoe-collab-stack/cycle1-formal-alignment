import ConstitutiveSearch.SAT.WidthSeparatorConstitutiveProfile

namespace ConstitutiveSearch.Tests.SATWidthSeparatorConstitutiveProfileRegression

open ConstitutiveSearch
open SAT

theorem width3 :
    (isolatedSeparatorEnvelopeProfile 3).maxFrontierWidth = 3 :=
  isolatedSeparatorEnvelopeProfile_width 3

theorem depth3 :
    (isolatedSeparatorEnvelopeProfile 3).depth = 1 := by
  rfl

theorem representationConsistent3 :
    RepresentationConsistent
      (isolatedSeparatorEnvelopeProfile 3)
      (isolatedSeparatorRepresentationAtomicCosts 3) :=
  isolatedSeparatorEnvelopeProfile_representationConsistent 3


theorem index3_le_serializedInput :
    3 ≤ isolatedFrontierInputBitSize 3 :=
  isolatedSeparatorIndex_le_inputBitSize 3

theorem separatorFamily_inputPolynomial :
    ConstitutiveProfileFamilyInputPolynomiallyBounded
      isolatedSeparatorEnvelopeProfile :=
  isolatedSeparatorEnvelopeProfile_inputPolynomiallyBounded

theorem normalizationBound3 :
    normalizationFindCallCount
        (generatedStructuralFlipAtSearch ([] : Cnf) 0)
        (generatedStructuralFlipAtAction ([] : Cnf) 0)
        (isolatedFrontier 3) ≤
      (isolatedSeparatorEnvelopeProfile 3).events.relationFindCalls :=
  isolatedSeparator_normalizationFindCalls_le_profile 0 3

theorem separatorNotBelowComposition3 :
    ¬
      (isolatedSeparatorEnvelopeProfile 3).BoundedBy
        (composedClosureConstitutivePhaseProfile 3) :=
  isolatedSeparator3_not_boundedBy_compositionPhase3

theorem compositionNotBelowSeparator3 :
    ¬
      (composedClosureConstitutivePhaseProfile 3).BoundedBy
        (isolatedSeparatorEnvelopeProfile 3) :=
  compositionPhase3_not_boundedBy_isolatedSeparator3

end ConstitutiveSearch.Tests.SATWidthSeparatorConstitutiveProfileRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATWidthSeparatorConstitutiveProfileRegression.width3
#print axioms ConstitutiveSearch.Tests.SATWidthSeparatorConstitutiveProfileRegression.depth3
#print axioms ConstitutiveSearch.Tests.SATWidthSeparatorConstitutiveProfileRegression.representationConsistent3
#print axioms ConstitutiveSearch.Tests.SATWidthSeparatorConstitutiveProfileRegression.index3_le_serializedInput
#print axioms ConstitutiveSearch.Tests.SATWidthSeparatorConstitutiveProfileRegression.separatorFamily_inputPolynomial
#print axioms ConstitutiveSearch.Tests.SATWidthSeparatorConstitutiveProfileRegression.normalizationBound3
#print axioms ConstitutiveSearch.Tests.SATWidthSeparatorConstitutiveProfileRegression.separatorNotBelowComposition3
#print axioms ConstitutiveSearch.Tests.SATWidthSeparatorConstitutiveProfileRegression.compositionNotBelowSeparator3
/- AXIOM_AUDIT_END -/
