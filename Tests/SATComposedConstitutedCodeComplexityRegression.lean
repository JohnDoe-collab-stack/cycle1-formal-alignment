import ConstitutiveSearch.SAT.ComposedConstitutedCodeComplexity

namespace ConstitutiveSearch.Tests.SATComposedConstitutedCodeComplexityRegression

open ConstitutiveSearch
open SAT

theorem sizePolynomial :
    InputPolynomiallyBounded
      explicitFamilyInputBitSize
      (fun count =>
        (composedConstitutedCode count).size) :=
  composedConstitutedCodeSize_inputPolynomiallyBounded

theorem familySequential :
    ∃ envelope : CostPolynomial,
      ∀ count : Nat,
        ∃ path :
            PrimitiveHitPath
              (composedPrimitiveSearch count)
              (composedSource count)
              (composedTarget count),
          path.length =
              (composedConstitutedCode count).size ∧
            (path.sequentialStats
                [composedMiddle count]
                2).primitiveQueries =
              (composedConstitutedCode count).size ∧
            (path.sequentialStats
                [composedMiddle count]
                2).primitiveQueries ≤
              envelope.eval
                (explicitFamilyInputBitSize count) ∧
            (path.sequentialStats
                [composedMiddle count]
                2).compositionCandidates =
              0 :=
  composedConstitutedCode_inputPolynomialSequentialExecution

theorem count3 :
    ∃ path :
        PrimitiveHitPath
          (composedPrimitiveSearch 3)
          (composedSource 3)
          (composedTarget 3),
      path.length = 2 ∧
        (path.sequentialStats
            [composedMiddle 3]
            2).primitiveQueries ≤
          2 ∧
        (path.sequentialStats
            [composedMiddle 3]
            2).compositionCandidates =
          0 :=
  composedConstitutedCode_sequentialPrimitive_le_two 3

end ConstitutiveSearch.Tests.SATComposedConstitutedCodeComplexityRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATComposedConstitutedCodeComplexityRegression.sizePolynomial
#print axioms ConstitutiveSearch.Tests.SATComposedConstitutedCodeComplexityRegression.familySequential
#print axioms ConstitutiveSearch.Tests.SATComposedConstitutedCodeComplexityRegression.count3
/- AXIOM_AUDIT_END -/
