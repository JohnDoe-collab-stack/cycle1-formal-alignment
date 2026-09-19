import ConstitutiveSearch.ConstitutedCodeSequentialComplexity
import ConstitutiveSearch.SAT.ComposedSearchableCode
import ConstitutiveSearch.SAT.ExplicitFamilyInputComplexity

/-!
# Input-polynomial sequential complexity of the constituted composed SAT code

The composed SAT benchmark already has a directly constituted searchable code:

  source -> middle -> target

with exactly two primitive atoms.

This module places that code family into the generic constituted-code
sequential complexity theorem.  Its code-size function is constant two, hence
input-polynomial in the concrete binary size of F(n).

Therefore every family member has a sequential primitive-hit execution with:
* exactly two primitive queries;
* zero composition-candidate inspections;
* a constant polynomial envelope.

No global closure run is needed to obtain this execution.
-/

namespace ConstitutiveSearch
namespace SAT

/-- The directly constituted composed code has input-polynomial size. -/
theorem composedConstitutedCodeSize_inputPolynomiallyBounded :
    InputPolynomiallyBounded
      explicitFamilyInputBitSize
      (fun count =>
        (composedConstitutedCode count).size) :=
  ⟨CostPolynomial.constant 2,
    fun count => by
      rw [composedConstitutedCode_size]
      exact Nat.le_refl 2⟩

/--
The directly constituted composed code family admits a uniformly
input-polynomial sequential execution.
-/
theorem composedConstitutedCode_inputPolynomialSequentialExecution :
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
  searchableCodeFamily_inputPolynomialSequentialExecution
    (fun count =>
      composedPrimitiveSearch count)
    (fun count =>
      [composedMiddle count])
    (fun _count =>
      2)
    (fun _count =>
      by decide)
    composedSource
    composedTarget
    composedConstitutedCode
    composedConstitutedCode_searchable
    composedConstitutedCodeSize_inputPolynomiallyBounded

/--
The constant envelope can be exposed directly as two for the composed family.
-/
theorem composedConstitutedCode_sequentialPrimitive_le_two
    (count : Nat) :
    ∃ path :
        PrimitiveHitPath
          (composedPrimitiveSearch count)
          (composedSource count)
          (composedTarget count),
      path.length = 2 ∧
        (path.sequentialStats
            [composedMiddle count]
            2).primitiveQueries ≤
          2 ∧
        (path.sequentialStats
            [composedMiddle count]
            2).compositionCandidates =
          0 := by
  rcases
      composedConstitutedCode_sequentialExecution
        count with
    ⟨path,
      pathLength,
      primitiveExact,
      compositionZero⟩
  have codeSize :=
    composedConstitutedCode_size count
  refine
    ⟨path, ?_, ?_, compositionZero⟩
  · rw [pathLength, codeSize]
  · rw [primitiveExact, codeSize]
    exact Nat.le_refl 2

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.composedConstitutedCodeSize_inputPolynomiallyBounded
#print axioms ConstitutiveSearch.SAT.composedConstitutedCode_inputPolynomialSequentialExecution
#print axioms ConstitutiveSearch.SAT.composedConstitutedCode_sequentialPrimitive_le_two
/- AXIOM_AUDIT_END -/
