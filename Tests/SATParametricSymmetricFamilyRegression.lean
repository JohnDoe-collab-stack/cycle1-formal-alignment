import ConstitutiveSearch.SAT.ParametricSymmetricFamily

namespace ConstitutiveSearch.Tests.SATParametricSymmetricFamilyRegression

open ConstitutiveSearch
open SAT

abbrev background : Cnf :=
  [[Literal.positive 1],
   [Literal.negative 2, Literal.positive 3]]

theorem background_avoids_zero :
    Cnf.AvoidsVar 0 background := by
  constructor
  · constructor
    · decide
    · exact True.intro
  · constructor
    · constructor
      · decide
      · constructor
        · decide
        · exact True.intro
    · exact True.intro

theorem anchor_three_differs_zero :
    (3 : Var) ≠ 0 := by
  decide

abbrev formula : Cnf :=
  symmetricBlockFamily 0 3 background

theorem formula_flip_symmetric :
    FlipSymmetricAt formula 0 :=
  symmetricBlockFamily_flipSymmetric
    anchor_three_differs_zero
    background_avoids_zero

abbrev root :
    GeneratedStructuralBranchContext formula :=
  GeneratedStructuralBranchContext.root formula

def reduction :=
  reduceFlipSymmetricSiblings
    root
    0
    True.intro
    formula_flip_symmetric

theorem retained_width_one :
    reduction.width = 1 := by
  rfl

theorem retained_is_true_child :
    reduction.retained =
      [GeneratedStructuralBranchContext.child
        root 0 true True.intro] := by
  rfl

def expansion :=
  generatedStructuralExpansion
    root
    0
    True.intro

def splitThenReduce :
    AcceptedFrontierPreservation
      (generatedStructuralBranchSystem formula)
      [root]
      reduction.retained :=
  expansion.trans reduction.preservation

def allTrue : Assignment :=
  fun _ => true

theorem allTrue_satisfies_formula :
    Satisfies allTrue formula :=
  .cons rfl
    (.cons rfl
      (.cons rfl
        (.cons rfl .nil)))

def rootContinuation :
    GeneratedStructuralBranchContinuation root :=
  ⟨allTrue, True.intro⟩

theorem rootContinuation_accept :
    GeneratedStructuralBranchAccept
      root
      rootContinuation :=
  allTrue_satisfies_formula

theorem root_viable :
    FrontierViable
      (generatedStructuralBranchSystem formula)
      [root] := by
  exact
    ⟨.head rootContinuation,
      rootContinuation_accept⟩

theorem one_step_viable_iff :
    FrontierViable
        (generatedStructuralBranchSystem formula)
        [root] ↔
      FrontierViable
        (generatedStructuralBranchSystem formula)
        reduction.retained :=
  splitThenReduce.viable_iff

theorem retained_viable :
    FrontierViable
      (generatedStructuralBranchSystem formula)
      reduction.retained :=
  one_step_viable_iff.mp root_viable

end ConstitutiveSearch.Tests.SATParametricSymmetricFamilyRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATParametricSymmetricFamilyRegression.background_avoids_zero
#print axioms ConstitutiveSearch.Tests.SATParametricSymmetricFamilyRegression.formula_flip_symmetric
#print axioms ConstitutiveSearch.Tests.SATParametricSymmetricFamilyRegression.reduction
#print axioms ConstitutiveSearch.Tests.SATParametricSymmetricFamilyRegression.retained_width_one
#print axioms ConstitutiveSearch.Tests.SATParametricSymmetricFamilyRegression.retained_is_true_child
#print axioms ConstitutiveSearch.Tests.SATParametricSymmetricFamilyRegression.splitThenReduce
#print axioms ConstitutiveSearch.Tests.SATParametricSymmetricFamilyRegression.rootContinuation
#print axioms ConstitutiveSearch.Tests.SATParametricSymmetricFamilyRegression.rootContinuation_accept
#print axioms ConstitutiveSearch.Tests.SATParametricSymmetricFamilyRegression.root_viable
#print axioms ConstitutiveSearch.Tests.SATParametricSymmetricFamilyRegression.one_step_viable_iff
#print axioms ConstitutiveSearch.Tests.SATParametricSymmetricFamilyRegression.retained_viable
/- AXIOM_AUDIT_END -/
