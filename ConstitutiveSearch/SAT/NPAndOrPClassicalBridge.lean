import ConstitutiveSearch.ClassicalDecisionComplexity
import ConstitutiveSearch.SAT.NPAndOrPProgramClosure

/-!
# Final minimal bridge from NP AND/OR P to classical P / NP interfaces

The constitutive program is already closed before this module.

This file only projects the closed result to an extensional decision view:

* the explicit family F(n) becomes a decision problem indexed by n;
* its constituted AND/OR trajectory preserves the yes/no viability answer;
* the generic NP-like continuation role projects to InNP only when an explicit
  polynomial verifier interface is supplied;
* the generic P-like computational role projects to InP only when an explicit
  correct polynomial decider is supplied;
* the classical extensional projection is not faithful to the constitutive
  computation: existing non-factorization theorems show loss of reconstructible
  relations and execution-organization cost.

No statement of P = NP or P != NP is made or required.
-/

namespace ConstitutiveSearch
namespace SAT

/--
Extensional decision problem obtained from the closed explicit family.

The input is only the family index.  The accepted proposition is viability of
the initial generated frontier.  The internal schedule, provenance and temporal
organization are intentionally absent from this classical projection.
-/
def explicitFamilyDecisionProblem :
    DecisionProblem :=
  { inputSize :=
      explicitFamilyInputBitSize
    Accept := fun count =>
      FrontierViable
        (generatedStructuralBranchSystem
          (explicitStackedSymmetricFamily
            count))
        [explicitStackedRoot count] }

/--
The AND/OR constitutive computation preserves exactly the classical yes/no
decision projected from F(n).
-/
theorem explicitFamilyDecisionProjection_preserved
    (count : Nat) :
    explicitFamilyDecisionProblem.Accept
        count ↔
      FrontierViable
        (generatedStructuralBranchSystem
          (explicitStackedSymmetricFamily
            count))
        [(explicitFamilyResourceTrajectory
          count).finish] :=
  explicitFamilyResourceTrajectory_viable_iff
    count

/--
Alias emphasizing the classical NP projection principle:
continuations become witnesses, but NP membership is obtained only from an
explicit polynomial verifier interface.
-/
theorem constitutiveNPStyle_projects_to_classicalNP
    {system : SearchSystem}
    {stateAt : Nat → system.State}
    {inputSize : Nat → Nat}
    (bridge :
      SearchSystemPolynomialVerifier
        system
        stateAt
        inputSize) :
    InNP
      (searchSystemDecisionProblem
        system
        stateAt
        inputSize)
      (fun input =>
        system.Continuation
          (stateAt input)) :=
  npLike_projects_to_InNP
    bridge

/--
Alias emphasizing the classical P projection principle:
P-like structural computation becomes P only when it supplies a correct
polynomial decision procedure in the declared cost model.
-/
theorem constitutivePStyle_projects_to_classicalP
    {system : SearchSystem}
    {stateAt : Nat → system.State}
    {inputSize : Nat → Nat}
    (bridge :
      SearchSystemPolynomialDecider
        system
        stateAt
        inputSize) :
    InP
      (searchSystemDecisionProblem
        system
        stateAt
        inputSize) :=
  pLike_projects_to_InP
    bridge

/--
The minimal bridge preserves the extensional decision but records that the
projection loses computationally relevant constitutive structure.
-/
structure NPAndOrPClassicalBridgeClosed : Prop where
  programClosed :
    NPAndOrPProgramClosed
  decisionPreserved :
    ∀ count : Nat,
      explicitFamilyDecisionProblem.Accept
          count ↔
        FrontierViable
          (generatedStructuralBranchSystem
            (explicitStackedSymmetricFamily
              count))
          [(explicitFamilyResourceTrajectory
            count).finish]
  projectionLoss :
    ConstitutiveProjectionLossClosed

/-- Final classical bridge for the already-closed constitutive program. -/
theorem npAndOrPClassicalBridgeClosed :
    NPAndOrPClassicalBridgeClosed :=
  { programClosed :=
      npAndOrPProgramClosed
    decisionPreserved :=
      explicitFamilyDecisionProjection_preserved
    projectionLoss :=
      constitutiveProjectionLossClosed }

/--
Final stop marker for the announced NP / P objective.

It contains the closed constitutive program and its minimal classical
projection, including the proved loss of constitutive computational structure.
It carries no further complexity-class consequence.
-/
structure NPAndPObjectiveComplete : Prop where
  bridge :
    NPAndOrPClassicalBridgeClosed

/-- OBJECTIF NP / P TERMINE. -/
theorem npAndPObjectiveComplete :
    NPAndPObjectiveComplete :=
  { bridge :=
      npAndOrPClassicalBridgeClosed }

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.explicitFamilyDecisionProblem
#print axioms ConstitutiveSearch.SAT.explicitFamilyDecisionProjection_preserved
#print axioms ConstitutiveSearch.SAT.constitutiveNPStyle_projects_to_classicalNP
#print axioms ConstitutiveSearch.SAT.constitutivePStyle_projects_to_classicalP
#print axioms ConstitutiveSearch.SAT.NPAndOrPClassicalBridgeClosed
#print axioms ConstitutiveSearch.SAT.npAndOrPClassicalBridgeClosed
#print axioms ConstitutiveSearch.SAT.NPAndPObjectiveComplete
#print axioms ConstitutiveSearch.SAT.npAndPObjectiveComplete
/- AXIOM_AUDIT_END -/
