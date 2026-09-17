import ConstitutiveSearch.FiniteFrontierNormalization
import ConstitutiveSearch.SAT.RestrictionTransport

/-!
# Finite SAT residual trajectories

This module connects successive SAT branch residuals to the generic finite
frontier normalizer.

A two-step trajectory contains the source CNF, the residual after one fixed
branch value, and the residual after a second fixed branch value. Each residual
is produced syntactically by `branchResidual`. The generic CNF weakening search
is then used to reconstruct directional continuation transports between states
of that finite trajectory.

No satisfiability query participates in trajectory construction or reduction.
The final width is measured only from the retained frontier produced by the
normalizer.
-/

namespace ConstitutiveSearch
namespace SAT

/-- Residual after one branch restriction. -/
def firstResidual
    (formula : Cnf)
    (firstVar : Var)
    (firstValue : Bool) : Cnf :=
  branchResidual formula firstVar firstValue

/-- Residual after a second branch restriction applied to the first residual. -/
def secondResidual
    (formula : Cnf)
    (firstVar : Var)
    (firstValue : Bool)
    (secondVar : Var)
    (secondValue : Bool) : Cnf :=
  branchResidual
    (firstResidual formula firstVar firstValue)
    secondVar
    secondValue

/-- Three syntactic states of a concrete two-step restriction trajectory. -/
def twoStepResidualTrajectory
    (formula : Cnf)
    (firstVar : Var)
    (firstValue : Bool)
    (secondVar : Var)
    (secondValue : Bool) : List Cnf :=
  [ formula,
    firstResidual formula firstVar firstValue,
    secondResidual formula firstVar firstValue secondVar secondValue ]

/-- The first trajectory edge has an explicit constructive weakening witness. -/
def firstResidualWeakening
    (formula : Cnf)
    (firstVar : Var)
    (firstValue : Bool) :
    CnfWeakening
      formula
      (firstResidual formula firstVar firstValue) :=
  branchWeakening formula firstVar firstValue

/-- The second trajectory edge has an explicit constructive weakening witness. -/
def secondResidualWeakening
    (formula : Cnf)
    (firstVar : Var)
    (firstValue : Bool)
    (secondVar : Var)
    (secondValue : Bool) :
    CnfWeakening
      (firstResidual formula firstVar firstValue)
      (secondResidual
        formula firstVar firstValue secondVar secondValue) :=
  branchWeakening
    (firstResidual formula firstVar firstValue)
    secondVar
    secondValue

/-- Normalize the complete finite trajectory using only structural CNF weakening. -/
def reduceTwoStepResidualTrajectory
    (formula : Cnf)
    (firstVar : Var)
    (firstValue : Bool)
    (secondVar : Var)
    (secondValue : Bool) :
    IrreducibleFrontierReduction
      (Completion := Completion)
      weakeningSearch
      (twoStepResidualTrajectory
        formula firstVar firstValue secondVar secondValue) :=
  normalizeFrontier
    weakeningSearch
    weakeningAction
    (twoStepResidualTrajectory
      formula firstVar firstValue secondVar secondValue)

/-- Width derived from the normalized two-step residual trajectory. -/
def twoStepResidualWidth
    (formula : Cnf)
    (firstVar : Var)
    (firstValue : Bool)
    (secondVar : Var)
    (secondValue : Bool) : Nat :=
  (reduceTwoStepResidualTrajectory
    formula firstVar firstValue secondVar secondValue).width

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.firstResidual
#print axioms ConstitutiveSearch.SAT.secondResidual
#print axioms ConstitutiveSearch.SAT.twoStepResidualTrajectory
#print axioms ConstitutiveSearch.SAT.firstResidualWeakening
#print axioms ConstitutiveSearch.SAT.secondResidualWeakening
#print axioms ConstitutiveSearch.SAT.reduceTwoStepResidualTrajectory
#print axioms ConstitutiveSearch.SAT.twoStepResidualWidth
/- AXIOM_AUDIT_END -/
