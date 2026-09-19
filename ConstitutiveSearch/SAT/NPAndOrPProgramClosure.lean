import ConstitutiveSearch.SAT.TrajectoryScheduleComposition
import ConstitutiveSearch.SAT.TrajectoryConstitutiveSynthesis
import ConstitutiveSearch.SAT.ConstitutiveProjectionSeparators

/-!
# Formal closure of the NP AND/OR P constitutive program

This module does not add a new search mechanism.

It packages the three closure obligations already proved:

1. local constituted schedules are endpoint-composable exactly under endpoint
   adjacency, while FlipSymmetricTrajectory schedules of length at least two
   remain schedules of local sibling reductions;
2. the complete production / provenance / validation / actual execution
   accounting for F(n) is input-polynomial without double-charging production;
3. forgetting constitution or temporal organization provably loses
   computationally relevant information.

This theorem closes the announced constitutive program.  It is not a theorem
about equality or inequality of classical complexity classes.
-/

namespace ConstitutiveSearch
namespace SAT

/--
Closed evidence package for the announced NP AND/OR P constitutive program.
-/
structure NPAndOrPProgramClosed : Prop where
  endpointComposition :
    ∀ {rootFormula : Cnf}
      (first :
        ConstitutedLocalWitness rootFormula)
      (rest :
        List (ConstitutedLocalWitness rootFormula)),
      ConstitutedLocalSchedule.EndpointComposable
          (first :: rest) →
        ∃ target :
            GeneratedStructuralBranchContext rootFormula,
          ∃ code :
              TransportClosure
                (GeneratedStructuralFlipWitness
                  (rootFormula := rootFormula))
                first.source
                target,
            code.size =
              (first :: rest).length
  trajectorySchedulesRemainLocal :
    ∀ {rootFormula : Cnf}
      {start finish :
        GeneratedStructuralBranchContext rootFormula}
      {length : Nat}
      (trajectory :
        FlipSymmetricTrajectory
          start
          finish
          length),
      2 ≤ length →
        ¬
          ConstitutedLocalSchedule.EndpointComposable
            trajectory.constitutedLocalWitnesses
  quantitativeClosure :
    ExplicitFamilyQuantitativeProgramClosed
  projectionLoss :
    ConstitutiveProjectionLossClosed

/--
The NP AND/OR P constitutive program is formally closed at the announced scope.
-/
theorem npAndOrPProgramClosed :
    NPAndOrPProgramClosed :=
  { endpointComposition :=
      ConstitutedLocalSchedule.endpointComposable_hasTransportCode
    trajectorySchedulesRemainLocal :=
      FlipSymmetricTrajectory.constitutedLocalWitnesses_not_endpointComposable_of_two_le
    quantitativeClosure :=
      explicitFamilyQuantitativeProgramClosed
    projectionLoss :=
      constitutiveProjectionLossClosed }

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.NPAndOrPProgramClosed
#print axioms ConstitutiveSearch.SAT.npAndOrPProgramClosed
/- AXIOM_AUDIT_END -/
