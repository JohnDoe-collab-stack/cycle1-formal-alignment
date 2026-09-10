import ConstitutiveAlignment.Machine
import Cycle2.ReflectiveAlignment

/-!
# Reflective machine status

This module lifts machine adequacy to propositional status representation and
then reuses the Cycle 2 diagonal kernel.  It neither identifies the resulting
representation exit with an operational exit nor constructs a successor
regime from diagonalization.
-/

namespace ConstitutiveAlignment

open Cycle2.DiagonalizationKernel
open Cycle2.ReflectiveAlignment

universe uCode

abbrev MachineRegimeStatus
    (machine : ConstitutiveMachine)
    (candidate : machine.Candidate) : Prop :=
  Nonempty (machine.Regime candidate)

abbrev MachineNormStatus
    (machine : ConstitutiveMachine)
    (candidate : machine.Candidate) : Prop :=
  Nonempty (machine.Norm candidate)

theorem machineStatusAdequacy
    {machine : ConstitutiveMachine}
    (adequacy : MachineAdequacy machine)
    (candidate : machine.Candidate) :
    MachineRegimeStatus machine candidate ↔
      MachineNormStatus machine candidate :=
  hasStatus_iff_of_maps
    (adequacy.sound candidate)
    (adequacy.complete candidate)

abbrev CodedMachineRegimeStatus
    (machine : ConstitutiveMachine)
    {Code : Type uCode}
    (decode : Code → machine.Candidate) : Code → Prop :=
  PullbackStatus decode (MachineRegimeStatus machine)

abbrev CodedMachineNormStatus
    (machine : ConstitutiveMachine)
    {Code : Type uCode}
    (decode : Code → machine.Candidate) : Code → Prop :=
  PullbackStatus decode (MachineNormStatus machine)

theorem codedMachineStatusAdequacy
    {machine : ConstitutiveMachine}
    (adequacy : MachineAdequacy machine)
    {Code : Type uCode}
    (decode : Code → machine.Candidate)
    (code : Code) :
    CodedMachineRegimeStatus machine decode code ↔
      CodedMachineNormStatus machine decode code :=
  machineStatusAdequacy adequacy (decode code)

structure ReflectiveMachineStatusView
    (machine : ConstitutiveMachine)
    (Code : Type uCode) where
  decode : Code → machine.Candidate
  eval : Code → Code → Prop
  program : Code
  representsRegime :
    Represents eval program (CodedMachineRegimeStatus machine decode)

namespace ReflectiveMachineStatusView

theorem representsNorm
    {machine : ConstitutiveMachine}
    {Code : Type uCode}
    (adequacy : MachineAdequacy machine)
    (view : ReflectiveMachineStatusView machine Code) :
    Represents view.eval view.program
      (CodedMachineNormStatus machine view.decode) :=
  transportRepresentation view.representsRegime
    (codedMachineStatusAdequacy adequacy view.decode)

end ReflectiveMachineStatusView

theorem exactMachineStatusRepresentation_hasDiagonalOutside
    {machine : ConstitutiveMachine}
    {Code : Type uCode}
    (adequacy : MachineAdequacy machine)
    (view : ReflectiveMachineStatusView machine Code) :
    Represents view.eval view.program
        (CodedMachineRegimeStatus machine view.decode) ∧
      Represents view.eval view.program
        (CodedMachineNormStatus machine view.decode) ∧
      ¬ InternallyRepresentable view.eval (diagonalStatus view.eval) :=
  ⟨view.representsRegime,
    view.representsNorm adequacy,
    diagonalStatus_notRepresentable view.eval⟩

theorem exactMachineStatusRepresentation_notGloballyClosed
    {machine : ConstitutiveMachine}
    {Code : Type uCode}
    (view : ReflectiveMachineStatusView machine Code) :
    ¬ GlobalReflectiveClosure view.eval :=
  noGlobalReflectiveClosure view.eval

def machineDiagonalStatusExit
    {machine : ConstitutiveMachine}
    {Code : Type uCode}
    (view : ReflectiveMachineStatusView machine Code) :
    StatusRepresentationExit view.eval :=
  diagonalStatusExit view.eval

/- Existing circular reflective views are reused definitionally. -/
def circularReflectiveMachineView
    {P : StrongPerimetralTurning.CircularPresentation}
    (A : StrongPerimetralTurning.ConcreteContinuationAlgebra P)
    {Code : Type uCode}
    (view : ReflectiveCircularStatusView P Code) :
    ReflectiveMachineStatusView (circularMachine P A) Code :=
  { decode := view.decode
    eval := view.eval
    program := view.program
    representsRegime := view.representsRegime }

/- The two exits coexist in a product but remain differently typed. -/
structure OperationalAndRepresentationalExit
    (machine : ConstitutiveMachine)
    {Code : Type uCode}
    (view : ReflectiveMachineStatusView machine Code) where
  operational : OperationalExit machine
  representational : StatusRepresentationExit view.eval

def combineDistinctExits
    {machine : ConstitutiveMachine}
    {Code : Type uCode}
    (view : ReflectiveMachineStatusView machine Code)
    (operational : OperationalExit machine) :
    OperationalAndRepresentationalExit machine view :=
  { operational := operational
    representational := machineDiagonalStatusExit view }

end ConstitutiveAlignment

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveAlignment.machineStatusAdequacy
#print axioms ConstitutiveAlignment.codedMachineStatusAdequacy
#print axioms ConstitutiveAlignment.ReflectiveMachineStatusView.representsNorm
#print axioms ConstitutiveAlignment.exactMachineStatusRepresentation_hasDiagonalOutside
#print axioms ConstitutiveAlignment.exactMachineStatusRepresentation_notGloballyClosed
#print axioms ConstitutiveAlignment.machineDiagonalStatusExit
#print axioms ConstitutiveAlignment.circularReflectiveMachineView
#print axioms ConstitutiveAlignment.combineDistinctExits
/- AXIOM_AUDIT_END -/
