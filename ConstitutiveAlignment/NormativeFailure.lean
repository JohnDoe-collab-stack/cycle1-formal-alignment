import ConstitutiveAlignment.Machine
import ConstitutiveAlignment.NormativeExecution

/-!
# Typed failure diagnostics

Formation failure, structural regime exit, and normative failure occupy
different types.  `OperationalExit` remains the existing `RegimeExit` kernel
under the machine vocabulary; it is not redefined here.
-/

namespace ConstitutiveAlignment

universe uRequest uFormed

/- Formation failure precedes the existence of a machine candidate. -/
structure FormationFailure
    (Request : Type uRequest)
    (Formed : Request → Type uFormed) where
  request : Request
  rejectsFormation : Formed request → False

/- Normative failure retains the formed candidate and its positive faithful
   realization while refuting the autonomous norm. -/
structure NormativeFailure (machine : ConstitutiveMachine) where
  candidate : machine.Candidate
  faithful : machine.Faithful candidate
  violatesNorm : machine.Norm candidate → False

namespace OperationalExit

def toNormativeFailure
    {machine : ConstitutiveMachine}
    (adequacy : MachineAdequacy machine)
    (exit : OperationalExit machine) : NormativeFailure machine :=
  { candidate := exit.candidate
    faithful := exit.faithful
    violatesNorm := fun normativeWitness =>
      exit.inadmissible (adequacy.complete exit.candidate normativeWitness) }

end OperationalExit

namespace NormativeFailure

def toOperationalExit
    {machine : ConstitutiveMachine}
    (adequacy : MachineAdequacy machine)
    (failure : NormativeFailure machine) : OperationalExit machine :=
  { candidate := failure.candidate
    faithful := failure.faithful
    inadmissible := fun regimeWitness =>
      failure.violatesNorm
        (adequacy.sound failure.candidate regimeWitness) }

end NormativeFailure

def oneStepNormativeFailure
    (P : StrongPerimetralTurning.CircularPresentation)
    (A : StrongPerimetralTurning.ConcreteContinuationAlgebra P) :
    NormativeFailure (circularMachine P A) :=
  (oneStepOperationalExit P A).toNormativeFailure
    (circularMachineAdequacy P A)

/-! ## Separators -/

namespace FailureExamples

inductive Request : Type
  | malformed

inductive Formed : Request → Type

def malformedRequestFailure : FormationFailure Request Formed :=
  { request := .malformed
    rejectsFormation := fun formed => nomatch formed }

def diagnosticWithoutPrevention :
    NormativeFailure Separators.regimeWithoutNorm :=
  { candidate := ()
    faithful := ()
    violatesNorm := fun normativeWitness => nomatch normativeWitness }

/- This deliberately unmediated effect coexists with the diagnostic.  It
   witnesses why prevention requires `CertifiedEffectuation`, not merely a
   failure report. -/
inductive UnmediatedCandidateEffect :
    Separators.regimeWithoutNorm.Candidate → Type
  | bypass : UnmediatedCandidateEffect ()

def diagnosticAndBypass :
    NormativeFailure Separators.regimeWithoutNorm ×
      UnmediatedCandidateEffect () :=
  ⟨diagnosticWithoutPrevention, .bypass⟩

end FailureExamples

end ConstitutiveAlignment

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveAlignment.OperationalExit.toNormativeFailure
#print axioms ConstitutiveAlignment.NormativeFailure.toOperationalExit
#print axioms ConstitutiveAlignment.oneStepNormativeFailure
#print axioms ConstitutiveAlignment.FailureExamples.malformedRequestFailure
#print axioms ConstitutiveAlignment.FailureExamples.diagnosticAndBypass
/- AXIOM_AUDIT_END -/
