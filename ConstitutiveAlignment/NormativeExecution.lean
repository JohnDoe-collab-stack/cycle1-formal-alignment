import ConstitutiveAlignment.Machine

set_option linter.checkUnivs false

/-!
# Normative admission and certified effectuation

Actions are values before they are effects.  Certificates are indexed by the
exact action and actual constitutive context.  The only effectuation object
exported here contains such a certificate and the result computed from it.
-/

namespace ConstitutiveAlignment

universe uNature uTarget uParameters uContext uScope uEffector
universe uAdmission uNorm uCertificate uEffect

structure ActionSignature where
  Nature : Type uNature
  Target : Type uTarget
  Parameters : Type uParameters
  Context : Type uContext
  Scope : Type uScope
  Effector : Type uEffector

structure ConstitutiveAction (signature : ActionSignature) where
  nature : signature.Nature
  target : signature.Target
  parameters : signature.Parameters
  declaredContext : signature.Context
  scope : signature.Scope
  requestedEffector : signature.Effector

structure NormativeExecutor (signature : ActionSignature) where
  Admission :
    signature.Context → ConstitutiveAction signature → Type uAdmission
  Norm : signature.Context → ConstitutiveAction signature → Type uNorm
  Certificate :
    signature.Context → ConstitutiveAction signature → Type uCertificate
  certificateAdmits :
    {context : signature.Context} →
    {action : ConstitutiveAction signature} →
      Certificate context action → Admission context action
  admissionSound :
    {context : signature.Context} →
    {action : ConstitutiveAction signature} →
      Admission context action → Norm context action
  Effect : signature.Context → ConstitutiveAction signature → Type uEffect
  perform :
    {context : signature.Context} →
    {action : ConstitutiveAction signature} →
      Certificate context action → Effect context action

structure CertifiedEffectuation
    {signature : ActionSignature}
    (executor : NormativeExecutor signature)
    (context : signature.Context)
    (action : ConstitutiveAction signature) where
  certificate : executor.Certificate context action
  result : executor.Effect context action
  resultExact : result = executor.perform certificate

def NormativeExecutor.effectuate
    {signature : ActionSignature}
    (executor : NormativeExecutor signature)
    {context : signature.Context}
    {action : ConstitutiveAction signature}
    (certificate : executor.Certificate context action) :
    CertifiedEffectuation executor context action :=
  { certificate := certificate
    result := executor.perform certificate
    resultExact := rfl }

def CertifiedEffectuation.admitted
    {signature : ActionSignature}
    {executor : NormativeExecutor signature}
    {context : signature.Context}
    {action : ConstitutiveAction signature}
    (effectuation : CertifiedEffectuation executor context action) :
    executor.Admission context action :=
  executor.certificateAdmits effectuation.certificate

def CertifiedEffectuation.normative
    {signature : ActionSignature}
    {executor : NormativeExecutor signature}
    {context : signature.Context}
    {action : ConstitutiveAction signature}
    (effectuation : CertifiedEffectuation executor context action) :
    executor.Norm context action :=
  executor.admissionSound effectuation.admitted

/- Rejection and non-effectuation are related only through the indexed
   certificate family; the rejected action is not rewritten into another one. -/
theorem noEffectuation_withoutCertificate
    {signature : ActionSignature}
    {executor : NormativeExecutor signature}
    {context : signature.Context}
    {action : ConstitutiveAction signature}
    (noCertificate : executor.Certificate context action → False) :
    CertifiedEffectuation executor context action → False :=
  fun effectuation => noCertificate effectuation.certificate

/-! ## Finite authorization model and negative bypass -/

namespace ExecutionExamples

inductive ActionNature : Type
  | read
  | write

inductive ActionTarget : Type
  | publicData
  | restrictedData

inductive ActionContext : Type
  | active
  | expired

def signature : ActionSignature where
  Nature := ActionNature
  Target := ActionTarget
  Parameters := Unit
  Context := ActionContext
  Scope := Unit
  Effector := Unit

def allowedAction : ConstitutiveAction signature where
  nature := .read
  target := .publicData
  parameters := ()
  declaredContext := .active
  scope := ()
  requestedEffector := ()

def otherTargetAction : ConstitutiveAction signature where
  nature := .read
  target := .restrictedData
  parameters := ()
  declaredContext := .active
  scope := ()
  requestedEffector := ()

def modifiedAction : ConstitutiveAction signature where
  nature := .write
  target := .publicData
  parameters := ()
  declaredContext := .active
  scope := ()
  requestedEffector := ()

inductive Admission :
    signature.Context → ConstitutiveAction signature → Type
  | allowRead : Admission .active allowedAction

/- This norm is declared independently from `Admission`; adequacy is supplied
   by a separate transformation in `executor`. -/
inductive Norm :
    signature.Context → ConstitutiveAction signature → Type
  | publicRead : Norm .active allowedAction

inductive Certificate :
    signature.Context → ConstitutiveAction signature → Type
  | issued : Certificate .active allowedAction

inductive Effect :
    signature.Context → ConstitutiveAction signature → Type
  | publicReadPerformed : Effect .active allowedAction

def executor : NormativeExecutor signature where
  Admission := Admission
  Norm := Norm
  Certificate := Certificate
  certificateAdmits
    | .issued => .allowRead
  admissionSound
    | .allowRead => .publicRead
  Effect := Effect
  perform
    | .issued => .publicReadPerformed

def allowedEffectuation :
    CertifiedEffectuation executor .active allowedAction :=
  executor.effectuate .issued

theorem otherTarget_hasNoCertificate :
    executor.Certificate .active otherTargetAction → False := by
  intro certificate
  nomatch certificate

theorem expiredContext_hasNoCertificate :
    executor.Certificate .expired allowedAction → False := by
  intro certificate
  nomatch certificate

theorem modifiedAction_notAdmitted :
    executor.Admission .active modifiedAction → False := by
  intro admission
  nomatch admission

theorem otherTarget_cannotBeEffectuated :
    CertifiedEffectuation executor .active otherTargetAction → False :=
  noEffectuation_withoutCertificate otherTarget_hasNoCertificate

/- An unmediated effect can be asserted for a rejected action, but it is not a
   `CertifiedEffectuation` and therefore carries no admission or norm theorem. -/
inductive UnmediatedEffect : ConstitutiveAction signature → Type
  | bypass : UnmediatedEffect otherTargetAction

def rejectedActionBypass : UnmediatedEffect otherTargetAction :=
  .bypass

end ExecutionExamples

end ConstitutiveAlignment

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveAlignment.NormativeExecutor.effectuate
#print axioms ConstitutiveAlignment.CertifiedEffectuation.admitted
#print axioms ConstitutiveAlignment.CertifiedEffectuation.normative
#print axioms ConstitutiveAlignment.noEffectuation_withoutCertificate
#print axioms ConstitutiveAlignment.ExecutionExamples.allowedEffectuation
#print axioms ConstitutiveAlignment.ExecutionExamples.otherTarget_hasNoCertificate
#print axioms ConstitutiveAlignment.ExecutionExamples.expiredContext_hasNoCertificate
#print axioms ConstitutiveAlignment.ExecutionExamples.modifiedAction_notAdmitted
#print axioms ConstitutiveAlignment.ExecutionExamples.otherTarget_cannotBeEffectuated
#print axioms ConstitutiveAlignment.ExecutionExamples.rejectedActionBypass
/- AXIOM_AUDIT_END -/
