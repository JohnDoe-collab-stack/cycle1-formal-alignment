import Alignment.ConstitutiveProfileRigidity

namespace Alignment.Tests.ConstitutiveProfileRigidityRegression

open GenesisReconstruction

/-- A profile whose single probe returns the identity itself. -/
def identityProfile : Bool → Unit → Bool :=
  fun identity _ => identity

/-- The identity-valued profile separates the Boolean carrier. -/
theorem identityProfile_separates :
    ProfileSeparates identityProfile := by
  intro first second agreement
  exact agreement ()

/-- The identity map preserves the separating profile. -/
theorem identityProfile_identity_preserved :
    PreservesProfile identityProfile identityProfile (fun value => value) := by
  intro identity probe
  cases probe
  rfl

/-- Every map preserving the separating identity profile is forced pointwise. -/
theorem identityProfile_forces_candidate
    (candidate : Bool → Bool)
    (candidatePreserves :
      PreservesProfile identityProfile identityProfile candidate)
    (identity : Bool) :
    candidate identity = identity :=
  profilePreserving_forward_unique
    identityProfile
    identityProfile
    identityProfile_separates
    candidate
    (fun value => value)
    candidatePreserves
    identityProfile_identity_preserved
    identity

/-- A deliberately non-faithful profile. -/
def constantProfile : Bool → Unit → Bool :=
  fun _ _ => false

/-- The constant profile cannot distinguish the two Boolean identities. -/
theorem constantProfile_not_separating :
    ¬ ProfileSeparates constantProfile := by
  intro separates
  have impossible : false = true :=
    separates false true (by
      intro probe
      cases probe
      rfl)
  cases impossible

/-- A nontrivial exact Boolean symmetry. -/
def swapBool : Bool → Bool
  | false => true
  | true => false

theorem swapBool_involutive
    (value : Bool) :
    swapBool (swapBool value) = value := by
  cases value <;> rfl

def boolSwapTransport : ExactTypeTransport Bool Bool :=
  { forward := swapBool
    backward := swapBool
    forwardBackward := swapBool_involutive
    backwardForward := swapBool_involutive }

/-- Identity and swap both preserve the non-separating constant profile. -/
theorem constantProfile_identity_preserved :
    PreservesProfile constantProfile constantProfile (fun value => value) := by
  intro identity probe
  cases identity <;> cases probe <;> rfl

theorem constantProfile_swap_preserved :
    PreservesProfile constantProfile constantProfile boolSwapTransport.forward := by
  intro identity probe
  cases identity <;> cases probe <;> rfl

/-- Non-separating observations leave genuine initial alignment ambiguity. -/
theorem constantProfile_candidates_differ :
    boolSwapTransport.forward false ≠ false := by
  intro equality
  change true = false at equality
  cases equality

end Alignment.Tests.ConstitutiveProfileRigidityRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms Alignment.Tests.ConstitutiveProfileRigidityRegression.identityProfile_separates
#print axioms Alignment.Tests.ConstitutiveProfileRigidityRegression.identityProfile_forces_candidate
#print axioms Alignment.Tests.ConstitutiveProfileRigidityRegression.constantProfile_not_separating
#print axioms Alignment.Tests.ConstitutiveProfileRigidityRegression.constantProfile_identity_preserved
#print axioms Alignment.Tests.ConstitutiveProfileRigidityRegression.constantProfile_swap_preserved
#print axioms Alignment.Tests.ConstitutiveProfileRigidityRegression.constantProfile_candidates_differ
/- AXIOM_AUDIT_END -/
