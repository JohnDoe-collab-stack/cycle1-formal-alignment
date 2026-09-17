import Alignment.GenesisRigidity

namespace Alignment.Tests.GenesisRigidityRegression

open GenesisReconstruction

/-- A nontrivial exact symmetry of the initial Boolean carrier. -/
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

/-- The Boolean initial carrier is not rigid because identity and swap are distinct. -/
theorem bool_initial_not_forwardRigid :
    ¬ InitialForwardRigid Bool Bool := by
  intro rigid
  have impossible :=
    rigid
      (ExactTypeTransport.reflexive Bool)
      boolSwapTransport
      false
  change false = true at impossible
  cases impossible

/-- The same ambiguity persists at every chosen finite genesis depth. -/
theorem bool_depth_three_not_genesisForwardRigid :
    ¬ GenesisForwardRigid Bool Bool 3 := by
  intro terminalRigid
  exact bool_initial_not_forwardRigid
    (initialForwardRigid_of_genesisForwardRigid 3 terminalRigid)

/-- Both competing finite transports preserve the complete genesis stratification. -/
theorem identity_depth_three_preservesGenesis :
    PreservesGenesis
      (liftToDepth (ExactTypeTransport.reflexive Bool) 3) :=
  liftToDepth_preservesGenesis (ExactTypeTransport.reflexive Bool) 3

theorem swap_depth_three_preservesGenesis :
    PreservesGenesis (liftToDepth boolSwapTransport 3) :=
  liftToDepth_preservesGenesis boolSwapTransport 3

/-- Genesis preservation cannot remove a symmetry already present at depth zero. -/
theorem competing_genesis_transports_differ_on_initial :
    (liftToDepth (ExactTypeTransport.reflexive Bool) 3).forward
        (IteratedCarrier.embedInitial 3 false) ≠
      (liftToDepth boolSwapTransport 3).forward
        (IteratedCarrier.embedInitial 3 false) := by
  change
    (Sum.inl (Sum.inl (Sum.inl false)) : IteratedCarrier Bool 3) ≠
      Sum.inl (Sum.inl (Sum.inl true))
  intro equality
  have booleanEquality : false = true :=
    Sum.inl.inj (Sum.inl.inj (Sum.inl.inj equality))
  cases booleanEquality

end Alignment.Tests.GenesisRigidityRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms Alignment.Tests.GenesisRigidityRegression.bool_initial_not_forwardRigid
#print axioms Alignment.Tests.GenesisRigidityRegression.bool_depth_three_not_genesisForwardRigid
#print axioms Alignment.Tests.GenesisRigidityRegression.identity_depth_three_preservesGenesis
#print axioms Alignment.Tests.GenesisRigidityRegression.swap_depth_three_preservesGenesis
#print axioms Alignment.Tests.GenesisRigidityRegression.competing_genesis_transports_differ_on_initial
/- AXIOM_AUDIT_END -/
