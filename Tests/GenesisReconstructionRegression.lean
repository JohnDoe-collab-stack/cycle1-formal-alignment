import Alignment.GenesisReconstruction

open Alignment
open Alignment.GenesisReconstruction

/-!
# Regression checks for finite genesis reconstruction

The first counterexample preserves the latest fresh identity at depth three but
swaps two earlier fresh identities. It therefore tests that reconstruction
requires the whole finite genesis stratification, not only the terminal fresh
point.

The second example shows the complementary limit: genesis preservation does
not force initial identities to be fixed. A nontrivial exact alignment of the
initial carrier can be lifted while preserving every later fresh stratum.
-/

namespace Alignment.Tests.GenesisReconstructionRegression

universe uInitial

/-- Swap the first two fresh identities while fixing initial and latest identities. -/
def swapFirstTwoFreshAtThree
    {Initial : Type uInitial} :
    IteratedCarrier Initial 3 → IteratedCarrier Initial 3
  | .inl prior =>
      match prior with
      | .inl priorTwo =>
          match priorTwo with
          | .inl initial => .inl (.inl (.inl initial))
          | .inr witness => by cases witness; exact .inl (.inr ())
      | .inr witness => by cases witness; exact .inl (.inl (.inr ()))
  | .inr witness => by cases witness; exact .inr ()

theorem swapFirstTwoFreshAtThree_involutive
    {Initial : Type uInitial}
    (identity : IteratedCarrier Initial 3) :
    swapFirstTwoFreshAtThree (swapFirstTwoFreshAtThree identity) = identity := by
  cases identity with
  | inl prior =>
      cases prior with
      | inl priorTwo =>
          cases priorTwo with
          | inl initial => rfl
          | inr witness => cases witness; rfl
      | inr witness => cases witness; rfl
  | inr witness => cases witness; rfl

def badThreeTransport
    {Initial : Type uInitial} :
    ExactTypeTransport
      (IteratedCarrier Initial 3)
      (IteratedCarrier Initial 3) :=
  { forward := swapFirstTwoFreshAtThree
    backward := swapFirstTwoFreshAtThree
    forwardBackward := swapFirstTwoFreshAtThree_involutive
    backwardForward := swapFirstTwoFreshAtThree_involutive }

/-- The bad transport passes the weaker test that only inspects the latest fresh identity. -/
theorem badThreeTransport_preserves_latestFresh
    {Initial : Type uInitial} :
    (@badThreeTransport Initial).forward
        (@IteratedCarrier.freshAtStep Initial 2) =
      @IteratedCarrier.freshAtStep Initial 2 := by
  rfl

/-- Preserving only the latest fresh identity is insufficient for finite reconstruction. -/
theorem badThreeTransport_not_preservesGenesis
    {Initial : Type uInitial} :
    ¬ PreservesGenesis (@badThreeTransport Initial) := by
  intro preserves
  have reconstructed :=
    reconstruct_forward
      3
      (@badThreeTransport Initial)
      preserves
      (Sum.inl (Sum.inl (Sum.inr ())) : IteratedCarrier Initial 3)
  change
    (Sum.inl (Sum.inr ()) : IteratedCarrier Initial 3) =
      Sum.inl (Sum.inl (Sum.inr ())) at reconstructed
  cases reconstructed

/-- A nontrivial exact alignment on the initial carrier. -/
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

/-- A nontrivial initial alignment still preserves every later fresh generation stratum. -/
theorem liftedBoolSwap_preservesGenesis :
    PreservesGenesis (liftToDepth boolSwapTransport 3) :=
  liftToDepth_preservesGenesis boolSwapTransport 3

/-- Genesis preservation does not by itself identify the initial identities pointwise. -/
theorem liftedBoolSwap_moves_initial :
    (liftToDepth boolSwapTransport 3).forward
        (IteratedCarrier.embedInitial 3 false) ≠
      IteratedCarrier.embedInitial 3 false := by
  change
    (Sum.inl (Sum.inl (Sum.inl true)) : IteratedCarrier Bool 3) ≠
      Sum.inl (Sum.inl (Sum.inl false))
  intro equality
  have booleanEquality : true = false :=
    Sum.inl.inj (Sum.inl.inj (Sum.inl.inj equality))
  cases booleanEquality

end Alignment.Tests.GenesisReconstructionRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms Alignment.Tests.GenesisReconstructionRegression.badThreeTransport_preserves_latestFresh
#print axioms Alignment.Tests.GenesisReconstructionRegression.badThreeTransport_not_preservesGenesis
#print axioms Alignment.Tests.GenesisReconstructionRegression.liftedBoolSwap_preservesGenesis
#print axioms Alignment.Tests.GenesisReconstructionRegression.liftedBoolSwap_moves_initial
/- AXIOM_AUDIT_END -/
