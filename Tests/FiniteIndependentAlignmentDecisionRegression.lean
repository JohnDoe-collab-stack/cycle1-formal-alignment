import Alignment.FiniteIndependentAlignmentDecision
import Tests.IndependentRelationalAlignmentRegression

namespace Alignment.Tests.FiniteIndependentAlignmentDecisionRegression

open GenesisReconstruction
open GenesisReconstruction.FiniteAnchoredMatchSearch
open GenesisReconstruction.FiniteIndependentAlignmentDecision
open IntrinsicRelationalMediatorRegression
open IndependentRelationalAlignmentRegression

deriving instance DecidableEq for SourceNode
deriving instance DecidableEq for TargetNode

def sourceNodeListing : FiniteListing SourceNode :=
  { values := [.root, .next]
    complete := by
      intro identity
      cases identity
      · exact List.Mem.head [SourceNode.next]
      · exact
          List.Mem.tail SourceNode.root
            (List.Mem.head []) }

def targetNodeListing : FiniteListing TargetNode :=
  { values := [.origin, .successor]
    complete := by
      intro identity
      cases identity
      · exact List.Mem.head [TargetNode.successor]
      · exact
          List.Mem.tail TargetNode.origin
            (List.Mem.head []) }

/--
The executable decision succeeds even though source and target relation values
have different types.
-/
theorem independent_decision_is_aligned :
    (decideAlignmentFromListings
      independentContext sourceNodeListing targetNodeListing).isAligned = true :=
  decideAlignmentFromListings_isAligned_of_alignment
    independentContext
    sourceNodeListing
    targetNodeListing
    independentConstitutiveAlignment

/-- A singleton source cannot admit exact alignment with an empty target. -/
def unitEmptyIndependentContext :
    IndependentRelationalContext Unit Empty Bool TargetObservation :=
  { sourceRelation := fun _ _ => true
    targetRelation := fun first _ => nomatch first
    sourceSeparates := by
      intro first second _
      cases first
      cases second
      rfl
    targetSeparates := by
      intro first _ _
      exact nomatch first }

def unitListing : FiniteListing Unit :=
  { values := [()]
    complete := by
      intro identity
      cases identity
      exact List.Mem.head [] }

def emptyListing : FiniteListing Empty :=
  { values := []
    complete := by
      intro identity
      exact nomatch identity }

theorem unitEmptyIndependent_no_alignment
    (alignment :
      IndependentConstitutiveAlignment unitEmptyIndependentContext) : False :=
  nomatch alignment.initial.transport.forward ()

theorem independent_decision_can_refute :
    (decideAlignmentFromListings
      unitEmptyIndependentContext unitListing emptyListing).isAligned = false :=
  decideAlignmentFromListings_isAligned_false_of_refutation
    unitEmptyIndependentContext
    unitListing
    emptyListing
    unitEmptyIndependent_no_alignment

end Alignment.Tests.FiniteIndependentAlignmentDecisionRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms Alignment.Tests.FiniteIndependentAlignmentDecisionRegression.sourceNodeListing
#print axioms Alignment.Tests.FiniteIndependentAlignmentDecisionRegression.targetNodeListing
#print axioms Alignment.Tests.FiniteIndependentAlignmentDecisionRegression.independent_decision_is_aligned
#print axioms Alignment.Tests.FiniteIndependentAlignmentDecisionRegression.unitEmptyIndependentContext
#print axioms Alignment.Tests.FiniteIndependentAlignmentDecisionRegression.unitListing
#print axioms Alignment.Tests.FiniteIndependentAlignmentDecisionRegression.emptyListing
#print axioms Alignment.Tests.FiniteIndependentAlignmentDecisionRegression.unitEmptyIndependent_no_alignment
#print axioms Alignment.Tests.FiniteIndependentAlignmentDecisionRegression.independent_decision_can_refute
/- AXIOM_AUDIT_END -/
