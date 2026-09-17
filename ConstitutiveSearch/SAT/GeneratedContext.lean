import ConstitutiveSearch.FrontierPreservation
import ConstitutiveSearch.SAT.BranchContextTransport

/-!
# Generated SAT branch contexts

`BranchContext` is intentionally abstract and can be supplied independently of
any search history.  This module isolates the smaller class of contexts that are
actually generated from one SAT root by successive fresh Boolean decisions.

Generation is proof-relevant.  A witness records the complete parent chain, the
selected variable and value at every step, and freshness of each new decision.
Carrier reconstruction is derived recursively from that generation witness.  It
is not stored as an arbitrary additional field.

The resulting `GeneratedBranchContext rootFormula` is one uniform state type.
Contexts produced from different parents can therefore coexist in one finite
frontier without forgetting their constitutive provenance.
-/

namespace ConstitutiveSearch
namespace SAT

/--
Proof-relevant witness that a concrete `BranchContext` was generated from one
fixed root formula by successive fresh branch decisions.
-/
inductive GeneratedFrom
    (rootFormula : Cnf) : BranchContext → Type 1 where
  | root : GeneratedFrom rootFormula (rootContext rootFormula)
  | child
      {parent : BranchContext}
      (parentGenerated : GeneratedFrom rootFormula parent)
      (var : Var)
      (value : Bool)
      (fresh : DecisionsAvoid var parent.decisions) :
      GeneratedFrom rootFormula (childContext parent var value)

namespace GeneratedFrom

/-- Carrier reconstruction is inherited along the generated parent chain. -/
def reconstruction
    {rootFormula : Cnf}
    {context : BranchContext} :
    GeneratedFrom rootFormula context →
      BranchContextReconstruction context
  | .root =>
      rootContextReconstruction rootFormula
  | .child parentGenerated var value _fresh =>
      childContextReconstruction
        (reconstruction parentGenerated)
        var value

/-- Number of constitutive branch decisions in one generation witness. -/
def depth
    {rootFormula : Cnf}
    {context : BranchContext} :
    GeneratedFrom rootFormula context → Nat
  | .root => 0
  | .child parentGenerated _var _value _fresh =>
      depth parentGenerated + 1

end GeneratedFrom

/--
One globally typed SAT search state together with exact provenance from the
fixed root formula.
-/
structure GeneratedBranchContext (rootFormula : Cnf) : Type 1 where
  context : BranchContext
  generated : GeneratedFrom rootFormula context

namespace GeneratedBranchContext

/-- Canonical generated root state. -/
def root (formula : Cnf) : GeneratedBranchContext formula :=
  { context := rootContext formula
    generated := .root }

/--
Generate one legal child.  Freshness is a property of the transition itself and
is recorded in the generation witness.
-/
def child
    {rootFormula : Cnf}
    (parent : GeneratedBranchContext rootFormula)
    (var : Var)
    (value : Bool)
    (fresh : DecisionsAvoid var parent.context.decisions) :
    GeneratedBranchContext rootFormula :=
  { context := childContext parent.context var value
    generated := .child parent.generated var value fresh }

/-- Reconstruction is derived from generation provenance. -/
def reconstruction
    {rootFormula : Cnf}
    (state : GeneratedBranchContext rootFormula) :
    BranchContextReconstruction state.context :=
  state.generated.reconstruction

/-- Structural generation depth. -/
def depth
    {rootFormula : Cnf}
    (state : GeneratedBranchContext rootFormula) : Nat :=
  state.generated.depth

/-- The root has structural generation depth zero. -/
theorem root_depth (formula : Cnf) :
    (root formula).depth = 0 :=
  rfl

/-- Every generated child has successor generation depth. -/
theorem child_depth
    {rootFormula : Cnf}
    (parent : GeneratedBranchContext rootFormula)
    (var : Var)
    (value : Bool)
    (fresh : DecisionsAvoid var parent.context.decisions) :
    (child parent var value fresh).depth = parent.depth + 1 :=
  rfl

/-- The newest generated decision is present at the head of child provenance. -/
theorem child_decisions
    {rootFormula : Cnf}
    (parent : GeneratedBranchContext rootFormula)
    (var : Var)
    (value : Bool)
    (fresh : DecisionsAvoid var parent.context.decisions) :
    (child parent var value fresh).context.decisions =
      { var := var, value := value } :: parent.context.decisions :=
  rfl

end GeneratedBranchContext

/-- Completion family indexed by globally generated SAT states. -/
def GeneratedBranchCompletion
    {rootFormula : Cnf}
    (state : GeneratedBranchContext rootFormula) : Type :=
  state.context.Carrier

/--
A fresh decision gives an exact split directly in the uniform generated-state
type.  The underlying branch-context split is re-exposed field by field so that
no equality between the two different state index types is required.
-/
def generatedSplit
    {rootFormula : Cnf}
    (parent : GeneratedBranchContext rootFormula)
    (var : Var)
    (fresh : DecisionsAvoid var parent.context.decisions) :
    ExactBinarySplit
      GeneratedBranchCompletion
      parent
      (GeneratedBranchContext.child parent var false fresh)
      (GeneratedBranchContext.child parent var true fresh) :=
  let splitter := contextSplit parent.context var
  { split := splitter.split
    merge := splitter.merge
    splitMerge := splitter.splitMerge
    mergeSplit := splitter.mergeSplit }

/--
The exact generated split preserves frontier completion existence in both
directions.
-/
def generatedExpansion
    {rootFormula : Cnf}
    (parent : GeneratedBranchContext rootFormula)
    (var : Var)
    (fresh : DecisionsAvoid var parent.context.decisions) :
    FrontierPreservation
      GeneratedBranchCompletion
      [parent]
      [ GeneratedBranchContext.child parent var false fresh,
        GeneratedBranchContext.child parent var true fresh ] :=
  FrontierPreservation.expandHead
    (generatedSplit parent var fresh)

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.GeneratedFrom
#print axioms ConstitutiveSearch.SAT.GeneratedFrom.reconstruction
#print axioms ConstitutiveSearch.SAT.GeneratedFrom.depth
#print axioms ConstitutiveSearch.SAT.GeneratedBranchContext
#print axioms ConstitutiveSearch.SAT.GeneratedBranchContext.root
#print axioms ConstitutiveSearch.SAT.GeneratedBranchContext.child
#print axioms ConstitutiveSearch.SAT.GeneratedBranchContext.reconstruction
#print axioms ConstitutiveSearch.SAT.GeneratedBranchContext.depth
#print axioms ConstitutiveSearch.SAT.GeneratedBranchCompletion
#print axioms ConstitutiveSearch.SAT.generatedSplit
#print axioms ConstitutiveSearch.SAT.generatedExpansion
/- AXIOM_AUDIT_END -/
