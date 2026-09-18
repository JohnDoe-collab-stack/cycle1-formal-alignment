import ConstitutiveSearch.DynamicRelationSearch
import ConstitutiveSearch.SAT.StructuralGlobalContextRelation

/-!
# Dynamic relations unlocked by generated SAT structure

A generated split anchor is not a semantic oracle or an external Boolean flag.
It is constructive data consisting of a generated SAT parent, a fresh variable,
and therefore the exact pair of children produced by the certified structural
split.

Relation reconstruction can be gated by such constituted data.  Before the
anchor is part of the current constitutive state, the gated search returns no
witness.  Once the same certified split data has been constituted, the search
may expose structural transports justified by that split.
-/

namespace ConstitutiveSearch
namespace SAT

/-- Constructive certificate of one legal generated SAT split. -/
structure GeneratedSplitAnchor
    (rootFormula : Cnf) where
  parent : GeneratedStructuralBranchContext rootFormula
  var : Var
  fresh :
    StructuralDecisionsAvoid
      var
      parent.context.decisions

namespace GeneratedSplitAnchor

/-- False child determined by the certified split. -/
def falseChild
    {rootFormula : Cnf}
    (anchor : GeneratedSplitAnchor rootFormula) :
    GeneratedStructuralBranchContext rootFormula :=
  GeneratedStructuralBranchContext.child
    anchor.parent
    anchor.var
    false
    anchor.fresh

/-- True child determined by the certified split. -/
def trueChild
    {rootFormula : Cnf}
    (anchor : GeneratedSplitAnchor rootFormula) :
    GeneratedStructuralBranchContext rootFormula :=
  GeneratedStructuralBranchContext.child
    anchor.parent
    anchor.var
    true
    anchor.fresh

/-- Exact frontier created by the split certificate. -/
def frontier
    {rootFormula : Cnf}
    (anchor : GeneratedSplitAnchor rootFormula) :
    List (GeneratedStructuralBranchContext rootFormula) :=
  [anchor.falseChild, anchor.trueChild]

/-- The anchor reconstructs the certified expansion that created its children. -/
def expansion
    {rootFormula : Cnf}
    (anchor : GeneratedSplitAnchor rootFormula) :
    AcceptedFrontierPreservation
      (generatedStructuralBranchSystem rootFormula)
      [anchor.parent]
      anchor.frontier :=
  generatedStructuralExpansion
    anchor.parent
    anchor.var
    anchor.fresh

end GeneratedSplitAnchor

/-- Constitution carried by the path: no recorded split yet, or one certified split. -/
abbrev GeneratedSplitConstitution
    (rootFormula : Cnf) :=
  Option (GeneratedSplitAnchor rootFormula)

/--
A dynamic relation made available by the split currently constituted in the
path.  Its semantic action is still the hardened global structural flip.
-/
structure ConstitutedSplitFlipRelation
    (rootFormula : Cnf)
    (current :
      ConstitutiveState
        (generatedStructuralBranchSystem rootFormula)
        (GeneratedSplitConstitution rootFormula))
    (source target : GeneratedStructuralBranchContext rootFormula) : Type where
  anchor : GeneratedSplitAnchor rootFormula
  anchorExact :
    current.constitution = some anchor
  flip :
    GeneratedStructuralFlipAtRelation
      anchor.var
      source
      target

/-- A constituted split relation acts by the already certified hardened flip. -/
def constitutedSplitFlipAction
    (rootFormula : Cnf) :
    ConstitutiveRelationalAction
      (generatedStructuralBranchSystem rootFormula)
      (GeneratedSplitConstitution rootFormula)
      (ConstitutedSplitFlipRelation rootFormula) :=
  { toTransport := fun relation =>
      relation.flip.toAcceptingTransport }

/--
Executable dynamic search.  With no constituted split anchor it returns no
relation.  With an anchor it delegates to the exact global flip search at the
anchor's generated variable.
-/
def constitutedSplitFlipSearch
    (rootFormula : Cnf) :
    ConstitutiveRelationSearch
      (generatedStructuralBranchSystem rootFormula)
      (GeneratedSplitConstitution rootFormula)
      (ConstitutedSplitFlipRelation rootFormula) :=
  { find := fun current source target =>
      match anchorExact : current.constitution with
      | none => none
      | some anchor =>
          match
            (generatedStructuralFlipAtSearch
              rootFormula
              anchor.var).find source target with
          | none => none
          | some flip =>
              some
                { anchor := anchor
                  anchorExact := anchorExact
                  flip := flip } }

/-- Normalize a frontier using exactly the generated split currently constituted. -/
def normalizeWithConstitutedSplit
    (rootFormula : Cnf)
    (current :
      ConstitutiveState
        (generatedStructuralBranchSystem rootFormula)
        (GeneratedSplitConstitution rootFormula))
    (frontier :
      List (GeneratedStructuralBranchContext rootFormula)) :
    AcceptedIrreducibleFrontierReduction
      ((constitutedSplitFlipSearch rootFormula).freeze current)
      frontier :=
  (constitutedSplitFlipSearch rootFormula).normalizeAt
    (constitutedSplitFlipAction rootFormula)
    current
    frontier

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.GeneratedSplitAnchor
#print axioms ConstitutiveSearch.SAT.GeneratedSplitAnchor.falseChild
#print axioms ConstitutiveSearch.SAT.GeneratedSplitAnchor.trueChild
#print axioms ConstitutiveSearch.SAT.GeneratedSplitAnchor.frontier
#print axioms ConstitutiveSearch.SAT.GeneratedSplitAnchor.expansion
#print axioms ConstitutiveSearch.SAT.GeneratedSplitConstitution
#print axioms ConstitutiveSearch.SAT.ConstitutedSplitFlipRelation
#print axioms ConstitutiveSearch.SAT.constitutedSplitFlipAction
#print axioms ConstitutiveSearch.SAT.constitutedSplitFlipSearch
#print axioms ConstitutiveSearch.SAT.normalizeWithConstitutedSplit
/- AXIOM_AUDIT_END -/
