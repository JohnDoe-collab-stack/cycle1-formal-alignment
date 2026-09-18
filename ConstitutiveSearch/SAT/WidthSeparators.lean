import ConstitutiveSearch.SAT.ExplicitFamilyRelationCosts

/-!
# Width separators for the hardened SAT relation engine

This module builds a parametric negative benchmark for the announced global
flip search.

The root formula is empty.  For every variable i we generate one true child of
the same root.  All residual formulas are therefore identical and empty, while
the constituted histories record different variable names.

A polarity flip may change one recorded Boolean value, but it never changes the
recorded variable name.  Hence two children generated on distinct variables
remain unresolved by every fixed global flip search.

The resulting frontier family has arbitrary search-relative irreducible width.
This does not claim intrinsic hardness; it is a separator for the declared
relation engine.
-/

namespace ConstitutiveSearch
namespace SAT

abbrev isolatedRoot :
    GeneratedStructuralBranchContext ([] : Cnf) :=
  GeneratedStructuralBranchContext.root []

theorem isolatedRootFresh
    (var : Var) :
    StructuralDecisionsAvoid
      var
      isolatedRoot.context.decisions :=
  True.intro

/-- One generated child carrying a unique one-decision provenance. -/
def isolatedChild
    (var : Var) :
    GeneratedStructuralBranchContext ([] : Cnf) :=
  GeneratedStructuralBranchContext.child
    isolatedRoot
    var
    true
    (isolatedRootFresh var)

/-- Distinct isolated children record distinct structural histories. -/
theorem isolatedChild_decisions_ne
    {leftVar rightVar : Var}
    (different : leftVar ≠ rightVar) :
    (isolatedChild leftVar).context.decisions ≠
      (isolatedChild rightVar).context.decisions := by
  intro equal
  have headEqual :
      ({ var := leftVar, value := true } :
        StructuralBranchDecision) =
      { var := rightVar, value := true } := by
    injection equal with headEqual tailEqual
  have varEqual :
      leftVar = rightVar :=
    congrArg StructuralBranchDecision.var headEqual
  exact different varEqual

/--
Flipping any selected variable never changes the variable name stored in one
isolated one-step history.
-/
theorem isolatedChild_decisions_ne_flipped
    (anchor : Var)
    {sourceVar targetVar : Var}
    (different : sourceVar ≠ targetVar) :
    (isolatedChild targetVar).context.decisions ≠
      flipStructuralDecisionsAt
        anchor
        (isolatedChild sourceVar).context.decisions := by
  intro equal
  have headEqual :
      ({ var := targetVar, value := true } :
        StructuralBranchDecision) =
      StructuralBranchDecision.flipAt
        anchor
        { var := sourceVar, value := true } := by
    injection equal with headEqual tailEqual
  have varEqual :
      targetVar = sourceVar := by
    have projected :=
      congrArg StructuralBranchDecision.var headEqual
    unfold StructuralBranchDecision.flipAt at projected
    by_cases selected : sourceVar = anchor
    · rw [if_pos selected] at projected
      exact projected
    · rw [if_neg selected] at projected
      exact projected
  exact different varEqual.symm

/-- Direct global flip search fails between distinct isolated children. -/
theorem isolatedChild_flipSearch_none
    (anchor : Var)
    {sourceVar targetVar : Var}
    (different : sourceVar ≠ targetVar) :
    (generatedStructuralFlipAtSearch ([] : Cnf) anchor).find
        (isolatedChild sourceVar)
        (isolatedChild targetVar) =
      none := by
  unfold generatedStructuralFlipAtSearch
  change
    (if formulaExact :
        ([] : Cnf) =
          Cnf.flipAt anchor [] then
      if decisionsExact :
          (isolatedChild targetVar).context.decisions =
            flipStructuralDecisionsAt
              anchor
              (isolatedChild sourceVar).context.decisions then
        some
          { formulaExact := formulaExact
            decisionsExact := decisionsExact }
      else
        none
    else
      none) =
    none
  rw [dif_pos rfl]
  rw [
    dif_neg
      (isolatedChild_decisions_ne_flipped
        anchor
        different)
  ]

/-- Frontier of isolated one-step children, with variables count-1 down to 0. -/
def isolatedFrontier : Nat →
    List (GeneratedStructuralBranchContext ([] : Cnf))
  | 0 =>
      []
  | count + 1 =>
      isolatedChild count ::
        isolatedFrontier count

/-- The separator frontier has exactly the requested width. -/
theorem isolatedFrontier_length
    (count : Nat) :
    (isolatedFrontier count).length =
      count := by
  induction count with
  | zero =>
      rfl
  | succ count inductionHypothesis =>
      change
        Nat.succ (isolatedFrontier count).length =
          Nat.succ count
      exact
        congrArg Nat.succ inductionHypothesis

/--
A child whose variable is at least count is unresolved against every child in
the smaller isolated frontier.
-/
theorem isolatedChild_unresolved_with_frontier
    (anchor sourceVar count : Nat)
    (countLeSource : count ≤ sourceVar) :
    ∀ other,
      other ∈ isolatedFrontier count →
        (generatedStructuralFlipAtSearch ([] : Cnf) anchor).find
              (isolatedChild sourceVar)
              other =
            none ∧
          (generatedStructuralFlipAtSearch ([] : Cnf) anchor).find
              other
              (isolatedChild sourceVar) =
            none := by
  induction count with
  | zero =>
      intro other member
      cases member
  | succ count inductionHypothesis =>
      intro other member
      cases member with
      | head =>
          have countLtSource :
              count < sourceVar :=
            Nat.lt_of_lt_of_le
              (Nat.lt_succ_self count)
              countLeSource
          have sourceDifferent :
              sourceVar ≠ count :=
            Nat.ne_of_gt countLtSource
          exact
            ⟨isolatedChild_flipSearch_none
                anchor
                sourceDifferent,
              isolatedChild_flipSearch_none
                anchor
                sourceDifferent.symm⟩
      | tail _ tailMember =>
          exact
            inductionHypothesis
              (Nat.le_trans
                (Nat.le_succ count)
                countLeSource)
              other
              tailMember

/--
For every n and every fixed flip variable, there is a SAT frontier of width n
that is irreducible relative to that exact search engine.
-/
theorem isolatedFrontier_searchIrreducible
    (anchor count : Nat) :
    SearchIrreducible
      (generatedStructuralFlipAtSearch ([] : Cnf) anchor)
      (isolatedFrontier count) := by
  induction count with
  | zero =>
      exact
        SearchIrreducible.nil
          (generatedStructuralFlipAtSearch
            ([] : Cnf)
            anchor)
  | succ count inductionHypothesis =>
      constructor
      · intro other member
        exact
          isolatedChild_unresolved_with_frontier
            anchor
            count
            count
            (Nat.le_refl count)
            other
            member
      · exact inductionHypothesis

/-- Concrete all-true continuation for one isolated child. -/
def isolatedChildContinuation
    (var : Var) :
    GeneratedStructuralBranchContinuation
      (isolatedChild var) :=
  ⟨fun _ => true,
    ⟨rfl, True.intro⟩⟩

/-- The concrete isolated continuation is accepted by the empty CNF. -/
theorem isolatedChildContinuation_accept
    (var : Var) :
    GeneratedStructuralBranchAccept
      (isolatedChild var)
      (isolatedChildContinuation var) :=
  Satisfies.nil

/-- Every isolated child is structurally viable over the empty CNF. -/
theorem isolatedChild_viable
    (var : Var) :
    (generatedStructuralBranchSystem ([] : Cnf)).Viable
      (isolatedChild var) :=
  ⟨isolatedChildContinuation var,
    isolatedChildContinuation_accept var⟩

/-- Every nonempty separator frontier is viable. -/
theorem isolatedFrontier_viable
    (count : Nat) :
    FrontierViable
      (generatedStructuralBranchSystem ([] : Cnf))
      (isolatedFrontier (count + 1)) := by
  exact
    ⟨.head (isolatedChildContinuation count),
      isolatedChildContinuation_accept count⟩

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.isolatedRoot
#print axioms ConstitutiveSearch.SAT.isolatedRootFresh
#print axioms ConstitutiveSearch.SAT.isolatedChild
#print axioms ConstitutiveSearch.SAT.isolatedChild_decisions_ne
#print axioms ConstitutiveSearch.SAT.isolatedChild_decisions_ne_flipped
#print axioms ConstitutiveSearch.SAT.isolatedChild_flipSearch_none
#print axioms ConstitutiveSearch.SAT.isolatedFrontier
#print axioms ConstitutiveSearch.SAT.isolatedFrontier_length
#print axioms ConstitutiveSearch.SAT.isolatedChild_unresolved_with_frontier
#print axioms ConstitutiveSearch.SAT.isolatedFrontier_searchIrreducible
#print axioms ConstitutiveSearch.SAT.isolatedChildContinuation
#print axioms ConstitutiveSearch.SAT.isolatedChildContinuation_accept
#print axioms ConstitutiveSearch.SAT.isolatedChild_viable
#print axioms ConstitutiveSearch.SAT.isolatedFrontier_viable
/- AXIOM_AUDIT_END -/
