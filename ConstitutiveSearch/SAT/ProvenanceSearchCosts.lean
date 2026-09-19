import Init.Omega
import ConstitutiveSearch.SAT.TrajectoryDerivedClosure

/-!
# Internal cost of provenance-restricted primitive search

provenanceStructuralFlipSearch is one RelationSearch interface, but one call to
its find function may test several trajectory variables before succeeding.

This module exposes that internal control-flow cost instead of treating one
top-level provenance query as one generatedStructuralFlipAtSearch query.

For a provenance list vars:
* the empty search performs zero variable-level primitive attempts;
* a nonempty search performs one attempt at the head;
* it recurses only when that attempt returns none.

Therefore every top-level provenance query performs at most vars.length
variable-level generated-structural-flip searches.

This is a source-level query count.  Representation and machine costs remain
separate layers.
-/

namespace ConstitutiveSearch
namespace SAT

/--
Exact number of variable-level generatedStructuralFlipAtSearch attempts made by
one provenanceStructuralFlipSearch query.
-/
def provenanceStructuralFlipSearchVariableQueries
    (rootFormula : Cnf) :
    (vars : List Var) →
      GeneratedStructuralBranchContext rootFormula →
      GeneratedStructuralBranchContext rootFormula →
      Nat
  | [], _source, _target =>
      0
  | var :: rest, source, target =>
      match
        (generatedStructuralFlipAtSearch
          rootFormula
          var).find
            source
            target with
      | some _ =>
          1
      | none =>
          1 +
            provenanceStructuralFlipSearchVariableQueries
              rootFormula
              rest
              source
              target

/--
Every provenance query inspects at most one generated flip search per announced
provenance variable.
-/
theorem provenanceStructuralFlipSearchVariableQueries_le_length
    (rootFormula : Cnf) :
    ∀ (vars : List Var)
      (source target :
        GeneratedStructuralBranchContext
          rootFormula),
      provenanceStructuralFlipSearchVariableQueries
          rootFormula
          vars
          source
          target ≤
        vars.length := by
  intro vars
  induction vars with
  | nil =>
      intro source target
      rfl
  | cons var rest inductionHypothesis =>
      intro source target
      cases found :
          (generatedStructuralFlipAtSearch
            rootFormula
            var).find
              source
              target with
      | some relation =>
          simp only [
            provenanceStructuralFlipSearchVariableQueries,
            found,
            List.length_cons
          ]
          exact Nat.succ_le_succ (Nat.zero_le _)
      | none =>
          simp only [
            provenanceStructuralFlipSearchVariableQueries,
            found,
            List.length_cons
          ]
          exact
            Nat.add_le_add_left
              (inductionHypothesis
                source
                target)
              1

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.provenanceStructuralFlipSearchVariableQueries
#print axioms ConstitutiveSearch.SAT.provenanceStructuralFlipSearchVariableQueries_le_length
/- AXIOM_AUDIT_END -/
