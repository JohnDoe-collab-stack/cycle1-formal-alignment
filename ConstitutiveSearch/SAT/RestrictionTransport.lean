import ConstitutiveSearch.SAT.BinaryBranch

/-!
# SAT branch residuals and continuation transports

This module connects the exact Boolean branch split to a syntactic residual CNF
without introducing a satisfiability query.

For one fixed variable value, clauses already satisfied by the corresponding
literal are deleted. Other clauses are kept unchanged. The residual therefore
remains an order-preserving sub-CNF of the source.

The residual CNF, its weakening witness, and the reconstruction of original
satisfaction are built together by one structural induction. This prevents a
later proof layer from silently strengthening the residual construction.

A branch completion transports to the residual by keeping the same assignment
and restricting its satisfaction proof. Conversely, a residual completion that
retains the fixed variable value reconstructs satisfaction of every deleted
clause and therefore a completion of the original branch.
-/

namespace ConstitutiveSearch
namespace SAT

namespace Literal

/-- The literal made true by assigning `value` to `var`. -/
def forValue (var : Var) : Bool → Literal
  | false => .negative var
  | true => .positive var

/-- The branch literal evaluates to true under the fixed branch value. -/
theorem eval_forValue_true
    (assignment : Assignment)
    (var : Var)
    (value : Bool)
    (valueExact : assignment var = value) :
    (forValue var value).eval assignment = true := by
  cases value with
  | false =>
      dsimp [forValue, Literal.eval]
      rw [valueExact]
      rfl
  | true =>
      dsimp [forValue, Literal.eval]
      exact valueExact

end Literal

namespace Clause

/-- Executable occurrence check for a literal inside one clause. -/
def containsLiteral (target : Literal) : Clause → Bool
  | [] => false
  | literal :: rest =>
      if literal = target then true else containsLiteral target rest

/--
If a clause contains a literal already known to evaluate to true, the complete
clause evaluates to true.
-/
theorem eval_true_of_containsLiteral
    (assignment : Assignment)
    (target : Literal)
    (targetTrue : target.eval assignment = true) :
    (clause : Clause) →
      containsLiteral target clause = true →
        eval assignment clause = true
  | [], contains => by
      cases contains
  | literal :: rest, contains => by
      by_cases literalExact : literal = target
      · subst literal
        dsimp [eval]
        rw [targetTrue]
        rfl
      · have tailContains : containsLiteral target rest = true := by
          rw [containsLiteral, if_neg literalExact] at contains
          exact contains
        have restTrue :=
          eval_true_of_containsLiteral
            assignment target targetTrue rest tailContains
        dsimp [eval]
        rw [restTrue]
        cases literal.eval assignment <;> rfl

end Clause

/--
Positive result of one branch reduction. The residual syntax, forward weakening,
and reverse satisfaction reconstruction are constituted together.
-/
structure BranchReductionResult
    (formula : Cnf)
    (var : Var)
    (value : Bool) where
  residual : Cnf
  weakening : CnfWeakening formula residual
  restore :
    (assignment : Assignment) →
      assignment var = value →
        Satisfies assignment residual →
          Satisfies assignment formula

/--
Compute the branch residual, weakening witness, and reconstruction by structural
induction over the CNF. The recursive result for the tail is supplied directly
by the list recursor and is executable data.
-/
def branchReduction
    (formula : Cnf)
    (var : Var)
    (value : Bool) :
    BranchReductionResult formula var value := by
  induction formula with
  | nil =>
      exact
        { residual := []
          weakening := .done
          restore := fun _assignment _valueExact _residualSatisfaction => .nil }
  | cons clause rest tail =>
      cases hitEq :
          Clause.containsLiteral (Literal.forValue var value) clause with
      | true =>
          exact
            { residual := tail.residual
              weakening := .drop clause tail.weakening
              restore := fun assignment valueExact residualSatisfaction =>
                let branchLiteralTrue :
                    (Literal.forValue var value).eval assignment = true :=
                  Literal.eval_forValue_true assignment var value valueExact
                let headSatisfaction : Clause.eval assignment clause = true :=
                  Clause.eval_true_of_containsLiteral
                    assignment
                    (Literal.forValue var value)
                    branchLiteralTrue
                    clause
                    hitEq
                .cons headSatisfaction
                  (tail.restore assignment valueExact residualSatisfaction) }
      | false =>
          exact
            { residual := clause :: tail.residual
              weakening := .keep clause tail.weakening
              restore := fun assignment valueExact residualSatisfaction =>
                match residualSatisfaction with
                | .cons headSatisfaction tailSatisfaction =>
                    .cons headSatisfaction
                      (tail.restore assignment valueExact tailSatisfaction) }

/-- Residual CNF obtained after deleting clauses satisfied by the fixed bit. -/
def branchResidual
    (formula : Cnf)
    (var : Var)
    (value : Bool) : Cnf :=
  (branchReduction formula var value).residual

/-- The residual is constructively a weakening of the original CNF. -/
def branchWeakening
    (formula : Cnf)
    (var : Var)
    (value : Bool) :
    CnfWeakening formula (branchResidual formula var value) :=
  (branchReduction formula var value).weakening

/--
Residual satisfaction plus the retained branch value reconstructs satisfaction
of the original CNF.
-/
theorem restoreSatisfaction
    (formula : Cnf)
    (assignment : Assignment)
    (var : Var)
    (value : Bool)
    (valueExact : assignment var = value) :
    Satisfies assignment (branchResidual formula var value) →
      Satisfies assignment formula :=
  (branchReduction formula var value).restore assignment valueExact

/-- A branch-indexed completion exposes the indexed variable value exactly. -/
theorem indexedCompletion_valueExact
    {formula : Cnf}
    {var : Var}
    {value : Bool}
    (completion : ValueIndexedCompletion formula var value) :
    completion.underlying.1 var = value := by
  cases completion with
  | ofCompletion _raw =>
      rfl

/--
A residual completion retains the assignment, its branch provenance, and
satisfaction of the residual CNF.
-/
structure ResidualBranchCompletion
    (formula : Cnf)
    (var : Var)
    (value : Bool) where
  assignment : Assignment
  valueExact : assignment var = value
  residualSatisfaction :
    Satisfies assignment (branchResidual formula var value)

/-- Transport a branch completion to its residual completion. -/
def branchToResidual
    {formula : Cnf}
    {var : Var}
    {value : Bool} :
    ValueIndexedCompletion formula var value →
      ResidualBranchCompletion formula var value :=
  fun completion =>
    { assignment := completion.underlying.1
      valueExact := indexedCompletion_valueExact completion
      residualSatisfaction :=
        (branchWeakening formula var value).preservesSatisfaction
          completion.underlying.2 }

/-- Reconstruct the original branch completion from its residual data. -/
def residualToBranch
    {formula : Cnf}
    {var : Var}
    {value : Bool}
    (residual : ResidualBranchCompletion formula var value) :
    ValueIndexedCompletion formula var value :=
  let originalSatisfaction : Satisfies residual.assignment formula :=
    restoreSatisfaction
      formula residual.assignment var value
      residual.valueExact residual.residualSatisfaction
  let raw : Completion formula :=
    ⟨residual.assignment, originalSatisfaction⟩
  let indexed :
      ValueIndexedCompletion formula var (residual.assignment var) :=
    ValueIndexedCompletion.ofCompletion raw
  Eq.mp
    (congrArg (ValueIndexedCompletion formula var) residual.valueExact)
    indexed

/-- Two views used to expose the branch/residual maps through the generic transport interface. -/
inductive RestrictionView where
  | branch
  | residual

/-- Completion family for one fixed branch and its residual view. -/
def RestrictionCompletion
    (formula : Cnf)
    (var : Var)
    (value : Bool) : RestrictionView → Type
  | .branch => ValueIndexedCompletion formula var value
  | .residual => ResidualBranchCompletion formula var value

/-- Generic continuation transport from exact branch data to residual data. -/
def branchToResidualTransport
    (formula : Cnf)
    (var : Var)
    (value : Bool) :
    ContinuationTransport
      (RestrictionCompletion formula var value)
      .branch
      .residual :=
  { map := branchToResidual }

/-- Generic continuation transport from residual data back to the original branch. -/
def residualToBranchTransport
    (formula : Cnf)
    (var : Var)
    (value : Bool) :
    ContinuationTransport
      (RestrictionCompletion formula var value)
      .residual
      .branch :=
  { map := residualToBranch }

/-- Branch and residual views have equivalent positive completion existence. -/
theorem branch_residual_nonempty_iff
    (formula : Cnf)
    (var : Var)
    (value : Bool) :
    Nonempty (ValueIndexedCompletion formula var value) ↔
      Nonempty (ResidualBranchCompletion formula var value) := by
  constructor
  · exact
      (branchToResidualTransport formula var value).preservesExistence
  · exact
      (residualToBranchTransport formula var value).preservesExistence

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.Literal.forValue
#print axioms ConstitutiveSearch.SAT.Literal.eval_forValue_true
#print axioms ConstitutiveSearch.SAT.Clause.containsLiteral
#print axioms ConstitutiveSearch.SAT.Clause.eval_true_of_containsLiteral
#print axioms ConstitutiveSearch.SAT.BranchReductionResult
#print axioms ConstitutiveSearch.SAT.branchReduction
#print axioms ConstitutiveSearch.SAT.branchResidual
#print axioms ConstitutiveSearch.SAT.branchWeakening
#print axioms ConstitutiveSearch.SAT.restoreSatisfaction
#print axioms ConstitutiveSearch.SAT.ResidualBranchCompletion
#print axioms ConstitutiveSearch.SAT.branchToResidual
#print axioms ConstitutiveSearch.SAT.residualToBranch
#print axioms ConstitutiveSearch.SAT.branchToResidualTransport
#print axioms ConstitutiveSearch.SAT.residualToBranchTransport
#print axioms ConstitutiveSearch.SAT.branch_residual_nonempty_iff
/- AXIOM_AUDIT_END -/