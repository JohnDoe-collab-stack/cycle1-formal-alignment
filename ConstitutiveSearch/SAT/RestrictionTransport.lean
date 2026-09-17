import ConstitutiveSearch.SAT.BinaryBranch

/-!
# SAT branch residuals and continuation transports

This module connects the exact Boolean branch split to a syntactic residual CNF
without introducing a satisfiability query.

For one fixed variable value, clauses already satisfied by the corresponding
literal are deleted.  Other clauses are kept unchanged.  The residual therefore
remains an order-preserving sub-CNF of the source.

A branch completion transports to the residual by keeping the same assignment
and restricting its satisfaction proof.  Conversely, a residual completion
that explicitly retains the fixed variable value reconstructs satisfaction of
every deleted clause and therefore a completion of the original branch.

The fixed-value witness is essential on the reverse direction.  A raw residual
CNF completion without this branch provenance would be too weak and could
introduce assignments that do not represent the branch from which the residual
was constituted.
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
      change !(assignment var) = true
      rw [valueExact]
      rfl
  | true =>
      change assignment var = true
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
        change target.eval assignment || eval assignment rest = true
        rw [targetTrue]
        rfl
      · change
          (if literal = target then true else containsLiteral target rest) = true
            at contains
        rw [if_neg literalExact] at contains
        have restTrue :=
          eval_true_of_containsLiteral assignment target targetTrue rest contains
        change literal.eval assignment || eval assignment rest = true
        rw [restTrue]
        cases literal.eval assignment <;> rfl

end Clause

/--
Compute one branch residual and its clause-deletion witness simultaneously.
This keeps the executable residual and the constructive weakening proof in one
recursion.
-/
def branchReduction
    (var : Var)
    (value : Bool) :
    (formula : Cnf) →
      Sigma fun residual : Cnf => CnfWeakening formula residual
  | [] => ⟨[], .done⟩
  | clause :: rest =>
      let tail := branchReduction var value rest
      match Clause.containsLiteral (Literal.forValue var value) clause with
      | true =>
          ⟨tail.1, .drop clause tail.2⟩
      | false =>
          ⟨clause :: tail.1, .keep clause tail.2⟩

/-- Residual CNF obtained after deleting clauses satisfied by the fixed bit. -/
def branchResidual
    (formula : Cnf)
    (var : Var)
    (value : Bool) : Cnf :=
  (branchReduction var value formula).1

/-- The residual is constructively a weakening of the original CNF. -/
def branchWeakening
    (formula : Cnf)
    (var : Var)
    (value : Bool) :
    CnfWeakening formula (branchResidual formula var value) :=
  (branchReduction var value formula).2

/-- Residual equation when the branch literal satisfies the head clause. -/
theorem branchResidual_cons_hit
    (clause : Clause)
    (rest : Cnf)
    (var : Var)
    (value : Bool)
    (hit :
      Clause.containsLiteral (Literal.forValue var value) clause = true) :
    branchResidual (clause :: rest) var value =
      branchResidual rest var value := by
  simp [branchResidual, branchReduction, hit]

/-- Residual equation when the branch literal does not satisfy the head clause. -/
theorem branchResidual_cons_miss
    (clause : Clause)
    (rest : Cnf)
    (var : Var)
    (value : Bool)
    (miss :
      Clause.containsLiteral (Literal.forValue var value) clause = false) :
    branchResidual (clause :: rest) var value =
      clause :: branchResidual rest var value := by
  simp [branchResidual, branchReduction, miss]

/--
Residual satisfaction plus the retained branch value reconstructs satisfaction
of the original CNF.  Deleted clauses are recovered because they contain the
literal made true by the branch value.
-/
theorem restoreSatisfaction
    (formula : Cnf)
    (assignment : Assignment)
    (var : Var)
    (value : Bool)
    (valueExact : assignment var = value) :
    Satisfies assignment (branchResidual formula var value) →
      Satisfies assignment formula := by
  induction formula with
  | nil =>
      intro _
      exact .nil
  | cons clause rest inductionHypothesis =>
      cases hitEq :
          Clause.containsLiteral (Literal.forValue var value) clause with
      | false =>
          rw [branchResidual_cons_miss clause rest var value hitEq]
          intro residualSatisfaction
          cases residualSatisfaction with
          | cons headSatisfaction tailSatisfaction =>
              exact .cons headSatisfaction
                (inductionHypothesis tailSatisfaction)
      | true =>
          rw [branchResidual_cons_hit clause rest var value hitEq]
          intro residualSatisfaction
          have branchLiteralTrue :
              (Literal.forValue var value).eval assignment = true :=
            Literal.eval_forValue_true assignment var value valueExact
          have headSatisfaction : Clause.eval assignment clause = true :=
            Clause.eval_true_of_containsLiteral
              assignment
              (Literal.forValue var value)
              branchLiteralTrue
              clause
              hitEq
          exact .cons headSatisfaction
            (inductionHypothesis residualSatisfaction)

/-- A branch-indexed completion exposes the indexed variable value exactly. -/
theorem indexedCompletion_valueExact
    {formula : Cnf}
    {var : Var}
    {value : Bool}
    (completion : ValueIndexedCompletion formula var value) :
    completion.underlying.1 var = value := by
  cases completion with
  | ofCompletion raw =>
      rfl

/--
A residual completion retains both the assignment, its branch provenance, and
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
    {value : Bool} :
    ResidualBranchCompletion formula var value →
      ValueIndexedCompletion formula var value := by
  intro residual
  rcases residual with ⟨assignment, valueExact, residualSatisfaction⟩
  have originalSatisfaction : Satisfies assignment formula :=
    restoreSatisfaction
      formula assignment var value valueExact residualSatisfaction
  let raw : Completion formula :=
    ⟨assignment, originalSatisfaction⟩
  cases valueExact
  exact ValueIndexedCompletion.ofCompletion raw

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