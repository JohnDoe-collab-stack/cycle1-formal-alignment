import ConstitutiveSearch.SAT.BinaryBranch

/-!
# SAT branch residuals and continuation transports

This module connects the exact Boolean branch split to a syntactic residual CNF
without introducing a satisfiability query.

For one fixed variable value, clauses already satisfied by the corresponding
literal are deleted. Other clauses are kept unchanged. The residual therefore
remains an order-preserving sub-CNF of the source.

The executable residual syntax and its constructive weakening witness are built
by direct structural recursion. The reverse satisfaction theorem is then proved
against exactly that residual. No later proof layer may silently strengthen the
residual construction.

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

/-- Executable branch residual by direct structural recursion on the CNF. -/
private def branchResidualCore
    (var : Var)
    (value : Bool) : Cnf → Cnf
  | [] => []
  | clause :: rest =>
      match Clause.containsLiteral (Literal.forValue var value) clause with
      | true => branchResidualCore var value rest
      | false => clause :: branchResidualCore var value rest

/-- Residual CNF obtained after deleting clauses satisfied by the fixed bit. -/
def branchResidual
    (formula : Cnf)
    (var : Var)
    (value : Bool) : Cnf :=
  branchResidualCore var value formula

/--
Constructive clause-deletion witness for the exact executable residual. This is
also direct structural recursion and therefore produces executable data in
`Type` without a noncomputable recursor.
-/
private def branchWeakeningCore
    (var : Var)
    (value : Bool) :
    (formula : Cnf) →
      CnfWeakening formula (branchResidualCore var value formula)
  | [] => .done
  | clause :: rest =>
      match Clause.containsLiteral (Literal.forValue var value) clause with
      | true => .drop clause (branchWeakeningCore var value rest)
      | false => .keep clause (branchWeakeningCore var value rest)

/-- The residual is constructively a weakening of the original CNF. -/
def branchWeakening
    (formula : Cnf)
    (var : Var)
    (value : Bool) :
    CnfWeakening formula (branchResidual formula var value) :=
  branchWeakeningCore var value formula

/--
Reverse satisfaction proof for the exact residual. The recursion is proof-only:
all executable data have already been constructed by the two structural
functions above.
-/
private theorem restoreSatisfactionCore
    (var : Var)
    (value : Bool)
    (assignment : Assignment)
    (valueExact : assignment var = value) :
    (formula : Cnf) →
      Satisfies assignment (branchResidualCore var value formula) →
        Satisfies assignment formula
  | [] => fun _ => .nil
  | clause :: rest => fun residualSatisfaction => by
      cases hitEq :
          Clause.containsLiteral (Literal.forValue var value) clause with
      | false =>
          rw [branchResidualCore, hitEq] at residualSatisfaction
          cases residualSatisfaction with
          | cons headSatisfaction tailSatisfaction =>
              exact .cons headSatisfaction
                (restoreSatisfactionCore
                  var value assignment valueExact rest tailSatisfaction)
      | true =>
          rw [branchResidualCore, hitEq] at residualSatisfaction
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
            (restoreSatisfactionCore
              var value assignment valueExact rest residualSatisfaction)

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
  restoreSatisfactionCore var value assignment valueExact formula

/--
Positive bundle exposing the residual syntax, its forward weakening witness,
and its reverse reconstruction theorem for clients that need the three layers
together.
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

/-- Assemble the already constructed residual and its two structural laws. -/
def branchReduction
    (formula : Cnf)
    (var : Var)
    (value : Bool) :
    BranchReductionResult formula var value :=
  { residual := branchResidual formula var value
    weakening := branchWeakening formula var value
    restore := fun assignment valueExact residualSatisfaction =>
      restoreSatisfaction
        formula assignment var value valueExact residualSatisfaction }

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
#print axioms ConstitutiveSearch.SAT.branchResidual
#print axioms ConstitutiveSearch.SAT.branchWeakening
#print axioms ConstitutiveSearch.SAT.restoreSatisfaction
#print axioms ConstitutiveSearch.SAT.BranchReductionResult
#print axioms ConstitutiveSearch.SAT.branchReduction
#print axioms ConstitutiveSearch.SAT.ResidualBranchCompletion
#print axioms ConstitutiveSearch.SAT.branchToResidual
#print axioms ConstitutiveSearch.SAT.residualToBranch
#print axioms ConstitutiveSearch.SAT.branchToResidualTransport
#print axioms ConstitutiveSearch.SAT.residualToBranchTransport
#print axioms ConstitutiveSearch.SAT.branch_residual_nonempty_iff
/- AXIOM_AUDIT_END -/