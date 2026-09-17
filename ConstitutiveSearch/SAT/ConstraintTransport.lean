import ConstitutiveSearch.IrreducibleFrontier

/-!
# First SAT instance: transports reconstructed from CNF weakening

This module instantiates constitutive search on propositional CNF constraints
without assuming satisfiability, unsatisfiability, or an oracle for either.

A completion is a total Boolean assignment together with a proof that it
satisfies every clause of the CNF.  The structural relation `CnfWeakening`
expresses that the target CNF is obtained by deleting zero or more clauses from
the source CNF while preserving the order of retained clauses.

Every source completion therefore transports constructively to a target
completion by keeping the same assignment and restricting the satisfaction
proof.  This gives a concrete `ContinuationTransport` from a purely structural
constraint relation.

An executable subsequence search constructs weakening witnesses when it finds
them.  As in the generic layer, `none` is only a search result.  This module does
not yet prove completeness of that search as a negative decision procedure.
-/

namespace ConstitutiveSearch
namespace SAT

abbrev Var := Nat
abbrev Assignment := Var → Bool

inductive Literal where
  | positive : Var → Literal
  | negative : Var → Literal
  deriving DecidableEq

abbrev Clause := List Literal
abbrev Cnf := List Clause

namespace Literal

/-- Boolean evaluation of one literal under a total assignment. -/
def eval (assignment : Assignment) : Literal → Bool
  | .positive variable => assignment variable
  | .negative variable => !(assignment variable)

end Literal

namespace Clause

/-- Disjunctive evaluation of a clause.  The empty clause is false. -/
def eval (assignment : Assignment) : Clause → Bool
  | [] => false
  | literal :: rest => literal.eval assignment || eval assignment rest

end Clause

/-- A total assignment satisfies every clause in the CNF. -/
def Satisfies (formula : Cnf) (assignment : Assignment) : Prop :=
  List.Forall (fun clause => Clause.eval assignment clause = true) formula

/-- Proof-relevant terminal completion space of a CNF. -/
abbrev Completion (formula : Cnf) : Type :=
  { assignment : Assignment // Satisfies formula assignment }

/--
Constructive clause-deletion relation.  `CnfWeakening source target` means that
`target` is an order-preserving sublist of `source`.
-/
inductive CnfWeakening : Cnf → Cnf → Type
  | done {source : Cnf} : CnfWeakening source []
  | drop
      {source target : Cnf}
      (clause : Clause)
      (rest : CnfWeakening source target) :
      CnfWeakening (clause :: source) target
  | keep
      {source target : Cnf}
      (clause : Clause)
      (rest : CnfWeakening source target) :
      CnfWeakening (clause :: source) (clause :: target)

namespace CnfWeakening

/-- Every CNF weakens to itself. -/
def refl : (formula : Cnf) → CnfWeakening formula formula
  | [] => .done
  | clause :: rest => .keep clause (refl rest)

/-- Weakening preserves satisfaction by deleting obligations only. -/
def preservesSatisfaction
    {source target : Cnf}
    (weakening : CnfWeakening source target)
    {assignment : Assignment} :
    Satisfies source assignment → Satisfies target assignment := by
  induction weakening with
  | done =>
      intro _
      exact .nil
  | drop clause rest inductionHypothesis =>
      intro sourceSatisfaction
      cases sourceSatisfaction with
      | cons _ tailSatisfaction =>
          exact inductionHypothesis tailSatisfaction
  | keep clause rest inductionHypothesis =>
      intro sourceSatisfaction
      cases sourceSatisfaction with
      | cons headSatisfaction tailSatisfaction =>
          exact .cons headSatisfaction
            (inductionHypothesis tailSatisfaction)

/-- A weakening witness acts constructively on completion spaces. -/
def completionMap
    {source target : Cnf}
    (weakening : CnfWeakening source target) :
    Completion source → Completion target :=
  fun completion =>
    ⟨completion.1,
      weakening.preservesSatisfaction completion.2⟩

/-- Structural CNF weakening reconstructs the generic continuation transport. -/
def toTransport
    {source target : Cnf}
    (weakening : CnfWeakening source target) :
    ContinuationTransport Completion source target :=
  { map := weakening.completionMap }

/--
Executable search for an order-preserving target sublist inside the source CNF.
It constructs a weakening witness when successful.
-/
def find : (source target : Cnf) → Option (CnfWeakening source target) := by
  intro source
  induction source with
  | nil =>
      intro target
      cases target with
      | nil => exact some .done
      | cons _ _ => exact none
  | cons sourceHead sourceTail inductionHypothesis =>
      intro target
      cases target with
      | nil =>
          exact some .done
      | cons targetHead targetTail =>
          by_cases headsEqual : sourceHead = targetHead
          · subst targetHead
            match inductionHypothesis targetTail with
            | some retainedTail =>
                exact some (.keep sourceHead retainedTail)
            | none =>
                match inductionHypothesis (sourceHead :: targetTail) with
                | some droppedTail =>
                    exact some (.drop sourceHead droppedTail)
                | none => exact none
          · match inductionHypothesis (targetHead :: targetTail) with
            | some droppedTail =>
                exact some (.drop sourceHead droppedTail)
            | none => exact none

end CnfWeakening

/-- Generic relational action instantiated by CNF weakening. -/
def weakeningAction :
    RelationalContinuationAction CnfWeakening Completion :=
  { act := fun witness completion =>
      witness.completionMap completion }

/-- Executable weakening search exposed through the generic relation interface. -/
def weakeningSearch : RelationSearch CnfWeakening :=
  { find := CnfWeakening.find }

/-- Convenient singleton positive clause. -/
def positiveUnit (variable : Var) : Clause :=
  [Literal.positive variable]

/-- Convenient singleton negative clause. -/
def negativeUnit (variable : Var) : Clause :=
  [Literal.negative variable]

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.Literal
#print axioms ConstitutiveSearch.SAT.Clause.eval
#print axioms ConstitutiveSearch.SAT.Satisfies
#print axioms ConstitutiveSearch.SAT.CnfWeakening
#print axioms ConstitutiveSearch.SAT.CnfWeakening.preservesSatisfaction
#print axioms ConstitutiveSearch.SAT.CnfWeakening.toTransport
#print axioms ConstitutiveSearch.SAT.CnfWeakening.find
#print axioms ConstitutiveSearch.SAT.weakeningAction
#print axioms ConstitutiveSearch.SAT.weakeningSearch
/- AXIOM_AUDIT_END -/