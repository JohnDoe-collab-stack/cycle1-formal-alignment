import ConstitutiveSearch.LocalSearchableCodeExecution
import ConstitutiveSearch.SearchableTransportCodeValidation
import ConstitutiveSearch.SAT.ProvenanceSequentialization
import ConstitutiveSearch.SAT.ExplicitFamilyTransportCosts
import ConstitutiveSearch.SAT.ExplicitFamilyInputComplexity

/-!
# Constituted entry-code schedule extracted from SAT trajectories

A FlipSymmetricTrajectory is not itself a linear path of primitive flips:
each constitutive step expands a parent into two children and then absorbs the
false sibling into the retained true child.  The primitive flip therefore runs
between siblings, not from the trajectory parent to its retained child.

This module preserves that distinction.

It extracts, directly from the proof-relevant trajectory, the finite schedule
of entry sibling witnesses actually constituted at its steps.  No witness list,
candidate list, closure fuel, or global ClosureSearch result is supplied
separately.

Every extracted witness:
* carries a variable from the trajectory's own decisionVars provenance;
* compiles to a one-atom entry TransportCode;
* is executable by the provenance-derived primitive search;
* validates with exactly one primitive query;
* admits candidate-free entry execution.

The complete extracted schedule has exactly one entry witness and one transport
atom per constitutive step.  Consequently its production-atom count and
executable validation-query count are exactly the trajectory length.
-/

namespace ConstitutiveSearch
namespace SAT

/--
One locally constituted sibling witness packaged with its dependent endpoints.

The finite provenance list is explicit in the type.  This lets heterogeneous
sibling endpoint pairs from different trajectory levels coexist in one ordinary
list without erasing their generator witness.
-/
structure ConstitutedLocalWitness
    (rootFormula : Cnf)
    (vars : List Var) where
  source :
    GeneratedStructuralBranchContext
      rootFormula
  target :
    GeneratedStructuralBranchContext
      rootFormula
  witness :
    ProvenanceStructuralFlipWitness
      (rootFormula := rootFormula)
      vars
      source
      target

namespace ConstitutedLocalWitness

/-- Compile one constituted entry witness to its one-atom transport code. -/
def code
    {rootFormula : Cnf}
    {vars : List Var}
    (entry :
      ConstitutedLocalWitness
        rootFormula
        vars) :
    TransportClosure
      (ProvenanceStructuralFlipWitness
        (rootFormula := rootFormula)
        vars)
      entry.source
      entry.target :=
  TransportClosure.ofGenerator
    entry.witness

/-- Every packaged entry witness contributes exactly one transport atom. -/
theorem code_size
    {rootFormula : Cnf}
    {vars : List Var}
    (entry :
      ConstitutedLocalWitness
        rootFormula
        vars) :
    entry.code.size = 1 := by
  rfl

/--
The code of every packaged witness is searchable by the finite provenance
search over the same constituted variable list.
-/
theorem code_searchable
    {rootFormula : Cnf}
    {vars : List Var}
    (entry :
      ConstitutedLocalWitness
        rootFormula
        vars) :
    entry.code.SearchableBy
      (provenanceStructuralFlipSearch
        rootFormula
        vars) := by
  change
    (provenanceStructuralFlipSearch
        rootFormula
        vars).find
      entry.source
      entry.target ≠
    none
  exact
    (provenanceStructuralFlipSearch_witnessComplete
      rootFormula
      vars)
      entry.witness

/-- Executable SearchableBy validation of one entry code succeeds. -/
theorem validation_success
    {rootFormula : Cnf}
    {vars : List Var}
    (entry :
      ConstitutedLocalWitness
        rootFormula
        vars) :
    (validateSearchableCode
        (provenanceStructuralFlipSearch
          rootFormula
          vars)
        entry.code).success =
      true :=
  validateSearchableCode_success_of_searchable
    (provenanceStructuralFlipSearch
      rootFormula
      vars)
    entry.code
    entry.code_searchable

/-- Executable validation performs exactly one primitive query per entry code. -/
theorem validation_primitiveQueries
    {rootFormula : Cnf}
    {vars : List Var}
    (entry :
      ConstitutedLocalWitness
        rootFormula
        vars) :
    (validateSearchableCode
        (provenanceStructuralFlipSearch
          rootFormula
          vars)
        entry.code).primitiveQueries =
      1 := by
  calc
    (validateSearchableCode
        (provenanceStructuralFlipSearch
          rootFormula
          vars)
        entry.code).primitiveQueries
        =
      entry.code.size :=
        validateSearchableCode_primitiveQueries
          (provenanceStructuralFlipSearch
            rootFormula
            vars)
          entry.code
    _ = 1 :=
      entry.code_size

/-- Every constituted entry code admits the minimal candidate-free execution. -/
theorem localSequentialExecution
    {rootFormula : Cnf}
    {vars : List Var}
    (entry :
      ConstitutedLocalWitness
        rootFormula
        vars) :
    TransportCode.LocalSequentialExecution
      (provenanceStructuralFlipSearch
        rootFormula
        vars)
      entry.code :=
  TransportCode.localSequentialExecution_of_searchable
    (provenanceStructuralFlipSearch
      rootFormula
      vars)
    entry.code
    entry.code_searchable

end ConstitutedLocalWitness

namespace FlipSymmetricTrajectory

/--
Extract the entry sibling witnesses of a trajectory into any finite provenance
list known to contain all variables constituted by that trajectory.

The containment proof is used only to package the already-present entry
witnesses.  No search is performed.
-/
def constitutedLocalWitnessesUnder
    {rootFormula : Cnf}
    {start finish :
      GeneratedStructuralBranchContext rootFormula}
    {length : Nat}
    (trajectory :
      FlipSymmetricTrajectory
        start
        finish
        length)
    (vars : List Var)
    (contains :
      ∀ query : Var,
        query ∈ trajectory.decisionVars →
          query ∈ vars) :
    List
      (ConstitutedLocalWitness
        rootFormula
        vars) :=
  match trajectory with
  | .done _ =>
      []
  | .step var fresh symmetric tail =>
      let headMember :
          var ∈ vars :=
        contains
          var
          (by
            change
              var ∈
                var :: tail.decisionVars
            exact
              List.mem_cons_self)
      let tailContains :
          ∀ query : Var,
            query ∈ tail.decisionVars →
              query ∈ vars :=
        fun query member =>
          contains
            query
            (by
              change
                query ∈
                  var :: tail.decisionVars
              exact
                List.mem_cons_of_mem
                  var
                  member)
      let head :
          ConstitutedLocalWitness
            rootFormula
            vars :=
        { source :=
            GeneratedStructuralBranchContext.child
              start
              var
              false
              fresh
          target :=
            GeneratedStructuralBranchContext.child
              start
              var
              true
              fresh
          witness :=
            { var := var
              member := headMember
              relation :=
                flipSymmetricSiblingRelation
                  start
                  var
                  fresh
                  symmetric } }
      head ::
        constitutedLocalWitnessesUnder
          tail
          vars
          tailContains

/--
Canonical entry schedule: the provenance domain is exactly decisionVars
extracted from the trajectory itself.
-/
def constitutedLocalWitnesses
    {rootFormula : Cnf}
    {start finish :
      GeneratedStructuralBranchContext rootFormula}
    {length : Nat}
    (trajectory :
      FlipSymmetricTrajectory
        start
        finish
        length) :
    List
      (ConstitutedLocalWitness
        rootFormula
        trajectory.decisionVars) :=
  trajectory.constitutedLocalWitnessesUnder
    trajectory.decisionVars
    (fun _query member =>
      member)

/-- The extracted schedule contains exactly one entry witness per step. -/
theorem constitutedLocalWitnessesUnder_length
    {rootFormula : Cnf}
    {start finish :
      GeneratedStructuralBranchContext rootFormula}
    {length : Nat}
    (trajectory :
      FlipSymmetricTrajectory
        start
        finish
        length) :
    ∀ (vars : List Var)
      (contains :
        ∀ query : Var,
          query ∈ trajectory.decisionVars →
            query ∈ vars),
      (trajectory.constitutedLocalWitnessesUnder
          vars
          contains).length =
        length := by
  induction trajectory with
  | done state =>
      intro vars contains
      rfl
  | step var fresh symmetric tail inductionHypothesis =>
      intro vars contains
      simp only [
        constitutedLocalWitnessesUnder,
        List.length_cons
      ]
      rw [
        inductionHypothesis
      ]

/-- Canonical trajectory-derived schedule length is the trajectory length. -/
theorem constitutedLocalWitnesses_length
    {rootFormula : Cnf}
    {start finish :
      GeneratedStructuralBranchContext rootFormula}
    {length : Nat}
    (trajectory :
      FlipSymmetricTrajectory
        start
        finish
        length) :
    trajectory.constitutedLocalWitnesses.length =
      length := by
  unfold constitutedLocalWitnesses
  exact
    trajectory.constitutedLocalWitnessesUnder_length
      trajectory.decisionVars
      (fun _query member =>
        member)

end FlipSymmetricTrajectory

namespace ConstitutedLocalSchedule

/-- Total number of transport atoms produced by an extracted entry schedule. -/
def atomCount
    {rootFormula : Cnf}
    {vars : List Var} :
    List
      (ConstitutedLocalWitness
        rootFormula
        vars) →
      Nat
  | [] =>
      0
  | entry :: rest =>
      entry.code.size +
        atomCount rest

/-- Total executable validation primitive queries for an extracted schedule. -/
def validationPrimitiveQueries
    {rootFormula : Cnf}
    {vars : List Var} :
    List
      (ConstitutedLocalWitness
        rootFormula
        vars) →
      Nat
  | [] =>
      0
  | entry :: rest =>
      (validateSearchableCode
          (provenanceStructuralFlipSearch
            rootFormula
            vars)
          entry.code).primitiveQueries +
        validationPrimitiveQueries
          rest

/-- Every entry code in the schedule validates successfully. -/
def ValidationSucceeds
    {rootFormula : Cnf}
    {vars : List Var} :
    List
      (ConstitutedLocalWitness
        rootFormula
        vars) →
      Prop
  | [] =>
      True
  | entry :: rest =>
      (validateSearchableCode
          (provenanceStructuralFlipSearch
            rootFormula
            vars)
          entry.code).success =
          true ∧
        ValidationSucceeds rest

/-- Every entry code in the schedule admits candidate-free entry execution. -/
def HasLocalExecutions
    {rootFormula : Cnf}
    {vars : List Var} :
    List
      (ConstitutedLocalWitness
        rootFormula
        vars) →
      Prop
  | [] =>
      True
  | entry :: rest =>
      TransportCode.LocalSequentialExecution
          (provenanceStructuralFlipSearch
            rootFormula
            vars)
          entry.code ∧
        HasLocalExecutions rest

/-- Production atom count is exactly schedule length. -/
theorem atomCount_eq_length
    {rootFormula : Cnf}
    {vars : List Var}
    (schedule :
      List
        (ConstitutedLocalWitness
          rootFormula
          vars)) :
    atomCount schedule =
      schedule.length := by
  induction schedule with
  | nil =>
      rfl
  | cons entry rest inductionHypothesis =>
      change
        entry.code.size +
            atomCount rest =
          rest.length + 1
      rw [
        entry.code_size,
        inductionHypothesis
      ]
      exact
        Nat.add_comm 1 rest.length

/-- Executable validation query count is exactly schedule length. -/
theorem validationPrimitiveQueries_eq_length
    {rootFormula : Cnf}
    {vars : List Var}
    (schedule :
      List
        (ConstitutedLocalWitness
          rootFormula
          vars)) :
    validationPrimitiveQueries schedule =
      schedule.length := by
  induction schedule with
  | nil =>
      rfl
  | cons entry rest inductionHypothesis =>
      change
        (validateSearchableCode
            (provenanceStructuralFlipSearch
              rootFormula
              vars)
            entry.code).primitiveQueries +
              validationPrimitiveQueries rest =
          rest.length + 1
      rw [
        entry.validation_primitiveQueries,
        inductionHypothesis
      ]
      exact
        Nat.add_comm 1 rest.length

/-- Every extracted schedule validates successfully. -/
theorem validationSucceeds
    {rootFormula : Cnf}
    {vars : List Var}
    (schedule :
      List
        (ConstitutedLocalWitness
          rootFormula
          vars)) :
    ValidationSucceeds schedule := by
  induction schedule with
  | nil =>
      exact True.intro
  | cons entry rest inductionHypothesis =>
      exact
        ⟨entry.validation_success,
          inductionHypothesis⟩

/-- Every extracted schedule admits entry candidate-free executions stepwise. -/
theorem hasLocalExecutions
    {rootFormula : Cnf}
    {vars : List Var}
    (schedule :
      List
        (ConstitutedLocalWitness
          rootFormula
          vars)) :
    HasLocalExecutions schedule := by
  induction schedule with
  | nil =>
      exact True.intro
  | cons entry rest inductionHypothesis =>
      exact
        ⟨entry.localSequentialExecution,
          inductionHypothesis⟩

end ConstitutedLocalSchedule

namespace FlipSymmetricTrajectory

/-- Produced entry transport atoms are exactly the constitutive trajectory length. -/
theorem constitutedLocalAtomCount_eq_length
    {rootFormula : Cnf}
    {start finish :
      GeneratedStructuralBranchContext rootFormula}
    {length : Nat}
    (trajectory :
      FlipSymmetricTrajectory
        start
        finish
        length) :
    ConstitutedLocalSchedule.atomCount
        trajectory.constitutedLocalWitnesses =
      length := by
  rw [
    ConstitutedLocalSchedule.atomCount_eq_length,
    trajectory.constitutedLocalWitnesses_length
  ]

/-- Executable validation charges exactly one primitive query per step. -/
theorem constitutedLocalValidationQueries_eq_length
    {rootFormula : Cnf}
    {start finish :
      GeneratedStructuralBranchContext rootFormula}
    {length : Nat}
    (trajectory :
      FlipSymmetricTrajectory
        start
        finish
        length) :
    ConstitutedLocalSchedule.validationPrimitiveQueries
        trajectory.constitutedLocalWitnesses =
      length := by
  rw [
    ConstitutedLocalSchedule.validationPrimitiveQueries_eq_length,
    trajectory.constitutedLocalWitnesses_length
  ]

/-- Every code produced from the trajectory validates successfully. -/
theorem constitutedLocalValidationSucceeds
    {rootFormula : Cnf}
    {start finish :
      GeneratedStructuralBranchContext rootFormula}
    {length : Nat}
    (trajectory :
      FlipSymmetricTrajectory
        start
        finish
        length) :
    ConstitutedLocalSchedule.ValidationSucceeds
      trajectory.constitutedLocalWitnesses :=
  ConstitutedLocalSchedule.validationSucceeds
    trajectory.constitutedLocalWitnesses

/-- Every code produced from the trajectory has a candidate-free entry execution. -/
theorem constitutedLocalHasLocalExecutions
    {rootFormula : Cnf}
    {start finish :
      GeneratedStructuralBranchContext rootFormula}
    {length : Nat}
    (trajectory :
      FlipSymmetricTrajectory
        start
        finish
        length) :
    ConstitutedLocalSchedule.HasLocalExecutions
      trajectory.constitutedLocalWitnesses :=
  ConstitutedLocalSchedule.hasLocalExecutions
    trajectory.constitutedLocalWitnesses

/--
The new endogenous production count agrees with the previously audited
transport-certificate atom count.
-/
theorem constitutedLocalAtomCount_eq_transportCertificateAtomCount
    {rootFormula : Cnf}
    {start finish :
      GeneratedStructuralBranchContext rootFormula}
    {length : Nat}
    (trajectory :
      FlipSymmetricTrajectory
        start
        finish
        length) :
    ConstitutedLocalSchedule.atomCount
        trajectory.constitutedLocalWitnesses =
      trajectory.transportCertificateAtomCount := by
  rw [
    trajectory.constitutedLocalAtomCount_eq_length,
    trajectory.transportCertificateAtomCount_eq_index
  ]

end FlipSymmetricTrajectory

/-- Canonical constituted entry schedule for the closed explicit SAT family. -/
def explicitFamilyConstitutedLocalWitnesses
    (count : Nat) :=
  (explicitFamilyResourceTrajectory
    count).trajectory.constitutedLocalWitnesses

/-- F(n) produces exactly n entry constituted witnesses. -/
theorem explicitFamilyConstitutedLocalWitnesses_length
    (count : Nat) :
    (explicitFamilyConstitutedLocalWitnesses
      count).length =
      count :=
  (explicitFamilyResourceTrajectory
    count).trajectory.constitutedLocalWitnesses_length

/-- F(n) produces exactly n primitive transport atoms. -/
theorem explicitFamilyConstitutedLocalAtomCount
    (count : Nat) :
    ConstitutedLocalSchedule.atomCount
        (explicitFamilyConstitutedLocalWitnesses
          count) =
      count :=
  (explicitFamilyResourceTrajectory
    count).trajectory.constitutedLocalAtomCount_eq_length

/-- F(n) validates the complete locally constituted schedule in exactly n queries. -/
theorem explicitFamilyConstitutedLocalValidationQueries
    (count : Nat) :
    ConstitutedLocalSchedule.validationPrimitiveQueries
        (explicitFamilyConstitutedLocalWitnesses
          count) =
      count :=
  (explicitFamilyResourceTrajectory
    count).trajectory.constitutedLocalValidationQueries_eq_length

/-- Every locally constituted F(n) code validates successfully. -/
theorem explicitFamilyConstitutedLocalValidationSucceeds
    (count : Nat) :
    ConstitutedLocalSchedule.ValidationSucceeds
      (explicitFamilyConstitutedLocalWitnesses
        count) :=
  (explicitFamilyResourceTrajectory
    count).trajectory.constitutedLocalValidationSucceeds

/-- Every locally constituted F(n) code admits candidate-free execution. -/
theorem explicitFamilyConstitutedLocalHasLocalExecutions
    (count : Nat) :
    ConstitutedLocalSchedule.HasLocalExecutions
      (explicitFamilyConstitutedLocalWitnesses
        count) :=
  (explicitFamilyResourceTrajectory
    count).trajectory.constitutedLocalHasLocalExecutions

/-- Production atom count of the endogenous F(n) schedule is input-polynomial. -/
theorem explicitFamilyConstitutedLocalAtomCount_inputPolynomiallyBounded :
    InputPolynomiallyBounded
      explicitFamilyInputBitSize
      (fun count =>
        ConstitutedLocalSchedule.atomCount
          (explicitFamilyConstitutedLocalWitnesses
            count)) := by
  refine
    ⟨CostPolynomial.input, ?_⟩
  intro count
  change
    ConstitutedLocalSchedule.atomCount
        (explicitFamilyConstitutedLocalWitnesses
          count) ≤
      explicitFamilyInputBitSize count
  rw [
    explicitFamilyConstitutedLocalAtomCount
  ]
  exact
    explicitFamilyIndex_le_inputBitSize
      count

/-- Validation query count of the endogenous F(n) schedule is input-polynomial. -/
theorem explicitFamilyConstitutedLocalValidation_inputPolynomiallyBounded :
    InputPolynomiallyBounded
      explicitFamilyInputBitSize
      (fun count =>
        ConstitutedLocalSchedule.validationPrimitiveQueries
          (explicitFamilyConstitutedLocalWitnesses
            count)) := by
  refine
    ⟨CostPolynomial.input, ?_⟩
  intro count
  change
    ConstitutedLocalSchedule.validationPrimitiveQueries
        (explicitFamilyConstitutedLocalWitnesses
          count) ≤
      explicitFamilyInputBitSize count
  rw [
    explicitFamilyConstitutedLocalValidationQueries
  ]
  exact
    explicitFamilyIndex_le_inputBitSize
      count

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.ConstitutedLocalWitness
#print axioms ConstitutiveSearch.SAT.ConstitutedLocalWitness.code
#print axioms ConstitutiveSearch.SAT.ConstitutedLocalWitness.code_size
#print axioms ConstitutiveSearch.SAT.ConstitutedLocalWitness.code_searchable
#print axioms ConstitutiveSearch.SAT.ConstitutedLocalWitness.validation_success
#print axioms ConstitutiveSearch.SAT.ConstitutedLocalWitness.validation_primitiveQueries
#print axioms ConstitutiveSearch.SAT.ConstitutedLocalWitness.localSequentialExecution
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.constitutedLocalWitnessesUnder
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.constitutedLocalWitnesses
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.constitutedLocalWitnessesUnder_length
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.constitutedLocalWitnesses_length
#print axioms ConstitutiveSearch.SAT.ConstitutedLocalSchedule.atomCount
#print axioms ConstitutiveSearch.SAT.ConstitutedLocalSchedule.validationPrimitiveQueries
#print axioms ConstitutiveSearch.SAT.ConstitutedLocalSchedule.ValidationSucceeds
#print axioms ConstitutiveSearch.SAT.ConstitutedLocalSchedule.HasLocalExecutions
#print axioms ConstitutiveSearch.SAT.ConstitutedLocalSchedule.atomCount_eq_length
#print axioms ConstitutiveSearch.SAT.ConstitutedLocalSchedule.validationPrimitiveQueries_eq_length
#print axioms ConstitutiveSearch.SAT.ConstitutedLocalSchedule.validationSucceeds
#print axioms ConstitutiveSearch.SAT.ConstitutedLocalSchedule.hasLocalExecutions
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.constitutedLocalAtomCount_eq_length
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.constitutedLocalValidationQueries_eq_length
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.constitutedLocalValidationSucceeds
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.constitutedLocalHasLocalExecutions
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.constitutedLocalAtomCount_eq_transportCertificateAtomCount
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedLocalWitnesses
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedLocalWitnesses_length
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedLocalAtomCount
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedLocalValidationQueries
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedLocalValidationSucceeds
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedLocalHasLocalExecutions
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedLocalAtomCount_inputPolynomiallyBounded
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedLocalValidation_inputPolynomiallyBounded
/- AXIOM_AUDIT_END -/
