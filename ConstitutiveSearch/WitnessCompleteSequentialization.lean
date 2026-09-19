import ConstitutiveSearch.SequentialPrimitiveExecution

/-!
# Sequentialization from witness-complete primitive search

SequentialPrimitiveExecution reconstructs a primitive-hit path after a bounded
ClosureSearch run succeeds.  This module removes that dependency on having run
global closure first.

A primitive RelationSearch is witness-complete when every primitive generator
witness has some executable search hit between the same endpoints.  Under this
condition, any already constituted TransportCode can be converted directly to
a PrimitiveHitPath.

Thus a finite composed transport that is already known proof-relevantly can be
executed sequentially edge by edge without first rediscovering it through the
global ClosureSearch procedure.
-/

namespace ConstitutiveSearch

universe uGenerator

namespace RelationSearch

/--
Local completeness on announced primitive witnesses.

The returned witness need not be proof-term-identical to the supplied witness;
only executable discovery of some witness for the same ordered pair is
required.
-/
def WitnessComplete
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator) : Prop :=
  ∀ {source target : State},
    (witness : Generator source target) →
      primitive.find source target ≠ none

end RelationSearch

namespace TransportCode

/--
A primitive atom can be turned directly into a one-edge PrimitiveHitPath when
the primitive search is witness-complete.
-/
theorem atom_hasPrimitiveHitPath
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator)
    (complete :
      primitive.WitnessComplete)
    {source target : State}
    (witness : Generator source target) :
    ∃ path :
        PrimitiveHitPath
          primitive
          source
          target,
      path.length = 1 := by
  cases found :
      primitive.find source target with
  | none =>
      exact
        False.elim
          ((complete witness) found)
  | some executableWitness =>
      exact
        ⟨PrimitiveHitPath.step
            found
            (PrimitiveHitPath.identity target),
          rfl⟩

/--
Any finite TransportCode over a witness-complete primitive relation has a
directly executable primitive-hit path with exactly the same number of atoms.

No ClosureSearch invocation occurs in this reconstruction.
-/
theorem hasPrimitiveHitPath_of_witnessComplete
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator)
    (complete :
      primitive.WitnessComplete)
    {source target : State}
    (code :
      TransportCode
        Generator
        source
        target) :
    ∃ path :
        PrimitiveHitPath
          primitive
          source
          target,
      path.length = code.size := by
  induction code with
  | identity state =>
      exact
        ⟨PrimitiveHitPath.identity state,
          rfl⟩
  | atom witness =>
      exact
        atom_hasPrimitiveHitPath
          primitive
          complete
          witness
  | compose first second firstHypothesis secondHypothesis =>
      rcases firstHypothesis with
        ⟨firstPath, firstLength⟩
      rcases secondHypothesis with
        ⟨secondPath, secondLength⟩
      refine
        ⟨firstPath.trans secondPath, ?_⟩
      rw [
        firstPath.trans_length,
        firstLength,
        secondLength
      ]
      rfl

/--
A known TransportCode over a witness-complete primitive search therefore has an
exact sequential execution: one primitive query per code atom and no
composition-candidate inspection.
-/
theorem hasSequentialExecution_of_witnessComplete
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator)
    (complete :
      primitive.WitnessComplete)
    (candidates : List State)
    (fuel : Nat)
    (fuelPositive : 0 < fuel)
    {source target : State}
    (code :
      TransportCode
        Generator
        source
        target) :
    ∃ path :
        PrimitiveHitPath
          primitive
          source
          target,
      path.length = code.size ∧
        (path.sequentialStats
            candidates
            fuel).primitiveQueries =
          code.size ∧
        (path.sequentialStats
            candidates
            fuel).compositionCandidates =
          0 := by
  rcases
      code.hasPrimitiveHitPath_of_witnessComplete
        primitive
        complete with
    ⟨path, pathLength⟩
  refine
    ⟨path,
      pathLength,
      ?_,
      ?_⟩
  · calc
      (path.sequentialStats
          candidates
          fuel).primitiveQueries
          =
        path.length :=
          path.sequentialStats_primitiveQueries
            candidates
            fuel
            fuelPositive
      _ =
        code.size :=
          pathLength
  · exact
      path.sequentialStats_compositionCandidates
        candidates
        fuel
        fuelPositive

end TransportCode

end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.RelationSearch.WitnessComplete
#print axioms ConstitutiveSearch.TransportCode.atom_hasPrimitiveHitPath
#print axioms ConstitutiveSearch.TransportCode.hasPrimitiveHitPath_of_witnessComplete
#print axioms ConstitutiveSearch.TransportCode.hasSequentialExecution_of_witnessComplete
/- AXIOM_AUDIT_END -/
