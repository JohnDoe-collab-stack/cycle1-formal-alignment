import ConstitutiveSearch.LocalSearchableCodePolynomial

/-!
# Composition of polynomial local searchable-code families

LocalSearchableCodePolynomial reduces candidate-free local execution to the
size of an already constituted searchable TransportCode.

This module proves the corresponding compositional closure theorem.

If two code families:
* meet at one constituted intermediate state;
* are searchable by the same primitive search;
* each have input-polynomial code size;

then their pointwise TransportClosure composition:
* is searchable;
* has additive code size;
* has input-polynomial code size;
* therefore has input-polynomial candidate-free local execution.

No global ClosureSearch candidate list or fuel is introduced by the
composition.
-/

namespace ConstitutiveSearch

universe uGenerator

/-- Pointwise composition of two compatible constituted-code families. -/
def composeSearchableCodeFamily
    {State : Nat → Type}
    {Generator :
      (n : Nat) →
        State n → State n → Type uGenerator}
    {source middle target :
      (n : Nat) →
        State n}
    (first :
      (n : Nat) →
        TransportCode
          (Generator n)
          (source n)
          (middle n))
    (second :
      (n : Nat) →
        TransportCode
          (Generator n)
          (middle n)
          (target n))
    (n : Nat) :
    TransportCode
      (Generator n)
      (source n)
      (target n) :=
  TransportClosure.compose
    (first n)
    (second n)

/-- Pointwise code size is exactly additive under local composition. -/
theorem composeSearchableCodeFamily_size
    {State : Nat → Type}
    {Generator :
      (n : Nat) →
        State n → State n → Type uGenerator}
    {source middle target :
      (n : Nat) →
        State n}
    (first :
      (n : Nat) →
        TransportCode
          (Generator n)
          (source n)
          (middle n))
    (second :
      (n : Nat) →
        TransportCode
          (Generator n)
          (middle n)
          (target n))
    (n : Nat) :
    (composeSearchableCodeFamily
        first
        second
        n).size =
      (first n).size +
        (second n).size := by
  rfl

/-- Searchability is closed under constituted code composition. -/
theorem composeSearchableCodeFamily_searchable
    {State : Nat → Type}
    {Generator :
      (n : Nat) →
        State n → State n → Type uGenerator}
    (primitive :
      (n : Nat) →
        RelationSearch (Generator n))
    {source middle target :
      (n : Nat) →
        State n}
    (first :
      (n : Nat) →
        TransportCode
          (Generator n)
          (source n)
          (middle n))
    (second :
      (n : Nat) →
        TransportCode
          (Generator n)
          (middle n)
          (target n))
    (firstSearchable :
      ∀ n : Nat,
        (first n).SearchableBy
          (primitive n))
    (secondSearchable :
      ∀ n : Nat,
        (second n).SearchableBy
          (primitive n)) :
    ∀ n : Nat,
      (composeSearchableCodeFamily
        first
        second
        n).SearchableBy
          (primitive n) := by
  intro n
  exact
    ⟨firstSearchable n,
      secondSearchable n⟩

/-- Input-polynomial code size is closed under constituted code composition. -/
theorem composeSearchableCodeFamily_size_inputPolynomiallyBounded
    {State : Nat → Type}
    {Generator :
      (n : Nat) →
        State n → State n → Type uGenerator}
    {source middle target :
      (n : Nat) →
        State n}
    (first :
      (n : Nat) →
        TransportCode
          (Generator n)
          (source n)
          (middle n))
    (second :
      (n : Nat) →
        TransportCode
          (Generator n)
          (middle n)
          (target n))
    (inputBits : Nat → Nat)
    (firstSizeBounded :
      InputPolynomiallyBounded
        inputBits
        (fun n =>
          (first n).size))
    (secondSizeBounded :
      InputPolynomiallyBounded
        inputBits
        (fun n =>
          (second n).size)) :
    InputPolynomiallyBounded
      inputBits
      (fun n =>
        (composeSearchableCodeFamily
          first
          second
          n).size) := by
  rcases firstSizeBounded with
    ⟨firstEnvelope, firstLe⟩
  rcases secondSizeBounded with
    ⟨secondEnvelope, secondLe⟩
  refine
    ⟨CostPolynomial.add
        firstEnvelope
        secondEnvelope,
      ?_⟩
  intro n
  rw [
    composeSearchableCodeFamily_size
  ]
  exact
    Nat.add_le_add
      (firstLe n)
      (secondLe n)

/--
Main closure theorem: locally constituted searchable code families compose
without leaving the input-polynomial candidate-free execution regime.
-/
theorem composeSearchableCodeFamily_localInputPolynomiallyBounded
    {State : Nat → Type}
    {Generator :
      (n : Nat) →
        State n → State n → Type uGenerator}
    (primitive :
      (n : Nat) →
        RelationSearch (Generator n))
    {source middle target :
      (n : Nat) →
        State n}
    (first :
      (n : Nat) →
        TransportCode
          (Generator n)
          (source n)
          (middle n))
    (second :
      (n : Nat) →
        TransportCode
          (Generator n)
          (middle n)
          (target n))
    (inputBits : Nat → Nat)
    (firstSearchable :
      ∀ n : Nat,
        (first n).SearchableBy
          (primitive n))
    (secondSearchable :
      ∀ n : Nat,
        (second n).SearchableBy
          (primitive n))
    (firstSizeBounded :
      InputPolynomiallyBounded
        inputBits
        (fun n =>
          (first n).size))
    (secondSizeBounded :
      InputPolynomiallyBounded
        inputBits
        (fun n =>
          (second n).size)) :
    LocalSearchableCodeFamilyInputPolynomiallyBounded
      primitive
      (composeSearchableCodeFamily
        first
        second)
      inputBits := by
  apply
    localSearchableCodeFamily_inputPolynomiallyBounded
      primitive
      (composeSearchableCodeFamily
        first
        second)
      inputBits
  · exact
      composeSearchableCodeFamily_searchable
        primitive
        first
        second
        firstSearchable
        secondSearchable
  · exact
      composeSearchableCodeFamily_size_inputPolynomiallyBounded
        first
        second
        inputBits
        firstSizeBounded
        secondSizeBounded

end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.composeSearchableCodeFamily
#print axioms ConstitutiveSearch.composeSearchableCodeFamily_size
#print axioms ConstitutiveSearch.composeSearchableCodeFamily_searchable
#print axioms ConstitutiveSearch.composeSearchableCodeFamily_size_inputPolynomiallyBounded
#print axioms ConstitutiveSearch.composeSearchableCodeFamily_localInputPolynomiallyBounded
/- AXIOM_AUDIT_END -/
