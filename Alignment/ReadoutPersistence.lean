import Alignment.FinitePersistence

/-!
# Readouts on finitely persistent constitutive carriers

Readout values are attached only after the finite constitutive carriers and
their exact realizations have been built.  The results below show that a
readout constructed by extension to an arbitrary natural-number depth retains its earlier values.  They do
not require arbitrary readouts to be injective and do not identify readouts
that were supplied independently.
-/

namespace Alignment

universe uInitial uOld uValue

/-- Extend an existing readout by one independently supplied fresh value. -/
def extendReadout
    {Old : Type uOld}
    {Value : Type uValue}
    (oldReadout : Old → Value)
    (freshValue : Value) :
    Old ⊕ Unit → Value
  | .inl old => oldReadout old
  | .inr _ => freshValue

@[simp] theorem extendReadout_old
    {Old : Type uOld}
    {Value : Type uValue}
    (oldReadout : Old → Value)
    (freshValue : Value)
    (old : Old) :
    extendReadout oldReadout freshValue (.inl old) = oldReadout old :=
  rfl

@[simp] theorem extendReadout_fresh
    {Old : Type uOld}
    {Value : Type uValue}
    (oldReadout : Old → Value)
    (freshValue : Value) :
    extendReadout oldReadout freshValue (.inr ()) = freshValue :=
  rfl

/-- Exactly the finite values introduced during `n` extensions. -/
def FiniteFreshValues (Value : Type uValue) : Nat → Type uValue
  | 0 => PUnit
  | n + 1 => FiniteFreshValues Value n × Value

namespace FiniteFreshValues

/-- Keep the prefix of values belonging to an earlier constitutive depth. -/
def take
    {Value : Type uValue}
    {source target : Nat} :
    DepthExtension source target →
      FiniteFreshValues Value target →
      FiniteFreshValues Value source
  | .refl _, values => values
  | .step depth, (prior, _) => take depth prior

theorem take_refl
    {Value : Type uValue}
    {n : Nat}
    (values : FiniteFreshValues Value n) :
    take (.refl n) values = values :=
  rfl

theorem take_trans
    {Value : Type uValue}
    {first middle last : Nat}
    (firstToMiddle : DepthExtension first middle)
    (middleToLast : DepthExtension middle last)
    (values : FiniteFreshValues Value last) :
    take firstToMiddle (take middleToLast values) =
      take (firstToMiddle.trans middleToLast) values := by
  induction middleToLast with
  | refl => rfl
  | step depth inductionHypothesis =>
      cases values with
      | mk prior fresh => exact inductionHypothesis prior

end FiniteFreshValues

/-- A readout assembled from initial values and one value per natural-depth extension. -/
def iteratedReadout
    {Initial : Type uInitial}
    {Value : Type uValue}
    (initialReadout : Initial → Value) :
    {n : Nat} →
      FiniteFreshValues Value n →
      IteratedCarrier Initial n →
      Value
  | 0, _, identity => initialReadout identity
  | _ + 1, (priorValues, _freshValue), .inl priorIdentity =>
      iteratedReadout initialReadout priorValues priorIdentity
  | _ + 1, (_, freshValue), .inr _ => freshValue

@[simp] theorem iteratedReadout_previous
    {Initial : Type uInitial}
    {Value : Type uValue}
    (initialReadout : Initial → Value)
    {n : Nat}
    (priorValues : FiniteFreshValues Value n)
    (freshValue : Value)
    (identity : IteratedCarrier Initial n) :
    iteratedReadout initialReadout (n := n + 1) (priorValues, freshValue)
        (IteratedCarrier.embedPrevious identity) =
      iteratedReadout initialReadout priorValues identity :=
  rfl

@[simp] theorem iteratedReadout_fresh
    {Initial : Type uInitial}
    {Value : Type uValue}
    (initialReadout : Initial → Value)
    {n : Nat}
    (priorValues : FiniteFreshValues Value n)
    (freshValue : Value) :
    iteratedReadout initialReadout (n := n + 1) (priorValues, freshValue)
        (IteratedCarrier.freshAtStep n) = freshValue :=
  rfl

/-- Values on every previously constituted identity persist to a later depth. -/
theorem iteratedReadout_embedFrom
    {Initial : Type uInitial}
    {Value : Type uValue}
    (initialReadout : Initial → Value)
    {source target : Nat}
    (depth : DepthExtension source target)
    (targetValues : FiniteFreshValues Value target)
    (identity : IteratedCarrier Initial source) :
    iteratedReadout initialReadout targetValues
        (IteratedCarrier.embedFrom depth identity) =
      iteratedReadout initialReadout
        (FiniteFreshValues.take depth targetValues) identity := by
  induction depth with
  | refl => rfl
  | step depth inductionHypothesis =>
      cases targetValues with
      | mk priorValues freshValue =>
          exact inductionHypothesis priorValues

/--
At every earlier identity, the retained readout value depends only on the
source and target depths, not on the supplied extension witness.
-/
theorem iteratedReadout_take_witness_independent
    {Initial : Type uInitial}
    {Value : Type uValue}
    (initialReadout : Initial → Value)
    {source target : Nat}
    (first second : DepthExtension source target)
    (targetValues : FiniteFreshValues Value target)
    (identity : IteratedCarrier Initial source) :
    iteratedReadout initialReadout
        (FiniteFreshValues.take first targetValues) identity =
      iteratedReadout initialReadout
        (FiniteFreshValues.take second targetValues) identity := by
  calc
    iteratedReadout initialReadout
        (FiniteFreshValues.take first targetValues) identity =
      iteratedReadout initialReadout targetValues
        (IteratedCarrier.embedFrom first identity) :=
          (iteratedReadout_embedFrom initialReadout first targetValues identity).symm
    _ = iteratedReadout initialReadout targetValues
        (IteratedCarrier.embedFrom second identity) :=
          congrArg (iteratedReadout initialReadout targetValues)
            (IteratedCarrier.embedFrom_witness_independent first second identity)
    _ = iteratedReadout initialReadout
        (FiniteFreshValues.take second targetValues) identity :=
          iteratedReadout_embedFrom initialReadout second targetValues identity

namespace FiniteFreshValues

/--
A finite value package is determined by its readout on the fresh identities.
`PEmpty` removes any unrelated initial value from this characterization.
-/
theorem eq_of_iteratedReadout_eq
    {Value : Type uValue}
    {depth : Nat}
    (first second : FiniteFreshValues Value depth)
    (agreement :
      (identity : IteratedCarrier (PEmpty : Type) depth) →
        iteratedReadout (Initial := PEmpty) PEmpty.elim first identity =
          iteratedReadout (Initial := PEmpty) PEmpty.elim second identity) :
    first = second := by
  induction depth with
  | zero =>
      cases first
      cases second
      rfl
  | succ depth inductionHypothesis =>
      cases first with
      | mk firstPrior firstFresh =>
          cases second with
          | mk secondPrior secondFresh =>
              have priorEqual : firstPrior = secondPrior :=
                inductionHypothesis firstPrior secondPrior
                  (fun identity => agreement (.inl identity))
              have freshEqual : firstFresh = secondFresh :=
                agreement (.inr ())
              cases priorEqual
              cases freshEqual
              rfl

/-- The retained finite value package is independent of the depth witness. -/
theorem take_witness_independent
    {Value : Type uValue}
    {source target : Nat}
    (first second : DepthExtension source target)
    (targetValues : FiniteFreshValues Value target) :
    take first targetValues = take second targetValues := by
  apply eq_of_iteratedReadout_eq
  intro identity
  exact iteratedReadout_take_witness_independent
    (Initial := PEmpty) PEmpty.elim first second targetValues identity

end FiniteFreshValues

/-- A distinction already made by a readout persists through extension to an arbitrary natural-number depth. -/
theorem iteratedReadout_distinction
    {Initial : Type uInitial}
    {Value : Type uValue}
    (initialReadout : Initial → Value)
    {source target : Nat}
    (depth : DepthExtension source target)
    (targetValues : FiniteFreshValues Value target)
    (first second : IteratedCarrier Initial source)
    (distinguished :
      iteratedReadout initialReadout
          (FiniteFreshValues.take depth targetValues) first ≠
        iteratedReadout initialReadout
          (FiniteFreshValues.take depth targetValues) second) :
    iteratedReadout initialReadout targetValues
        (IteratedCarrier.embedFrom depth first) ≠
      iteratedReadout initialReadout targetValues
        (IteratedCarrier.embedFrom depth second) := by
  intro collapsed
  apply distinguished
  rw [← iteratedReadout_embedFrom initialReadout depth targetValues first]
  rw [← iteratedReadout_embedFrom initialReadout depth targetValues second]
  exact collapsed

namespace FiniteConstitutiveAlignment.Realization

/-- Read a canonical finite value assignment on one exact realization. -/
def realizeReadout
    {Initial : Type uInitial}
    {Value : Type uValue}
    {depth : Nat}
    {alignment : FiniteConstitutiveAlignment Initial depth}
    (realization : alignment.Realization)
    (readout : IteratedCarrier Initial depth → Value) :
    realization.Concrete → Value :=
  fun identity => readout (realization.indexedSpoke.backward identity)

theorem realizeReadout_atIndex
    {Initial : Type uInitial}
    {Value : Type uValue}
    {depth : Nat}
    {alignment : FiniteConstitutiveAlignment Initial depth}
    (realization : alignment.Realization)
    (readout : IteratedCarrier Initial depth → Value)
    (identity : IteratedCarrier Initial depth) :
    realization.realizeReadout readout
        (realization.indexedSpoke.forward identity) = readout identity := by
  change
    readout
        (realization.indexedSpoke.backward
          (realization.indexedSpoke.forward identity)) = readout identity
  rw [realization.indexedSpoke.forwardBackward]

/-- Reindex a concrete readout through the shared finite constitutive carrier. -/
def transportReadout
    {Initial : Type uInitial}
    {Value : Type uValue}
    {depth : Nat}
    {alignment : FiniteConstitutiveAlignment Initial depth}
    (source target : alignment.Realization)
    (readout : source.Concrete → Value) :
    target.Concrete → Value :=
  fun identity => readout ((source.transport target).backward identity)

theorem transportReadout_atIndex
    {Initial : Type uInitial}
    {Value : Type uValue}
    {depth : Nat}
    {alignment : FiniteConstitutiveAlignment Initial depth}
    (source target : alignment.Realization)
    (readout : source.Concrete → Value)
    (identity : IteratedCarrier Initial depth) :
    source.transportReadout target readout
        (target.indexedSpoke.forward identity) =
      readout (source.indexedSpoke.forward identity) := by
  change
    readout
        (source.indexedSpoke.forward
          (target.indexedSpoke.backward
            (target.indexedSpoke.forward identity))) =
      readout (source.indexedSpoke.forward identity)
  rw [target.indexedSpoke.forwardBackward]

theorem transportReadout_roundTrip
    {Initial : Type uInitial}
    {Value : Type uValue}
    {depth : Nat}
    {alignment : FiniteConstitutiveAlignment Initial depth}
    (source target : alignment.Realization)
    (readout : source.Concrete → Value)
    (identity : source.Concrete) :
    target.transportReadout source
        (source.transportReadout target readout) identity = readout identity := by
  change
    readout
        ((source.transport target).backward
          ((target.transport source).backward identity)) = readout identity
  change
    readout
        ((source.transport target).backward
          ((source.transport target).forward identity)) = readout identity
  rw [(source.transport target).forwardBackward]

theorem transportReadout_comp
    {Initial : Type uInitial}
    {Value : Type uValue}
    {depth : Nat}
    {alignment : FiniteConstitutiveAlignment Initial depth}
    (source middle target : alignment.Realization)
    (readout : source.Concrete → Value)
    (identity : target.Concrete) :
    middle.transportReadout target
        (source.transportReadout middle readout) identity =
      source.transportReadout target readout identity := by
  change
    readout
        (source.indexedSpoke.forward
          (middle.indexedSpoke.backward
            (middle.indexedSpoke.forward
              (target.indexedSpoke.backward identity)))) =
      readout
        (source.indexedSpoke.forward
          (target.indexedSpoke.backward identity))
  rw [middle.indexedSpoke.forwardBackward]

/--
A finitely assembled readout persists on concrete identities extended from any
earlier depth.
-/
theorem realizeIteratedReadout_extend
    {Initial : Type uInitial}
    {Value : Type uValue}
    (initialReadout : Initial → Value)
    {sourceDepth targetDepth : Nat}
    {sourceAlignment : FiniteConstitutiveAlignment Initial sourceDepth}
    {targetAlignment : FiniteConstitutiveAlignment Initial targetDepth}
    (source : sourceAlignment.Realization)
    (target : targetAlignment.Realization)
    (depth : DepthExtension sourceDepth targetDepth)
    (targetValues : FiniteFreshValues Value targetDepth)
    (identity : source.Concrete) :
    target.realizeReadout (iteratedReadout initialReadout targetValues)
        (source.extend target depth identity) =
      source.realizeReadout
        (iteratedReadout initialReadout
          (FiniteFreshValues.take depth targetValues)) identity := by
  change
    iteratedReadout initialReadout targetValues
        (target.indexedSpoke.backward
          (target.indexedSpoke.forward
            (IteratedCarrier.embedFrom depth
              (source.indexedSpoke.backward identity)))) =
      iteratedReadout initialReadout
        (FiniteFreshValues.take depth targetValues)
        (source.indexedSpoke.backward identity)
  rw [target.indexedSpoke.forwardBackward]
  exact iteratedReadout_embedFrom initialReadout depth targetValues
    (source.indexedSpoke.backward identity)

theorem realizeIteratedReadout_distinction
    {Initial : Type uInitial}
    {Value : Type uValue}
    (initialReadout : Initial → Value)
    {sourceDepth targetDepth : Nat}
    {sourceAlignment : FiniteConstitutiveAlignment Initial sourceDepth}
    {targetAlignment : FiniteConstitutiveAlignment Initial targetDepth}
    (source : sourceAlignment.Realization)
    (target : targetAlignment.Realization)
    (depth : DepthExtension sourceDepth targetDepth)
    (targetValues : FiniteFreshValues Value targetDepth)
    (first second : source.Concrete)
    (distinguished :
      source.realizeReadout
          (iteratedReadout initialReadout
            (FiniteFreshValues.take depth targetValues)) first ≠
        source.realizeReadout
          (iteratedReadout initialReadout
            (FiniteFreshValues.take depth targetValues)) second) :
    target.realizeReadout (iteratedReadout initialReadout targetValues)
        (source.extend target depth first) ≠
      target.realizeReadout (iteratedReadout initialReadout targetValues)
        (source.extend target depth second) := by
  intro collapsed
  apply distinguished
  rw [← realizeIteratedReadout_extend initialReadout source target depth
    targetValues first]
  rw [← realizeIteratedReadout_extend initialReadout source target depth
    targetValues second]
  exact collapsed

end FiniteConstitutiveAlignment.Realization
end Alignment

/- AXIOM_AUDIT_BEGIN -/
#print axioms Alignment.iteratedReadout_embedFrom
#print axioms Alignment.iteratedReadout_take_witness_independent
#print axioms Alignment.FiniteFreshValues.eq_of_iteratedReadout_eq
#print axioms Alignment.FiniteFreshValues.take_witness_independent
#print axioms Alignment.iteratedReadout_distinction
#print axioms Alignment.FiniteConstitutiveAlignment.Realization.transportReadout_comp
#print axioms Alignment.FiniteConstitutiveAlignment.Realization.realizeIteratedReadout_extend
#print axioms Alignment.FiniteConstitutiveAlignment.Realization.realizeIteratedReadout_distinction
/- AXIOM_AUDIT_END -/
