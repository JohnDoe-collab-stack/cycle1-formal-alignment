import Alignment.Constitutive

/-!
# Finite constitutive persistence

This module derives finite-depth alignment from a common constitutive index.
Every depth retains the initial identities and adds one fresh identity.  Exact
realizations are connected horizontally through that index, while prior
identities are embedded vertically into later depths.  The two directions are
proved to commute; the commuting law is not stored as additional matching data.

No admission, specification, norm, or readout value occurs in this layer.
-/

namespace Alignment

universe uInitial uCarrier uConcrete

/-- A positively constructed finite extension from one depth to another. -/
inductive DepthExtension : Nat → Nat → Type
  | refl (n : Nat) : DepthExtension n n
  | step {source target : Nat} :
      DepthExtension source target → DepthExtension source (target + 1)

namespace DepthExtension

/-- Construct the finite extension from depth zero to any supplied depth. -/
def zeroTo : (n : Nat) → DepthExtension 0 n
  | 0 => .refl 0
  | n + 1 => .step (zeroTo n)

/-- Compose two finite depth extensions. -/
def trans
    {first middle last : Nat} :
    DepthExtension first middle →
      DepthExtension middle last →
      DepthExtension first last
  | firstToMiddle, .refl _ => firstToMiddle
  | firstToMiddle, .step middleToLast =>
      .step (trans firstToMiddle middleToLast)

/-- Forget the proof-relevant extension while retaining its arithmetic order. -/
theorem toLE
    {source target : Nat} :
    DepthExtension source target → source ≤ target
  | .refl _ => Nat.le_refl source
  | .step depth => Nat.le_succ_of_le depth.toLE

end DepthExtension

/--
The finite constitutive carrier at depth `n`: initial identities together with
the `n` identities introduced by the successive extensions.
-/
def IteratedCarrier (Initial : Type uInitial) : Nat → Type uInitial
  | 0 => Initial
  | n + 1 => IteratedCarrier Initial n ⊕ Unit

namespace IteratedCarrier

/-- Preserve every existing identity in the next finite carrier. -/
def embedPrevious
    {Initial : Type uInitial}
    {n : Nat} :
    IteratedCarrier Initial n → IteratedCarrier Initial (n + 1) :=
  fun identity => .inl identity

/-- The identity introduced at the transition from depth `n` to `n + 1`. -/
def freshAtStep
    {Initial : Type uInitial}
    (n : Nat) :
    IteratedCarrier Initial (n + 1) :=
  .inr ()

/-- Embed every identity from one depth into a later depth. -/
def embedFrom
    {Initial : Type uInitial}
    {source target : Nat}
    (depth : DepthExtension source target) :
    IteratedCarrier Initial source → IteratedCarrier Initial target :=
  match depth with
  | .refl _ => fun identity => identity
  | .step prior => fun identity => .inl (embedFrom prior identity)

/-- Embed an initial identity into any finite constitutive depth. -/
def embedInitial
    {Initial : Type uInitial}
    (n : Nat) :
    Initial → IteratedCarrier Initial n :=
  embedFrom (DepthExtension.zeroTo n)

/--
A depth-independent structural code for finite identities.  Initial identities
retain their identity; every fresh identity retains the depth at which it was
introduced.  The code deliberately forgets the later carrier in which the
identity is observed.
-/
def identityCode
    {Initial : Type uInitial} :
    {depth : Nat} → IteratedCarrier Initial depth → Initial ⊕ Nat
  | 0, identity => .inl identity
  | _ + 1, .inl identity => identityCode identity
  | n + 1, .inr () => .inr n

theorem identityCode_fresh_lt
    {Initial : Type uInitial}
    {depth freshDepth : Nat}
    (identity : IteratedCarrier Initial depth)
    (equality : identityCode identity = Sum.inr freshDepth) :
    freshDepth < depth := by
  induction depth with
  | zero =>
      cases equality
  | succ depth inductionHypothesis =>
      cases identity with
      | inl prior =>
          exact Nat.le.step (inductionHypothesis prior equality)
      | inr fresh =>
          cases fresh
          have depthEqual : depth = freshDepth := Sum.inr.inj equality
          cases depthEqual
          exact Nat.le_refl (freshDepth + 1)

/-- The structural code loses no identity information at a fixed depth. -/
theorem identityCode_injective
    {Initial : Type uInitial}
    {depth : Nat} :
    Function.Injective (@identityCode Initial depth) := by
  induction depth with
  | zero =>
      intro first second equality
      exact Sum.inl.inj equality
  | succ depth inductionHypothesis =>
      intro first second equality
      cases first with
      | inl firstPrior =>
          cases second with
          | inl secondPrior =>
              exact congrArg Sum.inl (inductionHypothesis equality)
          | inr secondFresh =>
              cases secondFresh
              exact False.elim
                (Nat.not_succ_le_self depth
                  (identityCode_fresh_lt firstPrior equality))
      | inr firstFresh =>
          cases firstFresh
          cases second with
          | inl secondPrior =>
              exact False.elim
                (Nat.not_succ_le_self depth
                  (identityCode_fresh_lt secondPrior equality.symm))
          | inr secondFresh =>
              cases secondFresh
              rfl

/-- Every finite extension preserves the same structural identity code. -/
theorem identityCode_embedFrom
    {Initial : Type uInitial}
    {source target : Nat}
    (depth : DepthExtension source target)
    (identity : IteratedCarrier Initial source) :
    identityCode (embedFrom depth identity) = identityCode identity := by
  induction depth with
  | refl => rfl
  | step prior inductionHypothesis =>
      exact inductionHypothesis

/--
The embedded identity depends only on the two depths, not on the supplied
proof-relevant path between them.  This compares the observable construction,
not the `DepthExtension` witnesses themselves.
-/
theorem embedFrom_witness_independent
    {Initial : Type uInitial}
    {source target : Nat}
    (first second : DepthExtension source target)
    (identity : IteratedCarrier Initial source) :
    embedFrom first identity = embedFrom second identity := by
  apply identityCode_injective
  exact
    (identityCode_embedFrom first identity).trans
      (identityCode_embedFrom second identity).symm

theorem embedFrom_refl
    {Initial : Type uInitial}
    {n : Nat}
    (identity : IteratedCarrier Initial n) :
    embedFrom (.refl n) identity = identity := by
  rfl

theorem embedFrom_trans
    {Initial : Type uInitial}
    {first middle last : Nat}
    (firstToMiddle : DepthExtension first middle)
    (middleToLast : DepthExtension middle last)
    (identity : IteratedCarrier Initial first) :
    embedFrom middleToLast (embedFrom firstToMiddle identity) =
      embedFrom (firstToMiddle.trans middleToLast) identity := by
  induction middleToLast with
  | refl => rfl
  | step depth inductionHypothesis =>
      exact congrArg Sum.inl inductionHypothesis

theorem embedFrom_injective
    {Initial : Type uInitial}
    {source target : Nat}
    (depth : DepthExtension source target) :
    Function.Injective (@embedFrom Initial source target depth) := by
  induction depth with
  | refl =>
      intro first second equality
      exact equality
  | step depth inductionHypothesis =>
      intro first second equality
      exact inductionHypothesis (Sum.inl.inj equality)

theorem embedFrom_ne
    {Initial : Type uInitial}
    {source target : Nat}
    (depth : DepthExtension source target)
    {first second : IteratedCarrier Initial source}
    (distinct : first ≠ second) :
    embedFrom depth first ≠ embedFrom depth second := by
  intro equality
  exact distinct (embedFrom_injective depth equality)

theorem embedInitial_injective
    {Initial : Type uInitial}
    (n : Nat) :
    Function.Injective (@embedInitial Initial n) :=
  embedFrom_injective (DepthExtension.zeroTo n)

/-- The exact old/fresh split between adjacent canonical carriers. -/
def oneStepTransport
    (Initial : Type uInitial)
    (n : Nat) :
    ExactTypeTransport
      (IteratedCarrier Initial n ⊕ Unit)
      (IteratedCarrier Initial (n + 1)) :=
  ExactTypeTransport.reflexive (IteratedCarrier Initial n ⊕ Unit)

/-- The adjacent transition as the existing exact one-step interface. -/
def oneStepAlignment
    (Initial : Type uInitial)
    (n : Nat) :
    ExactOneStepConstitutiveAlignment :=
  { Initial := IteratedCarrier Initial n
    Extended := IteratedCarrier Initial (n + 1)
    extension := oneStepTransport Initial n }

theorem embedPrevious_injective
    {Initial : Type uInitial}
    {n : Nat} :
    Function.Injective (@embedPrevious Initial n) :=
  (oneStepAlignment Initial n).old_injective

theorem embedPrevious_ne_fresh
    {Initial : Type uInitial}
    {n : Nat}
    (identity : IteratedCarrier Initial n) :
    embedPrevious identity ≠ freshAtStep n :=
  (oneStepAlignment Initial n).old_ne_fresh identity

/-- The old/fresh distinction survives every supplied later extension. -/
theorem embedPrevious_ne_fresh_later
    {Initial : Type uInitial}
    {n target : Nat}
    (depth : DepthExtension (n + 1) target)
    (identity : IteratedCarrier Initial n) :
    embedFrom depth (embedPrevious identity) ≠
      embedFrom depth (freshAtStep n) :=
  embedFrom_ne depth (embedPrevious_ne_fresh identity)

theorem embedPrevious_eq_embedFrom
    {Initial : Type uInitial}
    {n : Nat}
    (identity : IteratedCarrier Initial n) :
    embedPrevious identity =
      embedFrom (.step (.refl n)) identity := by
  rfl

end IteratedCarrier

/--
One carrier at a finite constitutive depth, exactly indexed by the canonical
finite carrier.  Intermediate depths remain separate instances of this
structure rather than being collapsed into the final carrier.
-/
structure FiniteConstitutiveAlignment
    (Initial : Type uInitial)
    (depth : Nat) where
  Carrier : Type uCarrier
  carrierSpoke : ExactTypeTransport (IteratedCarrier Initial depth) Carrier

namespace FiniteConstitutiveAlignment

/-- One exact concrete realization of a finite-depth constitutive carrier. -/
structure Realization
    {Initial : Type uInitial}
    {depth : Nat}
    (alignment : FiniteConstitutiveAlignment Initial depth) where
  Concrete : Type uConcrete
  spoke : ExactTypeTransport alignment.Carrier Concrete

namespace Realization

/-- The derived spoke from the common finite index to one concrete carrier. -/
def indexedSpoke
    {Initial : Type uInitial}
    {depth : Nat}
    {alignment : FiniteConstitutiveAlignment Initial depth}
    (realization : alignment.Realization) :
    ExactTypeTransport (IteratedCarrier Initial depth) realization.Concrete :=
  alignment.carrierSpoke.compose realization.spoke

/-- The backward map of every exact indexed spoke is injective. -/
theorem indexedSpoke_backward_injective
    {Initial : Type uInitial}
    {depth : Nat}
    {alignment : FiniteConstitutiveAlignment Initial depth}
    (realization : alignment.Realization) :
    Function.Injective realization.indexedSpoke.backward := by
  intro first second equality
  calc
    first =
        realization.indexedSpoke.forward
          (realization.indexedSpoke.backward first) :=
      (realization.indexedSpoke.backwardForward first).symm
    _ =
        realization.indexedSpoke.forward
          (realization.indexedSpoke.backward second) :=
      congrArg realization.indexedSpoke.forward equality
    _ = second :=
      realization.indexedSpoke.backwardForward second

/-- Change concrete realization at one fixed constitutive depth. -/
def transport
    {Initial : Type uInitial}
    {depth : Nat}
    {alignment : FiniteConstitutiveAlignment Initial depth}
    (source target : alignment.Realization) :
    ExactTypeTransport source.Concrete target.Concrete :=
  source.indexedSpoke.reverse.compose target.indexedSpoke

/-- Extend a concrete identity from one depth to a later depth. -/
def extend
    {Initial : Type uInitial}
    {sourceDepth targetDepth : Nat}
    {sourceAlignment : FiniteConstitutiveAlignment Initial sourceDepth}
    {targetAlignment : FiniteConstitutiveAlignment Initial targetDepth}
    (source : sourceAlignment.Realization)
    (target : targetAlignment.Realization)
    (depth : DepthExtension sourceDepth targetDepth) :
    source.Concrete → target.Concrete :=
  fun identity =>
    target.indexedSpoke.forward
      (IteratedCarrier.embedFrom depth
        (source.indexedSpoke.backward identity))

theorem transport_atIndex
    {Initial : Type uInitial}
    {depth : Nat}
    {alignment : FiniteConstitutiveAlignment Initial depth}
    (source target : alignment.Realization)
    (identity : IteratedCarrier Initial depth) :
    (source.transport target).forward (source.indexedSpoke.forward identity) =
      target.indexedSpoke.forward identity := by
  change
    target.indexedSpoke.forward
        (source.indexedSpoke.backward
          (source.indexedSpoke.forward identity)) =
      target.indexedSpoke.forward identity
  rw [source.indexedSpoke.forwardBackward]

theorem transport_roundTrip
    {Initial : Type uInitial}
    {depth : Nat}
    {alignment : FiniteConstitutiveAlignment Initial depth}
    (source target : alignment.Realization)
    (identity : source.Concrete) :
    (target.transport source).forward
        ((source.transport target).forward identity) = identity := by
  exact (source.transport target).forwardBackward identity

theorem transport_comp
    {Initial : Type uInitial}
    {depth : Nat}
    {alignment : FiniteConstitutiveAlignment Initial depth}
    (source middle target : alignment.Realization)
    (identity : source.Concrete) :
    (middle.transport target).forward
        ((source.transport middle).forward identity) =
      (source.transport target).forward identity := by
  change
    target.indexedSpoke.forward
        (middle.indexedSpoke.backward
          (middle.indexedSpoke.forward
            (source.indexedSpoke.backward identity))) =
      target.indexedSpoke.forward (source.indexedSpoke.backward identity)
  rw [middle.indexedSpoke.forwardBackward]

theorem extend_atIndex
    {Initial : Type uInitial}
    {sourceDepth targetDepth : Nat}
    {sourceAlignment : FiniteConstitutiveAlignment Initial sourceDepth}
    {targetAlignment : FiniteConstitutiveAlignment Initial targetDepth}
    (source : sourceAlignment.Realization)
    (target : targetAlignment.Realization)
    (depth : DepthExtension sourceDepth targetDepth)
    (identity : IteratedCarrier Initial sourceDepth) :
    source.extend target depth (source.indexedSpoke.forward identity) =
      target.indexedSpoke.forward (IteratedCarrier.embedFrom depth identity) := by
  change
    target.indexedSpoke.forward
        (IteratedCarrier.embedFrom depth
          (source.indexedSpoke.backward
            (source.indexedSpoke.forward identity))) =
      target.indexedSpoke.forward (IteratedCarrier.embedFrom depth identity)
  rw [source.indexedSpoke.forwardBackward]

/-- Concrete finite extension is independent of its depth witness. -/
theorem extend_witness_independent
    {Initial : Type uInitial}
    {sourceDepth targetDepth : Nat}
    {sourceAlignment : FiniteConstitutiveAlignment Initial sourceDepth}
    {targetAlignment : FiniteConstitutiveAlignment Initial targetDepth}
    (source : sourceAlignment.Realization)
    (target : targetAlignment.Realization)
    (first second : DepthExtension sourceDepth targetDepth)
    (identity : source.Concrete) :
    source.extend target first identity =
      source.extend target second identity := by
  exact congrArg target.indexedSpoke.forward
    (IteratedCarrier.embedFrom_witness_independent first second
      (source.indexedSpoke.backward identity))

theorem extend_refl
    {Initial : Type uInitial}
    {depth : Nat}
    {alignment : FiniteConstitutiveAlignment Initial depth}
    (realization : alignment.Realization)
    (identity : realization.Concrete) :
    realization.extend realization (.refl depth) identity = identity := by
  change
    realization.indexedSpoke.forward
        (IteratedCarrier.embedFrom (.refl depth)
          (realization.indexedSpoke.backward identity)) = identity
  rw [IteratedCarrier.embedFrom_refl]
  exact realization.indexedSpoke.backwardForward identity

theorem extend_comp
    {Initial : Type uInitial}
    {firstDepth middleDepth lastDepth : Nat}
    {firstAlignment : FiniteConstitutiveAlignment Initial firstDepth}
    {middleAlignment : FiniteConstitutiveAlignment Initial middleDepth}
    {lastAlignment : FiniteConstitutiveAlignment Initial lastDepth}
    (first : firstAlignment.Realization)
    (middle : middleAlignment.Realization)
    (last : lastAlignment.Realization)
    (firstToMiddle : DepthExtension firstDepth middleDepth)
    (middleToLast : DepthExtension middleDepth lastDepth)
    (identity : first.Concrete) :
    middle.extend last middleToLast
        (first.extend middle firstToMiddle identity) =
      first.extend last (firstToMiddle.trans middleToLast) identity := by
  change
    last.indexedSpoke.forward
        (IteratedCarrier.embedFrom middleToLast
          (middle.indexedSpoke.backward
            (middle.indexedSpoke.forward
              (IteratedCarrier.embedFrom firstToMiddle
                (first.indexedSpoke.backward identity))))) =
      last.indexedSpoke.forward
        (IteratedCarrier.embedFrom (firstToMiddle.trans middleToLast)
          (first.indexedSpoke.backward identity))
  rw [middle.indexedSpoke.forwardBackward]
  rw [IteratedCarrier.embedFrom_trans]

/--
Finite extension commutes with change of exact realization.  This is the
two-axis coherence law: extending then changing realization gives the same
concrete identity as changing realization then extending.
-/
theorem extend_transport_natural
    {Initial : Type uInitial}
    {sourceDepth targetDepth : Nat}
    {sourceAlignment : FiniteConstitutiveAlignment Initial sourceDepth}
    {targetAlignment : FiniteConstitutiveAlignment Initial targetDepth}
    (sourceA sourceB : sourceAlignment.Realization)
    (targetA targetB : targetAlignment.Realization)
    (depth : DepthExtension sourceDepth targetDepth)
    (identity : sourceA.Concrete) :
    (targetA.transport targetB).forward
        (sourceA.extend targetA depth identity) =
      sourceB.extend targetB depth
        ((sourceA.transport sourceB).forward identity) := by
  change
    targetB.indexedSpoke.forward
        (targetA.indexedSpoke.backward
          (targetA.indexedSpoke.forward
            (IteratedCarrier.embedFrom depth
              (sourceA.indexedSpoke.backward identity)))) =
      targetB.indexedSpoke.forward
        (IteratedCarrier.embedFrom depth
          (sourceB.indexedSpoke.backward
            (sourceB.indexedSpoke.forward
              (sourceA.indexedSpoke.backward identity))))
  rw [targetA.indexedSpoke.forwardBackward]
  rw [sourceB.indexedSpoke.forwardBackward]

end Realization
end FiniteConstitutiveAlignment
end Alignment

/- AXIOM_AUDIT_BEGIN -/
#print axioms Alignment.IteratedCarrier.oneStepTransport
#print axioms Alignment.IteratedCarrier.identityCode_injective
#print axioms Alignment.IteratedCarrier.identityCode_embedFrom
#print axioms Alignment.IteratedCarrier.embedFrom_witness_independent
#print axioms Alignment.IteratedCarrier.embedFrom_injective
#print axioms Alignment.IteratedCarrier.embedInitial_injective
#print axioms Alignment.IteratedCarrier.embedPrevious_ne_fresh_later
#print axioms Alignment.FiniteConstitutiveAlignment
#print axioms Alignment.FiniteConstitutiveAlignment.Realization.indexedSpoke_backward_injective
#print axioms Alignment.FiniteConstitutiveAlignment.Realization.extend_witness_independent
#print axioms Alignment.FiniteConstitutiveAlignment.Realization.extend_comp
#print axioms Alignment.FiniteConstitutiveAlignment.Realization.extend_transport_natural
/- AXIOM_AUDIT_END -/
