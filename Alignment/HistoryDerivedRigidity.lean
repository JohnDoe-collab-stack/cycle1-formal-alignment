import Alignment.HistoryDerivedAlignment

/-!
# Rigidity of history-derived alignment

The chronology relation derived from a finite proof-relevant history is not
merely separating. Its locally generated equality pattern is rigid: every exact
self-transport preserving that pattern fixes every occurrence.

Therefore any two compatible history-derived alignments agree pointwise, and
the same uniqueness propagates through arbitrary natural-depth persistence.
-/

namespace Alignment
namespace GenesisReconstruction
namespace HistoryDerivedAlignment

open StrongPerimetralTurning

universe uState uTargetState uStep

/-- Equality of local chronology observations is exactly equality of their Bool fields. -/
theorem historyRelation_eq_iff_bool_eq
    {State : Type uState}
    {Step : State → State → Type uStep}
    {source target : State}
    {history : History Step source target}
    (first second third fourth : History.Occurrence history) :
    historyRelation first second = historyRelation third fourth ↔
      occurrencePrecedesBool first second =
        occurrencePrecedesBool third fourth := by
  constructor
  · intro equality
    exact congrArg LocalChronologyObservation.precedes equality
  · intro equality
    exact
      congrArg
        (fun value =>
          (⟨value⟩ :
            LocalChronologyObservation (History.Occurrence history)))
        equality

/--
A pattern-preserving exact self-transport preserves and reflects the structural
precedence order.
-/
theorem precedes_iff_of_boolPattern
    {State : Type uState}
    {Step : State → State → Type uStep}
    {source target : State}
    {history : History Step source target}
    (automorphism :
      ExactTypeTransport
        (History.Occurrence history)
        (History.Occurrence history))
    (preserves :
      ∀ first second third fourth : History.Occurrence history,
        (occurrencePrecedesBool first second =
            occurrencePrecedesBool third fourth) ↔
          (occurrencePrecedesBool
              (automorphism.forward first)
              (automorphism.forward second) =
            occurrencePrecedesBool
              (automorphism.forward third)
              (automorphism.forward fourth)))
    (first second : History.Occurrence history) :
    History.OccurrencePrecedes first second ↔
      History.OccurrencePrecedes
        (automorphism.forward first)
        (automorphism.forward second) := by
  constructor
  · intro precedes
    have sourceDistinct :
        occurrencePrecedesBool first second ≠
          occurrencePrecedesBool first first := by
      intro equality
      rw [occurrencePrecedesBool_true_of_precedes precedes,
        occurrencePrecedesBool_self] at equality
      cases equality
    have targetDistinct :
        occurrencePrecedesBool
            (automorphism.forward first)
            (automorphism.forward second) ≠
          occurrencePrecedesBool
            (automorphism.forward first)
            (automorphism.forward first) := by
      intro equality
      exact sourceDistinct ((preserves first second first first).mpr equality)
    cases targetValue :
        occurrencePrecedesBool
          (automorphism.forward first)
          (automorphism.forward second) with
    | false =>
        have diagonal :=
          occurrencePrecedesBool_self (automorphism.forward first)
        exact False.elim
          (targetDistinct (targetValue.trans diagonal.symm))
    | true =>
        exact
          occurrencePrecedes_of_bool_true
            (automorphism.forward first)
            (automorphism.forward second)
            targetValue
  · intro precedes
    have targetDistinct :
        occurrencePrecedesBool
            (automorphism.forward first)
            (automorphism.forward second) ≠
          occurrencePrecedesBool
            (automorphism.forward first)
            (automorphism.forward first) := by
      intro equality
      rw [occurrencePrecedesBool_true_of_precedes precedes,
        occurrencePrecedesBool_self] at equality
      cases equality
    have sourceDistinct :
        occurrencePrecedesBool first second ≠
          occurrencePrecedesBool first first := by
      intro equality
      exact targetDistinct ((preserves first second first first).mp equality)
    cases sourceValue : occurrencePrecedesBool first second with
    | false =>
        have diagonal := occurrencePrecedesBool_self first
        exact False.elim
          (sourceDistinct (sourceValue.trans diagonal.symm))
    | true =>
        exact occurrencePrecedes_of_bool_true first second sourceValue

/-- The latest occurrence is fixed by every pattern-preserving automorphism. -/
theorem latest_fixed_of_boolPattern
    {State : Type uState}
    {Step : State → State → Type uStep}
    {source middle target : State}
    {previous : History Step source middle}
    {step : Step middle target}
    (automorphism :
      ExactTypeTransport
        (History.Occurrence (.extend previous step))
        (History.Occurrence (.extend previous step)))
    (preserves :
      ∀ first second third fourth :
          History.Occurrence (.extend previous step),
        (occurrencePrecedesBool first second =
            occurrencePrecedesBool third fourth) ↔
          (occurrencePrecedesBool
              (automorphism.forward first)
              (automorphism.forward second) =
            occurrencePrecedesBool
              (automorphism.forward third)
              (automorphism.forward fourth))) :
    automorphism.forward
        (History.Occurrence.last :
          History.Occurrence (.extend previous step)) =
      History.Occurrence.last := by
  cases image :
      automorphism.forward
        (History.Occurrence.last :
          History.Occurrence (.extend previous step)) with
  | last =>
      rfl
  | earlier moved =>
      let preimage :=
        automorphism.backward
          (History.Occurrence.last :
            History.Occurrence (.extend previous step))
      have targetPrecedes :
          History.OccurrencePrecedes
            (automorphism.forward
              (History.Occurrence.last :
                History.Occurrence (.extend previous step)))
            (automorphism.forward preimage) := by
        rw [image, automorphism.backwardForward]
        exact .earlier_last moved
      have sourcePrecedes :
          History.OccurrencePrecedes
            (History.Occurrence.last :
              History.Occurrence (.extend previous step))
            preimage :=
        (precedes_iff_of_boolPattern
          automorphism preserves
          History.Occurrence.last preimage).mpr targetPrecedes
      cases sourcePrecedes

/-- Backward transport fixes the latest occurrence once the forward map does. -/
theorem latest_backward_fixed
    {State : Type uState}
    {Step : State → State → Type uStep}
    {source middle target : State}
    {previous : History Step source middle}
    {step : Step middle target}
    (automorphism :
      ExactTypeTransport
        (History.Occurrence (.extend previous step))
        (History.Occurrence (.extend previous step)))
    (latestFixed :
      automorphism.forward
          (History.Occurrence.last :
            History.Occurrence (.extend previous step)) =
        History.Occurrence.last) :
    automorphism.backward
        (History.Occurrence.last :
          History.Occurrence (.extend previous step)) =
      History.Occurrence.last := by
  apply forward_injective automorphism
  calc
    automorphism.forward
        (automorphism.backward
          (History.Occurrence.last :
            History.Occurrence (.extend previous step))) =
      History.Occurrence.last :=
        automorphism.backwardForward _
    _ = automorphism.forward History.Occurrence.last :=
      latestFixed.symm

/-- Remove the latest constructor from an occurrence known not to be latest. -/
def previousOfOccurrence
    {State : Type uState}
    {Step : State → State → Type uStep}
    {source middle target : State}
    {previous : History Step source middle}
    {step : Step middle target}
    (occurrence : History.Occurrence (.extend previous step))
    (notLatest :
      occurrence ≠
        (History.Occurrence.last :
          History.Occurrence (.extend previous step))) :
    History.Occurrence previous :=
  match occurrence with
  | .last => False.elim (notLatest rfl)
  | .earlier prior => prior

theorem previousOfOccurrence_spec
    {State : Type uState}
    {Step : State → State → Type uStep}
    {source middle target : State}
    {previous : History Step source middle}
    {step : Step middle target}
    (occurrence : History.Occurrence (.extend previous step))
    (notLatest :
      occurrence ≠
        (History.Occurrence.last :
          History.Occurrence (.extend previous step))) :
    History.Occurrence.earlier
        (previousOfOccurrence occurrence notLatest) =
      occurrence := by
  cases occurrence with
  | last =>
      exact False.elim (notLatest rfl)
  | earlier prior =>
      rfl

theorem forward_earlier_ne_latest
    {State : Type uState}
    {Step : State → State → Type uStep}
    {source middle target : State}
    {previous : History Step source middle}
    {step : Step middle target}
    (automorphism :
      ExactTypeTransport
        (History.Occurrence (.extend previous step))
        (History.Occurrence (.extend previous step)))
    (latestFixed :
      automorphism.forward
          (History.Occurrence.last :
            History.Occurrence (.extend previous step)) =
        History.Occurrence.last)
    (occurrence : History.Occurrence previous) :
    automorphism.forward (History.Occurrence.earlier occurrence) ≠
      (History.Occurrence.last :
        History.Occurrence (.extend previous step)) := by
  intro equality
  have sameImage :
      automorphism.forward (History.Occurrence.earlier occurrence) =
        automorphism.forward
          (History.Occurrence.last :
            History.Occurrence (.extend previous step)) :=
    equality.trans latestFixed.symm
  have impossible :=
    forward_injective automorphism sameImage
  cases impossible

theorem backward_earlier_ne_latest
    {State : Type uState}
    {Step : State → State → Type uStep}
    {source middle target : State}
    {previous : History Step source middle}
    {step : Step middle target}
    (automorphism :
      ExactTypeTransport
        (History.Occurrence (.extend previous step))
        (History.Occurrence (.extend previous step)))
    (latestBackwardFixed :
      automorphism.backward
          (History.Occurrence.last :
            History.Occurrence (.extend previous step)) =
        History.Occurrence.last)
    (occurrence : History.Occurrence previous) :
    automorphism.backward (History.Occurrence.earlier occurrence) ≠
      (History.Occurrence.last :
        History.Occurrence (.extend previous step)) := by
  intro equality
  have sameImage :
      automorphism.backward (History.Occurrence.earlier occurrence) =
        automorphism.backward
          (History.Occurrence.last :
            History.Occurrence (.extend previous step)) :=
    equality.trans latestBackwardFixed.symm
  have impossible :=
    backward_injective automorphism sameImage
  cases impossible

/-- Restrict a latest-fixing automorphism to the previous history carrier. -/
def restrictPrevious
    {State : Type uState}
    {Step : State → State → Type uStep}
    {source middle target : State}
    {previous : History Step source middle}
    {step : Step middle target}
    (automorphism :
      ExactTypeTransport
        (History.Occurrence (.extend previous step))
        (History.Occurrence (.extend previous step)))
    (latestFixed :
      automorphism.forward
          (History.Occurrence.last :
            History.Occurrence (.extend previous step)) =
        History.Occurrence.last) :
    ExactTypeTransport
      (History.Occurrence previous)
      (History.Occurrence previous) := by
  let latestBackwardFixed :=
    latest_backward_fixed automorphism latestFixed
  let forward :
      History.Occurrence previous →
        History.Occurrence previous :=
    fun occurrence =>
      previousOfOccurrence
        (automorphism.forward
          (History.Occurrence.earlier occurrence))
        (forward_earlier_ne_latest
          automorphism latestFixed occurrence)
  let backward :
      History.Occurrence previous →
        History.Occurrence previous :=
    fun occurrence =>
      previousOfOccurrence
        (automorphism.backward
          (History.Occurrence.earlier occurrence))
        (backward_earlier_ne_latest
          automorphism latestBackwardFixed occurrence)
  exact
    { forward := forward
      backward := backward
      forwardBackward := by
        intro occurrence
        apply History.Occurrence.earlier.inj
        calc
          History.Occurrence.earlier
              (backward (forward occurrence)) =
            automorphism.backward
              (History.Occurrence.earlier
                (forward occurrence)) :=
              previousOfOccurrence_spec _ _
          _ = automorphism.backward
              (automorphism.forward
                (History.Occurrence.earlier occurrence)) := by
              rw [previousOfOccurrence_spec
                (automorphism.forward
                  (History.Occurrence.earlier occurrence))
                (forward_earlier_ne_latest
                  automorphism latestFixed occurrence)]
          _ = History.Occurrence.earlier occurrence :=
              automorphism.forwardBackward _
      backwardForward := by
        intro occurrence
        apply History.Occurrence.earlier.inj
        calc
          History.Occurrence.earlier
              (forward (backward occurrence)) =
            automorphism.forward
              (History.Occurrence.earlier
                (backward occurrence)) :=
              previousOfOccurrence_spec _ _
          _ = automorphism.forward
              (automorphism.backward
                (History.Occurrence.earlier occurrence)) := by
              rw [previousOfOccurrence_spec
                (automorphism.backward
                  (History.Occurrence.earlier occurrence))
                (backward_earlier_ne_latest
                  automorphism latestBackwardFixed occurrence)]
          _ = History.Occurrence.earlier occurrence :=
              automorphism.backwardForward _ }

/-- The restricted forward map is exactly the old component of the full map. -/
theorem restrictPrevious_forward_spec
    {State : Type uState}
    {Step : State → State → Type uStep}
    {source middle target : State}
    {previous : History Step source middle}
    {step : Step middle target}
    (automorphism :
      ExactTypeTransport
        (History.Occurrence (.extend previous step))
        (History.Occurrence (.extend previous step)))
    (latestFixed :
      automorphism.forward
          (History.Occurrence.last :
            History.Occurrence (.extend previous step)) =
        History.Occurrence.last)
    (occurrence : History.Occurrence previous) :
    History.Occurrence.earlier
        ((restrictPrevious automorphism latestFixed).forward occurrence) =
      automorphism.forward (History.Occurrence.earlier occurrence) := by
  unfold restrictPrevious
  exact previousOfOccurrence_spec _ _

/-- Pattern preservation descends to the previous history. -/
theorem restrictPrevious_preservesBoolPattern
    {State : Type uState}
    {Step : State → State → Type uStep}
    {source middle target : State}
    {previous : History Step source middle}
    {step : Step middle target}
    (automorphism :
      ExactTypeTransport
        (History.Occurrence (.extend previous step))
        (History.Occurrence (.extend previous step)))
    (preserves :
      ∀ first second third fourth :
          History.Occurrence (.extend previous step),
        (occurrencePrecedesBool first second =
            occurrencePrecedesBool third fourth) ↔
          (occurrencePrecedesBool
              (automorphism.forward first)
              (automorphism.forward second) =
            occurrencePrecedesBool
              (automorphism.forward third)
              (automorphism.forward fourth)))
    (latestFixed :
      automorphism.forward
          (History.Occurrence.last :
            History.Occurrence (.extend previous step)) =
        History.Occurrence.last)
    (first second third fourth : History.Occurrence previous) :
    (occurrencePrecedesBool first second =
        occurrencePrecedesBool third fourth) ↔
      (occurrencePrecedesBool
          ((restrictPrevious automorphism latestFixed).forward first)
          ((restrictPrevious automorphism latestFixed).forward second) =
        occurrencePrecedesBool
          ((restrictPrevious automorphism latestFixed).forward third)
          ((restrictPrevious automorphism latestFixed).forward fourth)) := by
  let lift :
      History.Occurrence previous →
        History.Occurrence (.extend previous step) :=
    fun occurrence =>
      History.Occurrence.earlier (step := step) occurrence
  constructor
  · intro sourceEquality
    have extendedSource :
        occurrencePrecedesBool (lift first) (lift second) =
          occurrencePrecedesBool (lift third) (lift fourth) := by
      exact sourceEquality
    have extendedTarget :=
      (preserves
        (lift first) (lift second) (lift third) (lift fourth)).mp
        extendedSource
    have firstSpec :=
      restrictPrevious_forward_spec automorphism latestFixed first
    have secondSpec :=
      restrictPrevious_forward_spec automorphism latestFixed second
    have thirdSpec :=
      restrictPrevious_forward_spec automorphism latestFixed third
    have fourthSpec :=
      restrictPrevious_forward_spec automorphism latestFixed fourth
    change
      lift ((restrictPrevious automorphism latestFixed).forward first) =
        automorphism.forward (lift first) at firstSpec
    change
      lift ((restrictPrevious automorphism latestFixed).forward second) =
        automorphism.forward (lift second) at secondSpec
    change
      lift ((restrictPrevious automorphism latestFixed).forward third) =
        automorphism.forward (lift third) at thirdSpec
    change
      lift ((restrictPrevious automorphism latestFixed).forward fourth) =
        automorphism.forward (lift fourth) at fourthSpec
    rw [← firstSpec, ← secondSpec, ← thirdSpec, ← fourthSpec]
      at extendedTarget
    exact extendedTarget
  · intro targetEquality
    have extendedTarget :
        occurrencePrecedesBool
            (lift ((restrictPrevious automorphism latestFixed).forward first))
            (lift ((restrictPrevious automorphism latestFixed).forward second)) =
          occurrencePrecedesBool
            (lift ((restrictPrevious automorphism latestFixed).forward third))
            (lift ((restrictPrevious automorphism latestFixed).forward fourth)) := by
      exact targetEquality
    have firstSpec :=
      restrictPrevious_forward_spec automorphism latestFixed first
    have secondSpec :=
      restrictPrevious_forward_spec automorphism latestFixed second
    have thirdSpec :=
      restrictPrevious_forward_spec automorphism latestFixed third
    have fourthSpec :=
      restrictPrevious_forward_spec automorphism latestFixed fourth
    change
      lift ((restrictPrevious automorphism latestFixed).forward first) =
        automorphism.forward (lift first) at firstSpec
    change
      lift ((restrictPrevious automorphism latestFixed).forward second) =
        automorphism.forward (lift second) at secondSpec
    change
      lift ((restrictPrevious automorphism latestFixed).forward third) =
        automorphism.forward (lift third) at thirdSpec
    change
      lift ((restrictPrevious automorphism latestFixed).forward fourth) =
        automorphism.forward (lift fourth) at fourthSpec
    rw [firstSpec, secondSpec, thirdSpec, fourthSpec] at extendedTarget
    have extendedSource :=
      (preserves
        (lift first) (lift second) (lift third) (lift fourth)).mpr
        extendedTarget
    exact extendedSource

/-- Every Boolean-pattern-preserving history automorphism is pointwise fixed. -/
theorem forward_fixed_of_boolPattern
    {State : Type uState}
    {Step : State → State → Type uStep}
    {source target : State}
    (history : History Step source target)
    (automorphism :
      ExactTypeTransport
        (History.Occurrence history)
        (History.Occurrence history))
    (preserves :
      ∀ first second third fourth : History.Occurrence history,
        (occurrencePrecedesBool first second =
            occurrencePrecedesBool third fourth) ↔
          (occurrencePrecedesBool
              (automorphism.forward first)
              (automorphism.forward second) =
            occurrencePrecedesBool
              (automorphism.forward third)
              (automorphism.forward fourth)))
    (identity : History.Occurrence history) :
    automorphism.forward identity = identity := by
  induction history with
  | root =>
      exact nomatch identity
  | extend previous step inductionHypothesis =>
      have latestFixed :=
        latest_fixed_of_boolPattern automorphism preserves
      cases identity with
      | last =>
          exact latestFixed
      | earlier prior =>
          let restricted := restrictPrevious automorphism latestFixed
          have restrictedPreserves :
              ∀ first second third fourth : History.Occurrence previous,
                (occurrencePrecedesBool first second =
                    occurrencePrecedesBool third fourth) ↔
                  (occurrencePrecedesBool
                      (restricted.forward first)
                      (restricted.forward second) =
                    occurrencePrecedesBool
                      (restricted.forward third)
                      (restricted.forward fourth)) :=
            restrictPrevious_preservesBoolPattern
              automorphism preserves latestFixed
          have priorFixed :=
            inductionHypothesis restricted restrictedPreserves prior
          calc
            automorphism.forward (History.Occurrence.earlier prior) =
                History.Occurrence.earlier (restricted.forward prior) :=
              (restrictPrevious_forward_spec
                automorphism latestFixed prior).symm
            _ = History.Occurrence.earlier prior :=
              congrArg History.Occurrence.earlier priorFixed

/-- The relation generated by every finite history is pattern-rigid. -/
theorem historyRelation_patternRigid
    {State : Type uState}
    {Step : State → State → Type uStep}
    {source target : State}
    {history : History Step source target} :
    RelationalPatternRigid
      (@historyRelation State Step source target history) := by
  intro automorphism preserves identity
  apply forward_fixed_of_boolPattern history automorphism
  · intro first second third fourth
    constructor
    · intro sourceEquality
      have sourceRelationEquality :=
        (historyRelation_eq_iff_bool_eq
          first second third fourth).mpr sourceEquality
      have targetRelationEquality :=
        (preserves first second third fourth).mp sourceRelationEquality
      exact
        (historyRelation_eq_iff_bool_eq
          (automorphism.forward first)
          (automorphism.forward second)
          (automorphism.forward third)
          (automorphism.forward fourth)).mp
            targetRelationEquality
    · intro targetEquality
      have targetRelationEquality :=
        (historyRelation_eq_iff_bool_eq
          (automorphism.forward first)
          (automorphism.forward second)
          (automorphism.forward third)
          (automorphism.forward fourth)).mpr
            targetEquality
      have sourceRelationEquality :=
        (preserves first second third fourth).mpr targetRelationEquality
      exact
        (historyRelation_eq_iff_bool_eq
          first second third fourth).mp sourceRelationEquality

/-- Any two closed history-derived alignments agree on their initial forward map. -/
theorem constitutiveAlignment_forward_unique
    {SourceState : Type uState}
    {SourceStep : SourceState → SourceState → Type uStep}
    {sourceStart sourceEnd : SourceState}
    (sourceHistory : History SourceStep sourceStart sourceEnd)
    {TargetState : Type uTargetState}
    {TargetStep : TargetState → TargetState → Type uStep}
    {targetStart targetEnd : TargetState}
    (targetHistory : History TargetStep targetStart targetEnd)
    (first second : ConstitutiveAlignment sourceHistory targetHistory)
    (identity : History.Occurrence sourceHistory) :
    first.initial.transport.forward identity =
      second.initial.transport.forward identity :=
  first.initial.forward_unique_of_targetPatternRigidity
    historyRelation_patternRigid second.initial identity

/-- The same canonicity propagates through every requested natural depth. -/
theorem constitutiveAlignment_depth_forward_unique
    {SourceState : Type uState}
    {SourceStep : SourceState → SourceState → Type uStep}
    {sourceStart sourceEnd : SourceState}
    (sourceHistory : History SourceStep sourceStart sourceEnd)
    {TargetState : Type uTargetState}
    {TargetStep : TargetState → TargetState → Type uStep}
    {targetStart targetEnd : TargetState}
    (targetHistory : History TargetStep targetStart targetEnd)
    (first second : ConstitutiveAlignment sourceHistory targetHistory)
    (depth : Nat)
    (identity : IteratedCarrier (History.Occurrence sourceHistory) depth) :
    (first.transportAtDepth depth).forward identity =
      (second.transportAtDepth depth).forward identity :=
  first.transportAtDepth_forward_unique_of_targetPatternRigidity
    historyRelation_patternRigid second depth identity

end HistoryDerivedAlignment
end GenesisReconstruction
end Alignment

/- AXIOM_AUDIT_BEGIN -/
#print axioms Alignment.GenesisReconstruction.HistoryDerivedAlignment.historyRelation_eq_iff_bool_eq
#print axioms Alignment.GenesisReconstruction.HistoryDerivedAlignment.precedes_iff_of_boolPattern
#print axioms Alignment.GenesisReconstruction.HistoryDerivedAlignment.latest_fixed_of_boolPattern
#print axioms Alignment.GenesisReconstruction.HistoryDerivedAlignment.latest_backward_fixed
#print axioms Alignment.GenesisReconstruction.HistoryDerivedAlignment.previousOfOccurrence
#print axioms Alignment.GenesisReconstruction.HistoryDerivedAlignment.previousOfOccurrence_spec
#print axioms Alignment.GenesisReconstruction.HistoryDerivedAlignment.forward_earlier_ne_latest
#print axioms Alignment.GenesisReconstruction.HistoryDerivedAlignment.backward_earlier_ne_latest
#print axioms Alignment.GenesisReconstruction.HistoryDerivedAlignment.restrictPrevious
#print axioms Alignment.GenesisReconstruction.HistoryDerivedAlignment.restrictPrevious_forward_spec
#print axioms Alignment.GenesisReconstruction.HistoryDerivedAlignment.restrictPrevious_preservesBoolPattern
#print axioms Alignment.GenesisReconstruction.HistoryDerivedAlignment.forward_fixed_of_boolPattern
#print axioms Alignment.GenesisReconstruction.HistoryDerivedAlignment.historyRelation_patternRigid
#print axioms Alignment.GenesisReconstruction.HistoryDerivedAlignment.constitutiveAlignment_forward_unique
#print axioms Alignment.GenesisReconstruction.HistoryDerivedAlignment.constitutiveAlignment_depth_forward_unique
/- AXIOM_AUDIT_END -/
