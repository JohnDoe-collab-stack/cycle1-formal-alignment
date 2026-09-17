import Alignment.FiniteAnchoredMatchSearch

/-!
# Finite decision certificates for anchored structural alignment

`FiniteAnchoredMatchSearch` constructs structural matches when its Boolean
checks succeed. This module proves the converse direction for complete finite
listings: any existing one-sided anchored matching forces the corresponding
Boolean check to succeed.

Consequently a failed finite check is a constructive certificate that the
corresponding structural matching cannot exist. The two directional checks
therefore separate three levels explicitly:

* forward totality gives a structural injection,
* backward totality gives a structural injection in the reverse direction,
* both together reconstruct exact alignment.

This is a finite decision result. It does not assume a pre-existing identity
index or a hidden alignment resolver.
-/

namespace Alignment
namespace GenesisReconstruction
namespace FiniteAnchoredMatchDecision

open FiniteAnchoredMatchSearch

universe uSource uTarget uAnchor uValue uA uB

/-- A genuine target match present in the candidate list prevents forward search failure. -/
theorem findTarget_ne_none_of_mem_of_matches
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : AnchoredRelationContext Source Target Anchor Value)
    (anchors : List Anchor)
    (source : Source)
    (candidates : List Target)
    (target : Target)
    (member : target ∈ candidates)
    (matching : context.Matches source target) :
    findTarget context anchors source candidates ≠ none := by
  induction candidates with
  | nil =>
      cases member
  | cons candidate rest ih =>
      cases member with
      | head =>
          have check : matchesOn context anchors source candidate = true :=
            matchesOn_true_of_matches context anchors source candidate matching
          change
            (match matchesOn context anchors source candidate with
            | true => some candidate
            | false => findTarget context anchors source rest) ≠ none
          rw [check]
          intro impossible
          cases impossible
      | tail _ tailMember =>
          cases check : matchesOn context anchors source candidate with
          | false =>
              change
                (match matchesOn context anchors source candidate with
                | true => some candidate
                | false => findTarget context anchors source rest) ≠ none
              rw [check]
              exact ih tailMember matching
          | true =>
              change
                (match matchesOn context anchors source candidate with
                | true => some candidate
                | false => findTarget context anchors source rest) ≠ none
              rw [check]
              intro impossible
              cases impossible

/-- A genuine source match present in the candidate list prevents reverse search failure. -/
theorem findSource_ne_none_of_mem_of_matches
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : AnchoredRelationContext Source Target Anchor Value)
    (anchors : List Anchor)
    (target : Target)
    (candidates : List Source)
    (source : Source)
    (member : source ∈ candidates)
    (matching : context.Matches source target) :
    findSource context anchors target candidates ≠ none := by
  induction candidates with
  | nil =>
      cases member
  | cons candidate rest ih =>
      cases member with
      | head =>
          have check : matchesOn context anchors candidate target = true :=
            matchesOn_true_of_matches context anchors candidate target matching
          change
            (match matchesOn context anchors candidate target with
            | true => some candidate
            | false => findSource context anchors target rest) ≠ none
          rw [check]
          intro impossible
          cases impossible
      | tail _ tailMember =>
          cases check : matchesOn context anchors candidate target with
          | false =>
              change
                (match matchesOn context anchors candidate target with
                | true => some candidate
                | false => findSource context anchors target rest) ≠ none
              rw [check]
              exact ih tailMember matching
          | true =>
              change
                (match matchesOn context anchors candidate target with
                | true => some candidate
                | false => findSource context anchors target rest) ≠ none
              rw [check]
              intro impossible
              cases impossible

/-- If every listed input has a search result, the global Boolean check succeeds. -/
theorem allFound_true_of_forall_mem
    {A : Type uA}
    {B : Type uB}
    (find : A → Option B)
    (values : List A) :
    (∀ value : A, value ∈ values → find value ≠ none) →
      allFound find values = true := by
  induction values with
  | nil =>
      intro _
      rfl
  | cons head tail ih =>
      intro everyFound
      have headFound : find head ≠ none :=
        everyFound head (List.Mem.head tail)
      cases headResult : find head with
      | none =>
          exact False.elim (headFound headResult)
      | some result =>
          have tailFound :
              ∀ value : A, value ∈ tail → find value ≠ none := by
            intro value member
            exact everyFound value (List.Mem.tail head member)
          have tailChecked : allFound find tail = true :=
            ih tailFound
          change
            (match find head with
            | none => false
            | some _ => allFound find tail) = true
          rw [headResult]
          exact tailChecked

/-- Any forward structural matching forces the finite forward checker to succeed. -/
theorem forwardTotalCheck_true_of_matching
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : AnchoredRelationContext Source Target Anchor Value)
    (anchors : FiniteListing Anchor)
    (sources : FiniteListing Source)
    (targets : FiniteListing Target)
    (matching : ForwardAnchoredMatching context) :
    forwardTotalCheck context anchors sources targets = true := by
  apply allFound_true_of_forall_mem
  intro source _
  exact
    findTarget_ne_none_of_mem_of_matches
      context anchors.values source targets.values
      (matching.forward source)
      (targets.complete (matching.forward source))
      (matching.forward_matches source)

/-- Any backward structural matching forces the finite reverse checker to succeed. -/
theorem backwardTotalCheck_true_of_matching
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : AnchoredRelationContext Source Target Anchor Value)
    (anchors : FiniteListing Anchor)
    (sources : FiniteListing Source)
    (targets : FiniteListing Target)
    (matching : BackwardAnchoredMatching context) :
    backwardTotalCheck context anchors sources targets = true := by
  apply allFound_true_of_forall_mem
  intro target _
  exact
    findSource_ne_none_of_mem_of_matches
      context anchors.values target sources.values
      (matching.backward target)
      (sources.complete (matching.backward target))
      (matching.backward_matches target)

/-- A failed forward check constructively refutes every forward structural matching. -/
theorem noForwardMatching_of_forwardTotalCheck_false
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : AnchoredRelationContext Source Target Anchor Value)
    (anchors : FiniteListing Anchor)
    (sources : FiniteListing Source)
    (targets : FiniteListing Target)
    (checked : forwardTotalCheck context anchors sources targets = false)
    (matching : ForwardAnchoredMatching context) : False := by
  have succeeds :=
    forwardTotalCheck_true_of_matching
      context anchors sources targets matching
  rw [checked] at succeeds
  cases succeeds

/-- A failed reverse check constructively refutes every backward structural matching. -/
theorem noBackwardMatching_of_backwardTotalCheck_false
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : AnchoredRelationContext Source Target Anchor Value)
    (anchors : FiniteListing Anchor)
    (sources : FiniteListing Source)
    (targets : FiniteListing Target)
    (checked : backwardTotalCheck context anchors sources targets = false)
    (matching : BackwardAnchoredMatching context) : False := by
  have succeeds :=
    backwardTotalCheck_true_of_matching
      context anchors sources targets matching
  rw [checked] at succeeds
  cases succeeds

/-- Forward finite totality is exactly inhabited one-sided structural matching. -/
theorem forwardTotalCheck_true_iff_nonempty
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : AnchoredRelationContext Source Target Anchor Value)
    (anchors : FiniteListing Anchor)
    (sources : FiniteListing Source)
    (targets : FiniteListing Target) :
    forwardTotalCheck context anchors sources targets = true ↔
      Nonempty (ForwardAnchoredMatching context) := by
  constructor
  · intro checked
    exact
      ⟨forwardMatchingOfCheck context anchors sources targets checked⟩
  · intro existing
    cases existing with
    | intro matching =>
        exact
          forwardTotalCheck_true_of_matching
            context anchors sources targets matching

/-- Reverse finite totality is exactly inhabited reverse structural matching. -/
theorem backwardTotalCheck_true_iff_nonempty
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : AnchoredRelationContext Source Target Anchor Value)
    (anchors : FiniteListing Anchor)
    (sources : FiniteListing Source)
    (targets : FiniteListing Target) :
    backwardTotalCheck context anchors sources targets = true ↔
      Nonempty (BackwardAnchoredMatching context) := by
  constructor
  · intro checked
    exact
      ⟨backwardMatchingOfCheck context anchors sources targets checked⟩
  · intro existing
    cases existing with
    | intro matching =>
        exact
          backwardTotalCheck_true_of_matching
            context anchors sources targets matching

/-- The pair of finite directional checks exactly characterizes inhabited total matching. -/
theorem totalChecks_true_iff_nonempty
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : AnchoredRelationContext Source Target Anchor Value)
    (anchors : FiniteListing Anchor)
    (sources : FiniteListing Source)
    (targets : FiniteListing Target) :
    (forwardTotalCheck context anchors sources targets = true ∧
      backwardTotalCheck context anchors sources targets = true) ↔
      Nonempty (TotalAnchoredMatching context) := by
  constructor
  · intro checks
    exact
      ⟨totalMatchingOfChecks
        context anchors sources targets checks.1 checks.2⟩
  · intro existing
    cases existing with
    | intro matching =>
        exact
          ⟨forwardTotalCheck_true_of_matching
              context anchors sources targets matching.toForwardMatching,
            backwardTotalCheck_true_of_matching
              context anchors sources targets matching.toBackwardMatching⟩

/-- A failed forward check also refutes any compatible exact alignment. -/
theorem noCompatibleExactAlignment_of_forwardTotalCheck_false
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : AnchoredRelationContext Source Target Anchor Value)
    (anchors : FiniteListing Anchor)
    (sources : FiniteListing Source)
    (targets : FiniteListing Target)
    (checked : forwardTotalCheck context anchors sources targets = false)
    (alignment : CompatibleExactAlignment context) : False :=
  noForwardMatching_of_forwardTotalCheck_false
    context anchors sources targets checked
    alignment.toTotalMatching.toForwardMatching

/-- A failed reverse check also refutes any compatible exact alignment. -/
theorem noCompatibleExactAlignment_of_backwardTotalCheck_false
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : AnchoredRelationContext Source Target Anchor Value)
    (anchors : FiniteListing Anchor)
    (sources : FiniteListing Source)
    (targets : FiniteListing Target)
    (checked : backwardTotalCheck context anchors sources targets = false)
    (alignment : CompatibleExactAlignment context) : False :=
  noBackwardMatching_of_backwardTotalCheck_false
    context anchors sources targets checked
    alignment.toTotalMatching.toBackwardMatching

/--
A successful forward check together with a failed reverse check yields a
positive injection and a constructive certificate that exact compatible
alignment is impossible.
-/
def forwardOnlyCertificateOfChecks
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : AnchoredRelationContext Source Target Anchor Value)
    (anchors : FiniteListing Anchor)
    (sources : FiniteListing Source)
    (targets : FiniteListing Target)
    (forwardChecked : forwardTotalCheck context anchors sources targets = true)
    (backwardChecked : backwardTotalCheck context anchors sources targets = false) :
    ForwardAnchoredMatching context ×
      (CompatibleExactAlignment context → False) :=
  ⟨forwardMatchingOfCheck
      context anchors sources targets forwardChecked,
    noCompatibleExactAlignment_of_backwardTotalCheck_false
      context anchors sources targets backwardChecked⟩

end FiniteAnchoredMatchDecision
end GenesisReconstruction
end Alignment

/- AXIOM_AUDIT_BEGIN -/
#print axioms Alignment.GenesisReconstruction.FiniteAnchoredMatchDecision.findTarget_ne_none_of_mem_of_matches
#print axioms Alignment.GenesisReconstruction.FiniteAnchoredMatchDecision.findSource_ne_none_of_mem_of_matches
#print axioms Alignment.GenesisReconstruction.FiniteAnchoredMatchDecision.allFound_true_of_forall_mem
#print axioms Alignment.GenesisReconstruction.FiniteAnchoredMatchDecision.forwardTotalCheck_true_of_matching
#print axioms Alignment.GenesisReconstruction.FiniteAnchoredMatchDecision.backwardTotalCheck_true_of_matching
#print axioms Alignment.GenesisReconstruction.FiniteAnchoredMatchDecision.noForwardMatching_of_forwardTotalCheck_false
#print axioms Alignment.GenesisReconstruction.FiniteAnchoredMatchDecision.noBackwardMatching_of_backwardTotalCheck_false
#print axioms Alignment.GenesisReconstruction.FiniteAnchoredMatchDecision.forwardTotalCheck_true_iff_nonempty
#print axioms Alignment.GenesisReconstruction.FiniteAnchoredMatchDecision.backwardTotalCheck_true_iff_nonempty
#print axioms Alignment.GenesisReconstruction.FiniteAnchoredMatchDecision.totalChecks_true_iff_nonempty
#print axioms Alignment.GenesisReconstruction.FiniteAnchoredMatchDecision.noCompatibleExactAlignment_of_forwardTotalCheck_false
#print axioms Alignment.GenesisReconstruction.FiniteAnchoredMatchDecision.noCompatibleExactAlignment_of_backwardTotalCheck_false
#print axioms Alignment.GenesisReconstruction.FiniteAnchoredMatchDecision.forwardOnlyCertificateOfChecks
/- AXIOM_AUDIT_END -/
