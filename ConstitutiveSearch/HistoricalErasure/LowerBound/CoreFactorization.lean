import ConstitutiveSearch.HistoricalErasure.Chain

/-!
# Testing necessity of dynamic discovery on the audited family

This file leaves the audited semantics unchanged. A direct cellwise function
has the same outputs as the audited executor, without searching tables or
threading an output guard. The equality is proved separately, not used to
implement the direct function. A second result factors full-branch viability
through the unchanged core; this blocks an independent-branch adversary.
-/

namespace ConstitutiveSearch.HistoricalErasure.LowerBound

/-- The core decision problem, with exactly the original length constraint. -/
def CoreViable (n : Nat) (G : List Bool → Prop) : Prop :=
  ∃ cores, cores.length = n ∧ G cores

theorem coreValues_length (cells : List Cell) :
    (coreValues cells).length = cells.length := by
  induction cells with
  | nil => rfl
  | cons c rest ih => exact congrArg Nat.succ ih

/-- No execution or discovered transport is used in either direction. -/
theorem branch_viable_iff_core (n : Nat) (G : List Bool → Prop)
    (history : List Bool) (lengthExact : history.length = n) :
    (chainSystem n G).Viable history ↔ CoreViable n G := by
  constructor
  · intro viable
    rcases viable with ⟨c, accepted⟩
    exact ⟨coreValues c.val, (coreValues_length c.val).trans c.property.1, accepted.1⟩
  · intro viable
    rcases viable with ⟨cores, same, accepted⟩
    exact every_branch_viable n G cores history same lengthExact accepted

theorem all_full_histories_same_viability (n : Nat) (G : List Bool → Prop)
    (h k : List Bool) (lh : h.length = n) (lk : k.length = n) :
    (chainSystem n G).Viable h ↔ (chainSystem n G).Viable k :=
  (branch_viable_iff_core n G h lh).trans (branch_viable_iff_core n G k lk).symm

/-- The proposed adversary cannot make one full branch viable and another not. -/
theorem no_mixed_viability (n : Nat) (G : List Bool → Prop)
    (h k : List Bool) (lh : h.length = n) (lk : k.length = n) :
    ¬ ((chainSystem n G).Viable h ∧ ¬ (chainSystem n G).Viable k) := by
  intro mixed
  exact mixed.2 ((all_full_histories_same_viability n G h k lh lk).mp mixed.1)

/-- Agreement on one branch forces agreement on every branch, even across cores. -/
theorem one_branch_determines_all (n : Nat) (G H : List Bool → Prop)
    (h k : List Bool) (lh : h.length = n) (lk : k.length = n)
    (same : (chainSystem n G).Viable h ↔ (chainSystem n H).Viable h) :
    (chainSystem n G).Viable k ↔ (chainSystem n H).Viable k :=
  ((all_full_histories_same_viability n G k h lk lh).trans same).trans
    (all_full_histories_same_viability n H h k lh lk)

/-- Literal cellwise update: no table language, discovery, or incoming guard. -/
def directCell (c : Cell) : Cell :=
  match c.decision with
  | false => ⟨true, c.core, c.core⟩
  | true => c

structure DirectRun where
  output : List Cell
  cellVisits : Nat
  deriving Repr

/-- One structural recursion; the tail depends on the input tail alone. -/
@[noinline] def directNormalize : List Cell → DirectRun
  | [] => ⟨[], 0⟩
  | c :: rest =>
      let tail := directNormalize rest
      ⟨directCell c :: tail.output, tail.cellVisits + 1⟩

theorem direct_visits (cells : List Cell) :
    (directNormalize cells).cellVisits = cells.length := by
  induction cells with
  | nil => rfl
  | cons c rest ih => exact congrArg Nat.succ ih

theorem direct_length (cells : List Cell) :
    (directNormalize cells).output.length = cells.length := by
  induction cells with
  | nil => rfl
  | cons c rest ih => exact congrArg Nat.succ ih

theorem direct_core (c : Cell) : (directCell c).core = c.core := by
  cases c with
  | mk d p z => cases d <;> rfl

theorem direct_decision (c : Cell) : (directCell c).decision = true := by
  cases c with
  | mk d p z => cases d <;> rfl

theorem direct_outgoing (c : Cell) : (directCell c).outgoing = true := by
  unfold Cell.outgoing outgoingGuard
  rw [direct_decision]
  rfl

theorem direct_cores (cells : List Cell) :
    coreValues (directNormalize cells).output = coreValues cells := by
  induction cells with
  | nil => rfl
  | cons c rest ih =>
    change (directCell c).core :: coreValues (directNormalize rest).output =
      c.core :: coreValues rest
    rw [direct_core, ih]

theorem direct_decisions (cells : List Cell) :
    decisionValues (directNormalize cells).output = retainedHistory cells.length := by
  induction cells with
  | nil => rfl
  | cons c rest ih =>
    change (directCell c).decision :: decisionValues (directNormalize rest).output =
      List.replicate (rest.length + 1) true
    rw [direct_decision, ih, List.replicate_succ]
    rfl

theorem direct_cell_ok (c : Cell) (accepted : CellOK true c) :
    CellOK true (directCell c) := by
  cases c with
  | mk d p z =>
    cases d with
    | false => exact fun _ => ⟨rfl, rfl⟩
    | true => exact accepted

theorem direct_chain_ok (cells : List Cell) (accepted : ChainOK true cells) :
    ChainOK true (directNormalize cells).output := by
  induction cells with
  | nil => exact True.intro
  | cons c rest ih =>
    change CellOK true (directCell c) ∧ ChainOK (directCell c).outgoing _
    rw [direct_outgoing]
    exact ⟨direct_cell_ok c accepted.1,
      ih (chainOK_guard_true c.outgoing rest accepted.2)⟩

theorem direct_preserves_acceptance (cells : List Cell) (G : List Bool → Prop)
    (accepted : Accepted G true cells) :
    Accepted G true (directNormalize cells).output := by
  exact ⟨(direct_cores cells).symm ▸ accepted.1, direct_chain_ok cells accepted.2⟩

/-- A total structural map, with its semantic obligation proved separately. -/
def directTransport (n : Nat) (G : List Bool → Prop) (history : List Bool) :
    AcceptingContinuationTransport (chainSystem n G) history (retainedHistory n) where
  map := fun c =>
    ⟨(directNormalize c.val).output,
      (direct_length c.val).trans c.property.1,
      ⟨[], ((direct_decisions c.val).trans
        (congrArg retainedHistory c.property.1)).trans
          (append_nil_exact (retainedHistory n)).symm⟩⟩
  preservesAccept := fun c accepted => direct_preserves_acceptance c.val G accepted

theorem apply_reset_is_direct (c : Cell) : applyCell resetTable c = directCell c := by
  cases c with
  | mk d p z => cases d <;> cases p <;> cases z <;> rfl

/-- Equality of outputs does not assert equality of constitutive execution paths. -/
theorem executed_output_eq_direct {guard : Bool} {cells : List Cell}
    (run : Execution guard cells) : run.output = (directNormalize cells).output := by
  induction run with
  | nil => rfl
  | @step g input rest stage tail ih =>
    change stage.produced :: tail.output = directCell input :: (directNormalize rest).output
    have table := (checkTable_unique g stage.certificate.val stage.certificate.property).2
    rw [stage.producedExact, table, apply_reset_is_direct, ih]

end ConstitutiveSearch.HistoricalErasure.LowerBound

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.HistoricalErasure.LowerBound.branch_viable_iff_core
#print axioms ConstitutiveSearch.HistoricalErasure.LowerBound.all_full_histories_same_viability
#print axioms ConstitutiveSearch.HistoricalErasure.LowerBound.no_mixed_viability
#print axioms ConstitutiveSearch.HistoricalErasure.LowerBound.one_branch_determines_all
#print axioms ConstitutiveSearch.HistoricalErasure.LowerBound.directNormalize
#print axioms ConstitutiveSearch.HistoricalErasure.LowerBound.direct_visits
#print axioms ConstitutiveSearch.HistoricalErasure.LowerBound.direct_length
#print axioms ConstitutiveSearch.HistoricalErasure.LowerBound.direct_cores
#print axioms ConstitutiveSearch.HistoricalErasure.LowerBound.direct_decisions
#print axioms ConstitutiveSearch.HistoricalErasure.LowerBound.direct_preserves_acceptance
#print axioms ConstitutiveSearch.HistoricalErasure.LowerBound.directTransport
#print axioms ConstitutiveSearch.HistoricalErasure.LowerBound.executed_output_eq_direct
/- AXIOM_AUDIT_END -/
