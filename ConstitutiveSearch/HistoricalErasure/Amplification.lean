import ConstitutiveSearch.HistoricalErasure.Chain
import Init.Data.List.Pairwise

/-!
# Exponential reference width and executed historical amplification

The reference frontier is the full enumeration of Boolean decision histories.
It is not materialized by `execute`. No lower bound on other algorithms is
claimed. Every reference history is viable whenever the unchanged core has
one accepted valuation. The actual retained frontier is a singleton, and the
source-level row/event ledger is exactly linear in the number of blocks.

The asymptotic assertion is expressed without real numbers: for every natural
multiplier K, beyond an explicit threshold, avoided reference width exceeds
K times the executed ledger. Acceptance of the core is not decided here.
-/

namespace ConstitutiveSearch.HistoricalErasure

/-- Reference enumeration only: never called by the normalizing executor. -/
def branches : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (branches n).map (List.cons false) ++ (branches n).map (List.cons true)

theorem branches_length (n : Nat) : (branches n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [branches, List.length_append, List.length_map, ih, Nat.pow_succ]
    omega

/-- Distinct histories remain distinct; there is no quotient of branch states. -/
theorem branches_nodup (n : Nat) : (branches n).Nodup := by
  induction n with
  | zero => decide
  | succ n ih =>
    change List.Pairwise (fun a b : List Bool => a ≠ b)
      ((branches n).map (List.cons false) ++ (branches n).map (List.cons true))
    apply List.pairwise_append.mpr
    refine ⟨?_, ?_, ?_⟩
    · exact List.Pairwise.map (R := fun a b : List Bool => a ≠ b)
        (List.cons false)
        (fun (a b : List Bool) (different : a ≠ b) (same : false :: a = false :: b) =>
          different (List.cons.inj same).2) ih
    · exact List.Pairwise.map (R := fun a b : List Bool => a ≠ b)
        (List.cons true)
        (fun (a b : List Bool) (different : a ≠ b) (same : true :: a = true :: b) =>
          different (List.cons.inj same).2) ih
    · intro a ha b hb same
      rcases List.mem_map.mp ha with ⟨xs, _, hx⟩
      rcases List.mem_map.mp hb with ⟨ys, _, hy⟩
      have impossible : false = true :=
        (List.cons.inj (hx.trans (same.trans hy.symm))).1
      cases impossible

/-- Exact characterization of the reference enumeration. -/
theorem mem_branches (bits : List Bool) : ∀ n, bits ∈ branches n ↔ bits.length = n := by
  induction bits with
  | nil =>
    intro n
    cases n with
    | zero => simp [branches]
    | succ n => simp [branches]
  | cons bit rest ih =>
    intro n
    cases n with
    | zero => simp [branches]
    | succ n =>
      cases bit <;> simp [branches, ih]

theorem retained_mem_branches (n : Nat) : retainedHistory n ∈ branches n := by
  apply (mem_branches (retainedHistory n) n).mpr
  exact List.length_replicate n true

/-- Viability of the fully expanded reference, without building it at runtime. -/
def ReferenceViable (n : Nat) (G : List Bool → Prop) : Prop :=
  ∃ history, history ∈ branches n ∧ (chainSystem n G).Viable history

theorem reference_viable_iff_retained (n : Nat) (G : List Bool → Prop) :
    ReferenceViable n G ↔ (chainSystem n G).Viable (retainedHistory n) := by
  constructor
  · intro viable
    rcases viable with ⟨history, _member, accepted⟩
    exact (normalizingTransport n G history).preservesViable accepted
  · intro viable
    exact ⟨retainedHistory n, retained_mem_branches n, viable⟩

theorem all_reference_branches_viable (n : Nat) (G : List Bool → Prop)
    (cores : List Bool) (lengthExact : cores.length = n) (accepted : G cores) :
    ∀ history, history ∈ branches n → (chainSystem n G).Viable history := by
  intro history member
  exact every_branch_viable n G cores history lengthExact
    ((mem_branches history n).mp member) accepted

/-- Exact width/cost certificate for the run on any structural continuation. -/
theorem executed_width_cost (cells : List Cell) :
    (branches cells.length).length = 2 ^ cells.length ∧
    [retainedHistory cells.length].length = 1 ∧
    (execute cells).work = 60 * cells.length ∧
    (execute cells).attempts = 6 * cells.length ∧
    (execute cells).program.length = cells.length :=
  ⟨branches_length _, rfl, (execute cells).work_exact,
    (execute cells).attempts_exact, (execute cells).program_length⟩

private theorem square_successor (m : Nat) :
    (m + 1) * (m + 1) = m * m + m + m + 1 := by
  calc
    (m + 1) * (m + 1) = m * (m + 1) + 1 * (m + 1) :=
      Nat.add_mul m 1 (m + 1)
    _ = (m * m + m * 1) + (m + 1) := by rw [Nat.mul_add, Nat.one_mul]
    _ = m * m + m + m + 1 := by rw [Nat.mul_one]; omega

private theorem square_le_pow_offset (k : Nat) : (k + 4) * (k + 4) ≤ 2 ^ (k + 4) := by
  induction k with
  | zero => decide
  | succ k ih =>
    have three : 3 * (k + 4) ≤ (k + 4) * (k + 4) :=
      Nat.mul_le_mul_right (k + 4) (by omega : 3 ≤ k + 4)
    have expanded := square_successor (k + 4)
    have nextSquare : (k + 5) * (k + 5) ≤ 2 * ((k + 4) * (k + 4)) := by
      omega
    calc
      (k + 1 + 4) * (k + 1 + 4) ≤ 2 * ((k + 4) * (k + 4)) := nextSquare
      _ ≤ 2 * (2 ^ (k + 4)) := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (k + 1 + 4) := by
        rw [show k + 1 + 4 = (k + 4) + 1 by omega, Nat.pow_succ]
        exact Nat.mul_comm _ _

theorem square_le_pow (n : Nat) (large : 4 ≤ n) : n * n ≤ 2 ^ n := by
  have exactIndex : n - 4 + 4 = n := by omega
  have result := square_le_pow_offset (n - 4)
  rw [exactIndex] at result
  exact result

/-- An explicit eventual separation, not merely a sequence of experiments. -/
theorem exponential_dominates_ledger (K n : Nat) (large : 60 * K + 5 ≤ n) :
    K * (60 * n) < 2 ^ n - 1 := by
  have square := square_le_pow n (by omega)
  have lower : (60 * K + 1) * n ≤ n * n :=
    Nat.mul_le_mul_right n (by omega : 60 * K + 1 ≤ n)
  rw [Nat.add_mul, Nat.one_mul] at lower
  have rearrange : (60 * K) * n = K * (60 * n) :=
    (congrArg (fun t => t * n) (Nat.mul_comm 60 K)).trans (Nat.mul_assoc K 60 n)
  rw [rearrange] at lower
  omega

/-- Avoided reference width eventually exceeds every multiple of actual ledger. -/
theorem amplification_unbounded :
    ∀ K : Nat, ∃ threshold : Nat, ∀ cells : List Cell,
      threshold ≤ cells.length →
      K * (execute cells).work < (branches cells.length).length - 1 := by
  intro K
  refine ⟨60 * K + 5, ?_⟩
  intro cells large
  rw [(execute cells).work_exact, branches_length]
  exact exponential_dominates_ledger K cells.length large

/-- The positive theorem package preserves the untouched acceptance core. -/
structure AmplificationCertificate (cells : List Cell) (G : List Bool → Prop) : Prop where
  distinctReference : (branches cells.length).Nodup
  referenceWidth : (branches cells.length).length = 2 ^ cells.length
  retainedWidth : [retainedHistory cells.length].length = 1
  viability : ReferenceViable cells.length G ↔
    (chainSystem cells.length G).Viable (retainedHistory cells.length)
  acceptedOutput : Accepted G true cells → Accepted G true (execute cells).output
  corePreserved : coreValues (execute cells).output = coreValues cells
  ledger : (execute cells).work = 60 * cells.length
  unbounded : ∀ K, 60 * K + 5 ≤ cells.length →
    K * (execute cells).work < (branches cells.length).length - 1

theorem amplificationCertificate (cells : List Cell) (G : List Bool → Prop) :
    AmplificationCertificate cells G :=
  { distinctReference := branches_nodup _
    referenceWidth := branches_length _
    retainedWidth := rfl
    viability := reference_viable_iff_retained _ _
    acceptedOutput := (execute cells).preserves_acceptance G
    corePreserved := (execute cells).output_cores
    ledger := (execute cells).work_exact
    unbounded := by
      intro K large
      rw [(execute cells).work_exact, branches_length]
      exact exponential_dominates_ledger K cells.length large }

end ConstitutiveSearch.HistoricalErasure

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.HistoricalErasure.branches_length
#print axioms ConstitutiveSearch.HistoricalErasure.branches_nodup
#print axioms ConstitutiveSearch.HistoricalErasure.mem_branches
#print axioms ConstitutiveSearch.HistoricalErasure.retained_mem_branches
#print axioms ConstitutiveSearch.HistoricalErasure.reference_viable_iff_retained
#print axioms ConstitutiveSearch.HistoricalErasure.all_reference_branches_viable
#print axioms ConstitutiveSearch.HistoricalErasure.executed_width_cost
#print axioms ConstitutiveSearch.HistoricalErasure.square_le_pow
#print axioms ConstitutiveSearch.HistoricalErasure.exponential_dominates_ledger
#print axioms ConstitutiveSearch.HistoricalErasure.amplification_unbounded
#print axioms ConstitutiveSearch.HistoricalErasure.amplificationCertificate
/- AXIOM_AUDIT_END -/
