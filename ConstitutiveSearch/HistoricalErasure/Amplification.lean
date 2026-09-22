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

private theorem congrArgPair {α β γ : Type} (f : α → β → γ)
    {a a' : α} {b b' : β} (ha : a = a') (hb : b = b') : f a b = f a' b' := by
  cases ha
  cases hb
  rfl

private theorem length_append_exact {α : Type} (xs ys : List α) :
    (xs ++ ys).length = xs.length + ys.length := by
  induction xs with
  | nil => exact (Nat.zero_add _).symm
  | cons x xs ih =>
    exact (congrArg Nat.succ ih).trans (Nat.succ_add _ _).symm

private theorem length_map_exact {α β : Type} (f : α → β) (xs : List α) :
    (xs.map f).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact congrArg Nat.succ ih

private theorem mem_append_left_exact {α : Type} {x : α} {xs ys : List α}
    (member : x ∈ xs) : x ∈ xs ++ ys := by
  induction member with
  | head => exact List.Mem.head _
  | tail a _ ih => exact List.Mem.tail a ih

private theorem mem_append_right_exact {α : Type} {x : α} (xs : List α) {ys : List α}
    (member : x ∈ ys) : x ∈ xs ++ ys := by
  induction xs with
  | nil => exact member
  | cons a xs ih => exact List.Mem.tail a ih

private theorem mem_append_cases_exact {α : Type} {x : α} {xs ys : List α}
    (member : x ∈ xs ++ ys) : x ∈ xs ∨ x ∈ ys := by
  induction xs with
  | nil => exact Or.inr member
  | cons a xs ih =>
    cases member with
    | head => exact Or.inl (List.Mem.head _)
    | tail _ rest =>
      cases ih rest with
      | inl left => exact Or.inl (List.Mem.tail a left)
      | inr right => exact Or.inr right

private theorem map_member_exact {α β : Type} (f : α → β) {x : α} {xs : List α}
    (member : x ∈ xs) : f x ∈ xs.map f := by
  induction member with
  | head => exact List.Mem.head _
  | tail a _ ih => exact List.Mem.tail (f a) ih

private theorem map_member_cases_exact {α β : Type} (f : α → β) {y : β} {xs : List α}
    (member : y ∈ xs.map f) : ∃ x, x ∈ xs ∧ f x = y := by
  induction xs with
  | nil => cases member
  | cons a xs ih =>
    cases member with
    | head => exact ⟨a, List.Mem.head _, rfl⟩
    | tail _ rest =>
      rcases ih rest with ⟨x, hx, equal⟩
      exact ⟨x, List.Mem.tail a hx, equal⟩

private theorem map_nodup_exact {α β : Type} (f : α → β)
    (injective : Function.Injective f) {xs : List α} (distinct : xs.Nodup) :
    (xs.map f).Nodup := by
  induction distinct with
  | nil => exact List.Pairwise.nil
  | @cons a xs apart _ ih =>
    refine List.Pairwise.cons ?_ ih
    intro b member same
    rcases map_member_cases_exact f member with ⟨x, hx, equal⟩
    exact apart x hx (injective (same.trans equal.symm))

private theorem pairwise_append_exact {α : Type} {R : α → α → Prop} {xs ys : List α}
    (left : List.Pairwise R xs) (right : List.Pairwise R ys) :
    (∀ a, a ∈ xs → ∀ b, b ∈ ys → R a b) → List.Pairwise R (xs ++ ys) := by
  induction left with
  | nil => exact fun _ => right
  | @cons a xs apart _ ih =>
    intro cross
    refine List.Pairwise.cons ?_ (ih ?_)
    · intro b member
      cases mem_append_cases_exact member with
      | inl leftMember => exact apart b leftMember
      | inr rightMember => exact cross a (List.Mem.head _) b rightMember
    · intro b hb c hc
      exact cross b (List.Mem.tail a hb) c hc

theorem branches_length (n : Nat) : (branches n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc
      (branches (n + 1)).length =
          ((branches n).map (List.cons false)).length +
          ((branches n).map (List.cons true)).length := length_append_exact _ _
      _ = (branches n).length + (branches n).length := by
        rw [length_map_exact, length_map_exact]
      _ = 2 ^ n + 2 ^ n := congrArg (fun x : Nat => x + x) ih
      _ = 2 ^ n * 2 := (Nat.mul_two _).symm
      _ = 2 ^ (n + 1) := (Nat.pow_succ 2 n).symm

/-- Distinct histories remain distinct; there is no quotient of branch states. -/
theorem branches_nodup (n : Nat) : (branches n).Nodup := by
  induction n with
  | zero => exact List.Pairwise.cons (fun _ impossible => by cases impossible) List.Pairwise.nil
  | succ n ih =>
    refine pairwise_append_exact
      (map_nodup_exact (List.cons false) ?_ ih)
      (map_nodup_exact (List.cons true) ?_ ih) ?_
    · intro a b same
      exact (List.cons.inj same).2
    · intro a b same
      exact (List.cons.inj same).2
    · intro a ha b hb same
      rcases map_member_cases_exact (List.cons false) ha with ⟨xs, _, hx⟩
      rcases map_member_cases_exact (List.cons true) hb with ⟨ys, _, hy⟩
      have impossible : false = true :=
        (List.cons.inj (hx.trans (same.trans hy.symm))).1
      cases impossible

/-- Exact characterization of the reference enumeration. -/
theorem mem_branches (bits : List Bool) : ∀ n, bits ∈ branches n ↔ bits.length = n := by
  intro n
  induction n generalizing bits with
  | zero =>
    constructor
    · intro member
      cases member with
      | head => rfl
      | tail _ impossible => cases impossible
    · intro lengthZero
      cases bits with
      | nil => exact List.Mem.head _
      | cons b rest => exact False.elim (Nat.noConfusion lengthZero)
  | succ n ih =>
    constructor
    · intro member
      cases mem_append_cases_exact member with
      | inl left =>
        rcases map_member_cases_exact (List.cons false) left with ⟨xs, hx, equal⟩
        exact (congrArg List.length equal).symm.trans (congrArg Nat.succ ((ih xs).mp hx))
      | inr right =>
        rcases map_member_cases_exact (List.cons true) right with ⟨xs, hx, equal⟩
        exact (congrArg List.length equal).symm.trans (congrArg Nat.succ ((ih xs).mp hx))
    · intro lengthExact
      cases bits with
      | nil => exact False.elim (Nat.noConfusion lengthExact)
      | cons b rest =>
        have tail : rest ∈ branches n := (ih rest).mpr (Nat.succ.inj lengthExact)
        cases b with
        | false => exact mem_append_left_exact (map_member_exact (List.cons false) tail)
        | true => exact mem_append_right_exact _ (map_member_exact (List.cons true) tail)

theorem retained_mem_branches (n : Nat) : retainedHistory n ∈ branches n := by
  apply (mem_branches (retainedHistory n) n).mpr
  change (List.replicate n true).length = n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ]
    exact congrArg Nat.succ ih

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

private theorem le_add_right_exact (a b : Nat) : a ≤ a + b := by
  induction b with
  | zero => exact Nat.le_refl a
  | succ b ih => exact Nat.le.step ih

private theorem add_mul_exact (a b c : Nat) : (a + b) * c = a * c + b * c := by
  calc
    (a + b) * c = c * (a + b) := Nat.mul_comm _ _
    _ = c * a + c * b := Nat.mul_add _ _ _
    _ = a * c + b * c := congrArgPair Nat.add (Nat.mul_comm _ _) (Nat.mul_comm _ _)

private theorem mul_assoc_exact (a b c : Nat) : (a * b) * c = a * (b * c) := by
  induction c with
  | zero => rfl
  | succ c ih =>
    change (a * b) * c + a * b = a * (b * c + b)
    rw [ih, Nat.mul_add]

private theorem square_successor (m : Nat) :
    (m + 1) * (m + 1) = m * m + m + m + 1 := by
  calc
    (m + 1) * (m + 1) = m * (m + 1) + 1 * (m + 1) :=
      add_mul_exact m 1 (m + 1)
    _ = (m * m + m * 1) + (m + 1) := by rw [Nat.mul_add, Nat.one_mul]
    _ = m * m + m + m + 1 := by
      rw [Nat.mul_one]
      exact (Nat.add_assoc _ _ _).symm

private theorem square_le_pow_offset (k : Nat) : (k + 4) * (k + 4) ≤ 2 ^ (k + 4) := by
  induction k with
  | zero => decide
  | succ k ih =>
    let m := k + 4
    have four : 4 ≤ m := by
      change 4 ≤ k + 4
      rw [Nat.add_comm]
      exact le_add_right_exact 4 k
    have one : 1 ≤ m := Nat.le_trans (by decide : 1 ≤ 4) four
    have three : 3 ≤ m := Nat.le_trans (by decide : 3 ≤ 4) four
    have tailBound : m + m + 1 ≤ m * m := by
      calc
        m + m + 1 ≤ m + m + m := Nat.add_le_add_left one (m + m)
        _ = 3 * m := by
          change m + m + m = (1 + 1 + 1) * m
          rw [add_mul_exact, add_mul_exact, Nat.one_mul]
        _ ≤ m * m := Nat.mul_le_mul_right m three
    have nextSquare : (m + 1) * (m + 1) ≤ 2 * (m * m) := by
      calc
        (m + 1) * (m + 1) = m * m + (m + m + 1) := by
          rw [square_successor, Nat.add_assoc (m * m) m m,
            Nat.add_assoc (m * m) (m + m) 1]
        _ ≤ m * m + m * m := Nat.add_le_add_left tailBound (m * m)
        _ = 2 * (m * m) := (Nat.two_mul _).symm
    have index : k + 1 + 4 = m + 1 :=
      ((Nat.add_assoc k 1 4).trans
        (congrArg (Nat.add k) (Nat.add_comm 1 4))).trans (Nat.add_assoc k 4 1).symm
    rw [index]
    calc
      (m + 1) * (m + 1) ≤ 2 * (m * m) := nextSquare
      _ ≤ 2 * (2 ^ m) := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (m + 1) := (Nat.mul_comm 2 (2 ^ m)).trans (Nat.pow_succ 2 m).symm

private theorem offset_of_le {a b : Nat} (h : a ≤ b) : ∃ k, b = k + a := by
  induction h with
  | refl => exact ⟨0, (Nat.zero_add a).symm⟩
  | @step b h ih =>
    rcases ih with ⟨k, hk⟩
    exact ⟨k + 1, (congrArg Nat.succ hk).trans (Nat.succ_add k a).symm⟩

theorem square_le_pow (n : Nat) (large : 4 ≤ n) : n * n ≤ 2 ^ n := by
  rcases offset_of_le large with ⟨k, hk⟩
  rw [hk]
  exact square_le_pow_offset k

private theorem lt_sub_one_of_add_two_le {a b : Nat} (h : a + 2 ≤ b) :
    a < b - 1 := by
  cases b with
  | zero => exact False.elim (Nat.not_succ_le_zero (a + 1) h)
  | succ b => exact Nat.le_of_succ_le_succ h

/-- An explicit eventual separation, not merely a sequence of experiments. -/
theorem exponential_dominates_ledger (K n : Nat) (large : 60 * K + 5 ≤ n) :
    K * (60 * n) < 2 ^ n - 1 := by
  have five : 5 ≤ 60 * K + 5 := by
    rw [Nat.add_comm]
    exact le_add_right_exact 5 (60 * K)
  have fiveN : 5 ≤ n := Nat.le_trans five large
  have square := square_le_pow n (Nat.le_trans (by decide : 4 ≤ 5) fiveN)
  have coefficient : 60 * K + 1 ≤ n :=
    Nat.le_trans (Nat.add_le_add_left (by decide : 1 ≤ 5) (60 * K)) large
  have lower : (60 * K + 1) * n ≤ n * n := Nat.mul_le_mul_right n coefficient
  rw [add_mul_exact, Nat.one_mul] at lower
  have rearrange : (60 * K) * n = K * (60 * n) :=
    (congrArg (fun t => t * n) (Nat.mul_comm 60 K)).trans (mul_assoc_exact K 60 n)
  rw [rearrange] at lower
  have two : 2 ≤ n := Nat.le_trans (by decide : 2 ≤ 5) fiveN
  have gap : K * (60 * n) + 2 ≤ 2 ^ n :=
    Nat.le_trans (Nat.add_le_add_left two _) (Nat.le_trans lower square)
  exact lt_sub_one_of_add_two_le gap

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
#print axioms ConstitutiveSearch.HistoricalErasure.congrArgPair
#print axioms ConstitutiveSearch.HistoricalErasure.add_mul_exact
#print axioms ConstitutiveSearch.HistoricalErasure.mul_assoc_exact
#print axioms ConstitutiveSearch.HistoricalErasure.square_successor
#print axioms ConstitutiveSearch.HistoricalErasure.square_le_pow_offset
#print axioms ConstitutiveSearch.HistoricalErasure.offset_of_le
#print axioms ConstitutiveSearch.HistoricalErasure.lt_sub_one_of_add_two_le
#print axioms ConstitutiveSearch.HistoricalErasure.square_le_pow
#print axioms ConstitutiveSearch.HistoricalErasure.exponential_dominates_ledger
#print axioms ConstitutiveSearch.HistoricalErasure.amplification_unbounded
#print axioms ConstitutiveSearch.HistoricalErasure.amplificationCertificate
/- AXIOM_AUDIT_END -/
