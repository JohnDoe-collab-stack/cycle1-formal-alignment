import ConstitutiveSearch.HistoricalErasure.Amplification
import ConstitutiveSearch.HistoricalErasure.LowerBound.CoreFactorization

/-!
# Exact branch-query lower bound and its applicability boundary

A deterministic finite decision tree may adapt each query to all earlier
answers. For independently variable branch answers, deciding their disjunction
requires every branch on the all-false input. This theorem concerns exact
Boolean queries, not machine running time. The audited chain's viability
answers satisfy a different promise: all full histories have the same answer.
The final section proves that one query suffices under that actual promise.
-/

namespace ConstitutiveSearch.HistoricalErasure.LowerBound

inductive QueryTree (Q : Type) where
  | done (answer : Bool)
  | ask (query : Q) (whenFalse whenTrue : QueryTree Q)

namespace QueryTree

@[noinline] def eval {Q : Type} (oracle : Q → Bool) : QueryTree Q → Bool
  | .done b => b
  | .ask q lo hi => if oracle q then eval oracle hi else eval oracle lo

@[noinline] def trace {Q : Type} (oracle : Q → Bool) : QueryTree Q → List Q
  | .done _ => []
  | .ask q lo hi => q :: (if oracle q then trace oracle hi else trace oracle lo)

def zero {Q : Type} : Q → Bool := fun _ => false

def singleton {Q : Type} [DecidableEq Q] (point : Q) : Q → Bool :=
  fun q => if q = point then true else false

/-- Correct on all independent answer tables over the supplied domain. -/
def Correct {Q : Type} (tree : QueryTree Q) (domain : List Q) : Prop :=
  ∀ oracle : Q → Bool,
    tree.eval oracle = true ↔ ∃ q, q ∈ domain ∧ oracle q = true

/-- A branch absent from the all-false trace cannot affect that run's answer. -/
theorem missed_singleton {Q : Type} [DecidableEq Q] (tree : QueryTree Q) (point : Q)
    (missed : point ∉ tree.trace zero) :
    tree.eval (singleton point) = tree.eval zero := by
  induction tree with
  | done b => rfl
  | ask q lo hi ihlo _ =>
    have different : q ≠ point := by
      intro same
      apply missed
      change point ∈ q :: lo.trace zero
      rw [same]
      exact List.Mem.head _
    have tailMiss : point ∉ lo.trace zero := by
      intro member
      exact missed (List.Mem.tail q member)
    change (if singleton point q then hi.eval (singleton point) else lo.eval (singleton point)) =
      lo.eval zero
    rw [singleton, if_neg different]
    exact ihlo tailMiss

private def memberDecide {Q : Type} [DecidableEq Q] (q : Q) :
    (xs : List Q) → Decidable (q ∈ xs)
  | [] => .isFalse (fun h => by cases h)
  | x :: xs =>
    match decEq q x with
    | .isTrue same => .isTrue (same.symm ▸ List.Mem.head xs)
    | .isFalse apart =>
      match memberDecide q xs with
      | .isTrue member => .isTrue (List.Mem.tail x member)
      | .isFalse absent => .isFalse (fun h => by
          cases h with
          | head => exact apart rfl
          | tail _ member => exact absent member)

/-- Indistinguishability forces inspection of every coordinate on a negative input. -/
theorem correct_covers_zero {Q : Type} [DecidableEq Q]
    (tree : QueryTree Q) (domain : List Q) (correct : tree.Correct domain) :
    ∀ q, q ∈ domain → q ∈ tree.trace zero := by
  intro q member
  cases memberDecide q (tree.trace zero) with
  | isTrue seen => exact seen
  | isFalse seen =>
    have same := missed_singleton tree q seen
    have positive : tree.eval (singleton q) = true :=
      (correct (singleton q)).mpr ⟨q, member, by unfold singleton; rw [if_pos rfl]⟩
    have negativeImpossible : tree.eval zero ≠ true := by
      intro positiveZero
      rcases (correct zero).mp positiveZero with ⟨r, _, bad⟩
      exact Bool.noConfusion bad
    exact False.elim (negativeImpossible (same.symm.trans positive))

private def eraseFirst {Q : Type} [DecidableEq Q] (a : Q) : List Q → List Q
  | [] => []
  | x :: xs => if x = a then xs else x :: eraseFirst a xs

private theorem erase_length {Q : Type} [DecidableEq Q] (a : Q) (xs : List Q)
    (member : a ∈ xs) : (eraseFirst a xs).length + 1 = xs.length := by
  induction xs with
  | nil => cases member
  | cons x xs ih =>
    by_cases same : x = a
    · rw [eraseFirst, if_pos same]
      rfl
    · rw [eraseFirst, if_neg same]
      have tail : a ∈ xs := by
        cases member with
        | head => exact False.elim (same rfl)
        | tail _ h => exact h
      exact congrArg Nat.succ (ih tail)

private theorem mem_erase {Q : Type} [DecidableEq Q] (a b : Q) (xs : List Q)
    (different : b ≠ a) (member : b ∈ xs) : b ∈ eraseFirst a xs := by
  induction xs with
  | nil => cases member
  | cons x xs ih =>
    by_cases same : x = a
    · rw [eraseFirst, if_pos same]
      cases member with
      | head => exact False.elim (different same)
      | tail _ h => exact h
    · rw [eraseFirst, if_neg same]
      cases member with
      | head => exact List.Mem.head _
      | tail _ h => exact List.Mem.tail x (ih h)

/-- Counting follows from explicit removal, without any quotient or finite set. -/
theorem length_le_of_coverage {Q : Type} [DecidableEq Q]
    (domain observations : List Q) (distinct : domain.Nodup)
    (covers : ∀ q, q ∈ domain → q ∈ observations) :
    domain.length ≤ observations.length := by
  induction distinct generalizing observations with
  | nil => exact Nat.zero_le _
  | @cons a rest apart _ ih =>
    have member : a ∈ observations := covers a (List.Mem.head _)
    have shorter : rest.length ≤ (eraseFirst a observations).length := by
      apply ih
      intro b hb
      exact mem_erase a b observations (fun same => apart b hb same.symm)
        (covers b (List.Mem.tail a hb))
    have step := Nat.succ_le_succ shorter
    change rest.length + 1 ≤ (eraseFirst a observations).length + 1 at step
    rw [erase_length a observations member] at step
    exact step

theorem independent_lower_bound {Q : Type} [DecidableEq Q]
    (tree : QueryTree Q) (domain : List Q) (distinct : domain.Nodup)
    (correct : tree.Correct domain) :
    domain.length ≤ (tree.trace zero).length :=
  length_le_of_coverage domain (tree.trace zero) distinct
    (correct_covers_zero tree domain correct)

/-- A concrete correct algorithm closes the model's correctness premise. -/
@[noinline] def scan {Q : Type} : List Q → QueryTree Q
  | [] => .done false
  | q :: rest => .ask q (scan rest) (.done true)

theorem scan_correct {Q : Type} (domain : List Q) :
    (scan domain).Correct domain := by
  intro oracle
  induction domain with
  | nil =>
    constructor
    · intro impossible; cases impossible
    · intro witness; rcases witness with ⟨q, bad, _⟩; cases bad
  | cons q rest ih =>
    cases answer : oracle q with
    | false =>
      change (if oracle q then true else (scan rest).eval oracle) = true ↔ _
      rw [answer]
      constructor
      · intro positive
        rcases ih.mp positive with ⟨r, member, accepted⟩
        exact ⟨r, List.Mem.tail q member, accepted⟩
      · intro witness
        rcases witness with ⟨r, member, accepted⟩
        cases member with
        | head => exact False.elim (Bool.noConfusion (answer.symm.trans accepted))
        | tail _ hr => exact ih.mpr ⟨r, hr, accepted⟩
    | true =>
      change (if oracle q then true else (scan rest).eval oracle) = true ↔ _
      rw [answer]
      exact ⟨fun _ => ⟨q, List.Mem.head _, answer⟩, fun _ => rfl⟩

theorem scan_zero_trace {Q : Type} (domain : List Q) :
    (scan domain).trace zero = domain := by
  induction domain with
  | nil => rfl
  | cons q rest ih => exact congrArg (List.cons q) ih

end QueryTree

/-- Exponential lower bound in the independent branch-answer model. -/
theorem independent_exponential_lower_bound (n : Nat) (tree : QueryTree (List Bool))
    (correct : tree.Correct (branches n)) :
    2 ^ n ≤ (tree.trace QueryTree.zero).length := by
  rw [← branches_length]
  exact QueryTree.independent_lower_bound tree (branches n) (branches_nodup n) correct

/-- Actual query count of a concrete correct independent-answer baseline. -/
theorem independent_bound_is_tight (n : Nat) :
    (QueryTree.scan (branches n)).Correct (branches n) ∧
    ((QueryTree.scan (branches n)).trace QueryTree.zero).length = 2 ^ n :=
  ⟨QueryTree.scan_correct _, (congrArg List.length (QueryTree.scan_zero_trace _)).trans
    (branches_length n)⟩

/-- A promised oracle models branch viability; this does not compute G. -/
def ModelsChain (n : Nat) (G : List Bool → Prop) (oracle : List Bool → Bool) : Prop :=
  ∀ history, history ∈ branches n →
    (oracle history = true ↔ (chainSystem n G).Viable history)

/-- A single branch query, with no search for a relation or transport. -/
def oneQuery (n : Nat) : QueryTree (List Bool) :=
  .ask (retainedHistory n) (.done false) (.done true)

theorem oneQuery_eval (n : Nat) (oracle : List Bool → Bool) :
    (oneQuery n).eval oracle = oracle (retainedHistory n) := by
  cases h : oracle (retainedHistory n) <;> change (if oracle (retainedHistory n) then true else false) = _ <;> rw [h] <;> rfl

theorem oneQuery_count (n : Nat) (oracle : List Bool → Bool) :
    ((oneQuery n).trace oracle).length = 1 := by
  cases h : oracle (retainedHistory n) <;> change (List.cons _ (if oracle (retainedHistory n) then [] else [])).length = 1 <;> rw [h] <;> rfl

/-- Same decision goal, but restricted to the answer tables the audited family admits. -/
theorem oneQuery_correct_for_chain (n : Nat) (G : List Bool → Prop)
    (oracle : List Bool → Bool) (models : ModelsChain n G oracle) :
    (oneQuery n).eval oracle = true ↔ ReferenceViable n G := by
  rw [oneQuery_eval]
  constructor
  · intro positive
    exact ⟨retainedHistory n, retained_mem_branches n,
      (models _ (retained_mem_branches n)).mp positive⟩
  · intro viable
    rcases viable with ⟨h, member, accepted⟩
    apply (models _ (retained_mem_branches n)).mpr
    exact (all_full_histories_same_viability n G h (retainedHistory n)
      ((mem_branches h n).mp member)
      ((mem_branches _ n).mp (retained_mem_branches n))).mp accepted

/-- Single-branch variation is excluded by the actual viability promise. -/
theorem chain_answer_tables_cannot_mix (n : Nat) (G : List Bool → Prop)
    (oracle : List Bool → Bool) (models : ModelsChain n G oracle)
    (h k : List Bool) (hh : h ∈ branches n) (hk : k ∈ branches n) :
    ¬ (oracle h = true ∧ oracle k = false) := by
  intro mixed
  have viable := (models h hh).mp mixed.1
  have targetViable := (all_full_histories_same_viability n G h k
    ((mem_branches h n).mp hh) ((mem_branches k n).mp hk)).mp viable
  have good := (models k hk).mpr targetViable
  exact Bool.noConfusion (mixed.2.symm.trans good)


/-- Correct for precisely the family promise, not for independent answer tables. -/
def ChainCorrect (n : Nat) (tree : QueryTree (List Bool)) : Prop :=
  ∀ G oracle, ModelsChain n G oracle →
    (tree.eval oracle = true ↔ ReferenceViable n G)

theorem oneQuery_chainCorrect (n : Nat) : ChainCorrect n (oneQuery n) :=
  oneQuery_correct_for_chain n

private theorem replicate_length_exact (n : Nat) (b : Bool) :
    (List.replicate n b).length = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ]
    exact congrArg Nat.succ ih

theorem trueCore_models (n : Nat) :
    ModelsChain n (fun _ => True) (fun _ => true) := by
  intro h member
  exact ⟨fun _ => every_branch_viable n (fun _ => True)
    (List.replicate n false) h (replicate_length_exact n false)
    ((mem_branches h n).mp member) True.intro, fun _ => rfl⟩

theorem falseCore_models (n : Nat) :
    ModelsChain n (fun _ => False) QueryTree.zero := by
  intro h _
  constructor
  · intro impossible; cases impossible
  · intro viable
    rcases viable with ⟨c, accepted⟩
    exact False.elim accepted.1

theorem trueCore_reference (n : Nat) : ReferenceViable n (fun _ => True) :=
  ⟨retainedHistory n, retained_mem_branches n,
    (trueCore_models n _ (retained_mem_branches n)).mp rfl⟩

theorem falseCore_reference (n : Nat) : ¬ ReferenceViable n (fun _ => False) := by
  intro viable
  rcases viable with ⟨h, _, c, accepted⟩
  exact accepted.1

/-- Zero queries cannot distinguish the two actual instances with G true/false. -/
theorem chain_at_least_one_query (n : Nat) (tree : QueryTree (List Bool))
    (correct : ChainCorrect n tree) : 1 ≤ (tree.trace QueryTree.zero).length := by
  cases tree with
  | done answer =>
    have yes : answer = true :=
      (correct (fun _ => True) (fun _ => true) (trueCore_models n)).mpr
        (trueCore_reference n)
    exact False.elim (falseCore_reference n
      ((correct (fun _ => False) QueryTree.zero (falseCore_models n)).mp yes))
  | ask q lo hi => exact Nat.succ_le_succ (Nat.zero_le _)

private theorem one_le_two_pow (n : Nat) : 1 ≤ 2 ^ n := by
  induction n with
  | zero => exact Nat.le_refl 1
  | succ n ih =>
    rw [Nat.pow_succ]
    exact Nat.le_trans (by decide : 1 ≤ 1 * 2) (Nat.mul_le_mul_right 2 ih)

/-- The claimed exponential necessity is false for this actual query promise. -/
theorem no_exponential_query_necessity (n : Nat) :
    ¬ (∀ tree : QueryTree (List Bool), ChainCorrect (n + 1) tree →
      2 ^ (n + 1) ≤ (tree.trace QueryTree.zero).length) := by
  intro bound
  have impossible := bound (oneQuery (n + 1)) (oneQuery_chainCorrect (n + 1))
  rw [oneQuery_count] at impossible
  have two : 2 ≤ 2 ^ (n + 1) := by
    rw [Nat.pow_succ]
    exact Nat.mul_le_mul_right 2 (one_le_two_pow n)
  exact Nat.not_succ_le_self 1 (Nat.le_trans two impossible)

/-- The one-query program is not a solver for independent branch oracles. -/
theorem oneQuery_not_independent_correct (n : Nat) :
    ¬ (oneQuery (n + 1)).Correct (branches (n + 1)) := by
  intro correct
  have bad := independent_exponential_lower_bound (n + 1) (oneQuery (n + 1)) correct
  rw [oneQuery_count] at bad
  have two : 2 ≤ 2 ^ (n + 1) := by
    rw [Nat.pow_succ]
    exact Nat.mul_le_mul_right 2 (one_le_two_pow n)
  exact Nat.not_succ_le_self 1 (Nat.le_trans two bad)

/-- An exact optimal query result, with both a lower bound and a closed witness. -/
theorem chain_query_optimum_one (n : Nat) :
    (∀ tree, ChainCorrect n tree → 1 ≤ (tree.trace QueryTree.zero).length) ∧
    ChainCorrect n (oneQuery n) ∧
    (∀ oracle, ((oneQuery n).trace oracle).length = 1) :=
  ⟨chain_at_least_one_query n, oneQuery_chainCorrect n, oneQuery_count n⟩

end ConstitutiveSearch.HistoricalErasure.LowerBound

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.HistoricalErasure.LowerBound.QueryTree.missed_singleton
#print axioms ConstitutiveSearch.HistoricalErasure.LowerBound.QueryTree.correct_covers_zero
#print axioms ConstitutiveSearch.HistoricalErasure.LowerBound.QueryTree.length_le_of_coverage
#print axioms ConstitutiveSearch.HistoricalErasure.LowerBound.QueryTree.independent_lower_bound
#print axioms ConstitutiveSearch.HistoricalErasure.LowerBound.QueryTree.scan_correct
#print axioms ConstitutiveSearch.HistoricalErasure.LowerBound.QueryTree.scan_zero_trace
#print axioms ConstitutiveSearch.HistoricalErasure.LowerBound.independent_exponential_lower_bound
#print axioms ConstitutiveSearch.HistoricalErasure.LowerBound.independent_bound_is_tight
#print axioms ConstitutiveSearch.HistoricalErasure.LowerBound.oneQuery_count
#print axioms ConstitutiveSearch.HistoricalErasure.LowerBound.oneQuery_correct_for_chain
#print axioms ConstitutiveSearch.HistoricalErasure.LowerBound.chain_answer_tables_cannot_mix
#print axioms ConstitutiveSearch.HistoricalErasure.LowerBound.trueCore_models
#print axioms ConstitutiveSearch.HistoricalErasure.LowerBound.falseCore_models
#print axioms ConstitutiveSearch.HistoricalErasure.LowerBound.chain_at_least_one_query
#print axioms ConstitutiveSearch.HistoricalErasure.LowerBound.no_exponential_query_necessity
#print axioms ConstitutiveSearch.HistoricalErasure.LowerBound.oneQuery_not_independent_correct
#print axioms ConstitutiveSearch.HistoricalErasure.LowerBound.chain_query_optimum_one
/- AXIOM_AUDIT_END -/
