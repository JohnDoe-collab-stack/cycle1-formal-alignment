import ConstitutiveSearch.AcceptedFrontierNormalization

/-!
# Generic control-flow costs for accepted-frontier normalization

This module instruments the exact pair-classification control flow used by the
generic accepted-frontier normalizer.

A pair classification evaluates relation search in both directions, so one
classification corresponds to two RelationSearch.find invocations.  The
instrumentation remains source-level control-flow accounting; it does not assign
machine cost to one find call.
-/

namespace ConstitutiveSearch

universe uRelation

/-- Number of pair classifications performed while inserting one state. -/
def insertPairClassificationCount
    {State : Type}
    {Relation : State → State → Type uRelation}
    (search : RelationSearch Relation)
    (state : State) :
    List State → Nat
  | [] => 0
  | current :: tail =>
      match search.classifyPairCertified state current with
      | .bidirectional _ _ _ _ => 1
      | .forwardOnly _ _ _ => 1
      | .backwardOnly _ _ _ =>
          1 +
            insertPairClassificationCount
              search
              state
              tail
      | .unresolved _ _ =>
          1 +
            insertPairClassificationCount
              search
              state
              tail

/-- Insertion never classifies more pairs than the retained frontier length. -/
theorem insertPairClassificationCount_le_length
    {State : Type}
    {Relation : State → State → Type uRelation}
    (search : RelationSearch Relation)
    (state : State) :
    ∀ rest : List State,
      insertPairClassificationCount search state rest ≤
        rest.length := by
  intro rest
  induction rest with
  | nil =>
      exact Nat.le_refl 0
  | cons current tail inductionHypothesis =>
      cases classification :
          search.classifyPairCertified state current with
      | bidirectional forward backward forwardFound backwardFound =>
          have countExact :
              insertPairClassificationCount
                  search
                  state
                  (current :: tail) =
                1 := by
            unfold insertPairClassificationCount
            rw [classification]
          rw [countExact]
          exact Nat.succ_le_succ (Nat.zero_le _)
      | forwardOnly forward forwardFound backwardNotFound =>
          have countExact :
              insertPairClassificationCount
                  search
                  state
                  (current :: tail) =
                1 := by
            unfold insertPairClassificationCount
            rw [classification]
          rw [countExact]
          exact Nat.succ_le_succ (Nat.zero_le _)
      | backwardOnly backward forwardNotFound backwardFound =>
          have countExact :
              insertPairClassificationCount
                  search
                  state
                  (current :: tail) =
                1 +
                  insertPairClassificationCount
                    search
                    state
                    tail := by
            unfold insertPairClassificationCount
            rw [classification]
          rw [countExact]
          rw [Nat.succ_eq_add_one]
          rw [Nat.add_comm 1 (insertPairClassificationCount search state tail)]
          exact
            Nat.add_le_add_right
              inductionHypothesis
              1
      | unresolved forwardNotFound backwardNotFound =>
          have countExact :
              insertPairClassificationCount
                  search
                  state
                  (current :: tail) =
                1 +
                  insertPairClassificationCount
                    search
                    state
                    tail := by
            unfold insertPairClassificationCount
            rw [classification]
          rw [countExact]
          rw [Nat.succ_eq_add_one]
          rw [Nat.add_comm 1 (insertPairClassificationCount search state tail)]
          exact
            Nat.add_le_add_right
              inductionHypothesis
              1

/--
The original insertion algorithm never increases width by more than the inserted
state itself.
-/
theorem insertAcceptedIntoIrreducible_retained_length_le
    {system : SearchSystem}
    {Relation : system.State → system.State → Type uRelation}
    (search : RelationSearch Relation)
    (action : AcceptedRelationalAction system Relation)
    (state : system.State) :
    ∀ (rest : List system.State)
      (restIrreducible : SearchIrreducible search rest),
      (insertAcceptedIntoIrreducible
        search
        action
        state
        rest
        restIrreducible).retained.length ≤
          rest.length + 1 := by
  intro rest
  induction rest with
  | nil =>
      intro restIrreducible
      exact Nat.le_refl 1
  | cons current tail inductionHypothesis =>
      intro restIrreducible
      let tailIrreducible := restIrreducible.2
      cases classification :
          search.classifyPairCertified state current with
      | bidirectional forward backward forwardFound backwardFound =>
          have retainedExact :
              (insertAcceptedIntoIrreducible
                search
                action
                state
                (current :: tail)
                restIrreducible).retained =
              current :: tail := by
            unfold insertAcceptedIntoIrreducible
            rw [classification]
          rw [retainedExact]
          exact
            Nat.le_add_right
              (current :: tail).length
              1
      | forwardOnly forward forwardFound backwardNotFound =>
          have retainedExact :
              (insertAcceptedIntoIrreducible
                search
                action
                state
                (current :: tail)
                restIrreducible).retained =
              current :: tail := by
            unfold insertAcceptedIntoIrreducible
            rw [classification]
          rw [retainedExact]
          exact
            Nat.le_add_right
              (current :: tail).length
              1
      | backwardOnly backward forwardNotFound backwardFound =>
          have recursiveLe :=
            inductionHypothesis tailIrreducible
          have retainedExact :
              (insertAcceptedIntoIrreducible
                search
                action
                state
                (current :: tail)
                restIrreducible).retained =
              (insertAcceptedIntoIrreducible
                search
                action
                state
                tail
                tailIrreducible).retained := by
            unfold insertAcceptedIntoIrreducible
            rw [classification]
          rw [retainedExact]
          exact
            Nat.le_trans
              recursiveLe
              (Nat.le_add_right
                (tail.length + 1)
                1)
      | unresolved forwardNotFound backwardNotFound =>
          have recursiveLe :=
            inductionHypothesis tailIrreducible
          have retainedExact :
              (insertAcceptedIntoIrreducible
                search
                action
                state
                (current :: tail)
                restIrreducible).retained =
              current ::
                (insertAcceptedIntoIrreducible
                  search
                  action
                  state
                  tail
                  tailIrreducible).retained := by
            unfold insertAcceptedIntoIrreducible
            rw [classification]
          rw [retainedExact]
          exact
            Nat.succ_le_succ
              recursiveLe

/-- Generic normalization never retains more states than it receives. -/
theorem normalizeAcceptedFrontier_retained_length_le
    {system : SearchSystem}
    {Relation : system.State → system.State → Type uRelation}
    (search : RelationSearch Relation)
    (action : AcceptedRelationalAction system Relation) :
    ∀ source : List system.State,
      (normalizeAcceptedFrontier
        search
        action
        source).retained.length ≤
      source.length := by
  intro source
  induction source with
  | nil =>
      exact Nat.le_refl 0
  | cons state tail inductionHypothesis =>
      let tailReduction :=
        normalizeAcceptedFrontier search action tail
      let inserted :=
        insertAcceptedIntoIrreducible
          search
          action
          state
          tailReduction.retained
          tailReduction.irreducible
      have insertedLe :
          inserted.retained.length ≤
            tailReduction.retained.length + 1 :=
        insertAcceptedIntoIrreducible_retained_length_le
          search
          action
          state
          tailReduction.retained
          tailReduction.irreducible
      have tailLe :
          tailReduction.retained.length ≤
            tail.length :=
        inductionHypothesis
      have widened :
          tailReduction.retained.length + 1 ≤
            tail.length + 1 :=
        Nat.add_le_add_right
          tailLe
          1
      exact
        Nat.le_trans
          insertedLe
          widened

/--
Exact number of pair classifications executed by the recursive normalizer.
The tail is normalized first; the head is then compared against the retained
tail produced by that exact recursive normalization.
-/
def normalizationPairClassificationCount
    {system : SearchSystem}
    {Relation : system.State → system.State → Type uRelation}
    (search : RelationSearch Relation)
    (action : AcceptedRelationalAction system Relation) :
    List system.State → Nat
  | [] => 0
  | state :: tail =>
      let tailReduction :=
        normalizeAcceptedFrontier search action tail
      normalizationPairClassificationCount
          search
          action
          tail +
        insertPairClassificationCount
          search
          state
          tailReduction.retained

/-- Quadratic pair-classification envelope in source frontier width. -/
def normalizationPairClassificationQuadraticBudget
    (width : Nat) : Nat :=
  width * width

/--
The exact generic normalization classification count is at most quadratic in
the input frontier width.
-/
theorem normalizationPairClassificationCount_le_quadratic
    {system : SearchSystem}
    {Relation : system.State → system.State → Type uRelation}
    (search : RelationSearch Relation)
    (action : AcceptedRelationalAction system Relation) :
    ∀ source : List system.State,
      normalizationPairClassificationCount
          search
          action
          source ≤
        normalizationPairClassificationQuadraticBudget
          source.length := by
  intro source
  induction source with
  | nil =>
      exact Nat.le_refl 0
  | cons state tail inductionHypothesis =>
      let tailReduction :=
        normalizeAcceptedFrontier search action tail
      have insertLe :
          insertPairClassificationCount
              search
              state
              tailReduction.retained ≤
            tailReduction.retained.length :=
        insertPairClassificationCount_le_length
          search
          state
          tailReduction.retained
      have retainedLe :
          tailReduction.retained.length ≤
            tail.length :=
        normalizeAcceptedFrontier_retained_length_le
          search
          action
          tail
      have insertTailLe :
          insertPairClassificationCount
              search
              state
              tailReduction.retained ≤
            tail.length :=
        Nat.le_trans insertLe retainedLe
      have sumLe :
          normalizationPairClassificationCount
                search
                action
                tail +
              insertPairClassificationCount
                search
                state
                tailReduction.retained ≤
            tail.length * tail.length +
              tail.length :=
        Nat.add_le_add
          inductionHypothesis
          insertTailLe
      change
        normalizationPairClassificationCount
              search
              action
              tail +
            insertPairClassificationCount
              search
              state
              tailReduction.retained ≤
          Nat.succ tail.length *
            Nat.succ tail.length
      have squareExpand :
          Nat.succ tail.length *
              Nat.succ tail.length =
            (tail.length * tail.length +
              tail.length) +
                Nat.succ tail.length := by
        rw [Nat.succ_mul]
        rw [Nat.mul_succ]
      rw [squareExpand]
      exact
        Nat.le_trans
          sumLe
          (Nat.le_add_right
            (tail.length * tail.length +
              tail.length)
            (Nat.succ tail.length))

/-- Each certified pair classification performs exactly two directed find calls. -/
def normalizationFindCallCount
    {system : SearchSystem}
    {Relation : system.State → system.State → Type uRelation}
    (search : RelationSearch Relation)
    (action : AcceptedRelationalAction system Relation)
    (source : List system.State) : Nat :=
  2 *
    normalizationPairClassificationCount
      search
      action
      source

/-- Quadratic directed-find envelope for generic normalization. -/
def normalizationFindCallQuadraticBudget
    (width : Nat) : Nat :=
  2 *
    normalizationPairClassificationQuadraticBudget
      width

/-- Directed find-call count is quadratically bounded in source width. -/
theorem normalizationFindCallCount_le_quadratic
    {system : SearchSystem}
    {Relation : system.State → system.State → Type uRelation}
    (search : RelationSearch Relation)
    (action : AcceptedRelationalAction system Relation)
    (source : List system.State) :
    normalizationFindCallCount
        search
        action
        source ≤
      normalizationFindCallQuadraticBudget
        source.length := by
  unfold normalizationFindCallCount
  unfold normalizationFindCallQuadraticBudget
  exact
    Nat.mul_le_mul_left
      2
      (normalizationPairClassificationCount_le_quadratic
        search
        action
        source)

end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.insertPairClassificationCount
#print axioms ConstitutiveSearch.insertPairClassificationCount_le_length
#print axioms ConstitutiveSearch.insertAcceptedIntoIrreducible_retained_length_le
#print axioms ConstitutiveSearch.normalizeAcceptedFrontier_retained_length_le
#print axioms ConstitutiveSearch.normalizationPairClassificationCount
#print axioms ConstitutiveSearch.normalizationPairClassificationQuadraticBudget
#print axioms ConstitutiveSearch.normalizationPairClassificationCount_le_quadratic
#print axioms ConstitutiveSearch.normalizationFindCallCount
#print axioms ConstitutiveSearch.normalizationFindCallQuadraticBudget
#print axioms ConstitutiveSearch.normalizationFindCallCount_le_quadratic
/- AXIOM_AUDIT_END -/
