import ConstitutiveSearch.SAT.GlobalContextRelation

namespace ConstitutiveSearch.Tests.SATGlobalContextRelationRegression

open SAT

abbrev c0p : Clause :=
  [Literal.positive 0, Literal.positive 2]

abbrev c0n : Clause :=
  [Literal.negative 0, Literal.positive 2]

abbrev c1p : Clause :=
  [Literal.positive 1, Literal.positive 2]

abbrev c1n : Clause :=
  [Literal.negative 1, Literal.positive 2]

abbrev formula : Cnf :=
  [c0p, c0n, c1p, c1n]

abbrev root : GeneratedBranchContext formula :=
  GeneratedBranchContext.root formula

theorem rootVar0Fresh : DecisionsAvoid 0 root.context.decisions :=
  True.intro

abbrev falseParent : GeneratedBranchContext formula :=
  GeneratedBranchContext.child root 0 false rootVar0Fresh

abbrev trueParent : GeneratedBranchContext formula :=
  GeneratedBranchContext.child root 0 true rootVar0Fresh

/-- The two deep states below really have distinct immediate decision histories. -/
theorem parent_histories_differ :
    falseParent.context.decisions ≠ trueParent.context.decisions := by
  decide

theorem falseParentVar1Fresh : DecisionsAvoid 1 falseParent.context.decisions := by
  constructor
  · decide
  · exact True.intro

theorem trueParentVar1Fresh : DecisionsAvoid 1 trueParent.context.decisions := by
  constructor
  · decide
  · exact True.intro

/-- Source and target have different immediate parents but the same second decision. -/
abbrev source : GeneratedBranchContext formula :=
  GeneratedBranchContext.child falseParent 1 true falseParentVar1Fresh

abbrev target : GeneratedBranchContext formula :=
  GeneratedBranchContext.child trueParent 1 true trueParentVar1Fresh

/-- Their residual formulas are globally related by flipping variable zero. -/
theorem formulas_flip_exact :
    target.context.formula =
      Cnf.flipAt 0 source.context.formula := by
  rfl

/-- Their complete constitutive histories are related by the same flip. -/
theorem histories_flip_exact :
    target.context.decisions =
      flipDecisionsAt 0 source.context.decisions := by
  rfl

/-- A global relation now exists without any common-parent witness. -/
def sourceToTarget : GeneratedFlipAtRelation 0 source target :=
  { formulaExact := formulas_flip_exact
    decisionsExact := histories_flip_exact }

/-- Concrete source assignment: x0=false, x1=true, all later variables=true. -/
def sourceAssignment : Assignment
  | 0 => false
  | _ => true

/-- The source assignment satisfies the root formula. -/
def rootCompletion : GeneratedBranchCompletion root :=
  ⟨sourceAssignment,
    .cons rfl
      (.cons rfl
        (.cons rfl
          (.cons rfl .nil)))⟩

/-- Reify the x0=false parent decision. -/
def falseParentCompletion : GeneratedBranchCompletion falseParent :=
  { underlying := rootCompletion
    valueExact := rfl }

/-- Reify the deeper x1=true decision. -/
def sourceCompletion : GeneratedBranchCompletion source :=
  { underlying := falseParentCompletion
    valueExact := rfl }

/-- Transport across different immediate parents. -/
def targetCompletion : GeneratedBranchCompletion target :=
  sourceToTarget.mapCompletion sourceCompletion

/-- Variable zero is flipped by the global transport. -/
theorem target_x0_true :
    target.context.assignment targetCompletion 0 = true := by
  change
    target.context.assignment
      (sourceToTarget.mapCompletion sourceCompletion) 0 = true
  rw [GeneratedFlipAtRelation.mapCompletion_assignment]
  rw [Assignment.flipAt_selected]
  rfl

/-- The unrelated second decision remains unchanged. -/
theorem target_x1_true :
    target.context.assignment targetCompletion 1 = true := by
  change
    target.context.assignment
      (sourceToTarget.mapCompletion sourceCompletion) 1 = true
  rw [GeneratedFlipAtRelation.mapCompletion_assignment]
  rw [Assignment.flipAt_other 0 1]
  · rfl
  · decide

/-- The executable global search reconstructs the relation. -/
theorem global_search_found :
    (generatedFlipAtSearch formula 0).find source target ≠ none := by
  intro impossible
  change some _ = none at impossible
  cases impossible

/-- A heterogeneous pair can now be normalized by a relation independent of parent identity. -/
def heterogeneousPair : List (GeneratedBranchContext formula) :=
  [source, target]

def reducedHeterogeneousPair :=
  normalizeGeneratedFrontierByFlip formula 0 heterogeneousPair

/-- The two different-parent states reduce to one representative. -/
theorem heterogeneous_width_one :
    reducedHeterogeneousPair.width = 1 := by
  rfl

/-- Positive completion existence is preserved in both directions by normalization. -/
theorem heterogeneous_nonempty_iff :
    Nonempty
        (FrontierCompletion GeneratedBranchCompletion heterogeneousPair) ↔
      Nonempty
        (FrontierCompletion GeneratedBranchCompletion
          reducedHeterogeneousPair.retained) :=
  reducedHeterogeneousPair.nonempty_iff

/-- One source-side completion enters the heterogeneous frontier. -/
def sourceFrontierCompletion :
    FrontierCompletion GeneratedBranchCompletion heterogeneousPair :=
  .head sourceCompletion

/-- The normalization transports it to the retained representative. -/
def retainedCompletion :
    FrontierCompletion GeneratedBranchCompletion
      reducedHeterogeneousPair.retained :=
  reducedHeterogeneousPair.preservation.forward.map sourceFrontierCompletion

/-- The retained completion remains interpretable in the original heterogeneous frontier. -/
def restoredHeterogeneousCompletion :
    FrontierCompletion GeneratedBranchCompletion heterogeneousPair :=
  reducedHeterogeneousPair.preservation.backward.map retainedCompletion

end ConstitutiveSearch.Tests.SATGlobalContextRelationRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATGlobalContextRelationRegression.parent_histories_differ
#print axioms ConstitutiveSearch.Tests.SATGlobalContextRelationRegression.formulas_flip_exact
#print axioms ConstitutiveSearch.Tests.SATGlobalContextRelationRegression.histories_flip_exact
#print axioms ConstitutiveSearch.Tests.SATGlobalContextRelationRegression.sourceToTarget
#print axioms ConstitutiveSearch.Tests.SATGlobalContextRelationRegression.rootCompletion
#print axioms ConstitutiveSearch.Tests.SATGlobalContextRelationRegression.sourceCompletion
#print axioms ConstitutiveSearch.Tests.SATGlobalContextRelationRegression.targetCompletion
#print axioms ConstitutiveSearch.Tests.SATGlobalContextRelationRegression.target_x0_true
#print axioms ConstitutiveSearch.Tests.SATGlobalContextRelationRegression.target_x1_true
#print axioms ConstitutiveSearch.Tests.SATGlobalContextRelationRegression.global_search_found
#print axioms ConstitutiveSearch.Tests.SATGlobalContextRelationRegression.reducedHeterogeneousPair
#print axioms ConstitutiveSearch.Tests.SATGlobalContextRelationRegression.heterogeneous_nonempty_iff
#print axioms ConstitutiveSearch.Tests.SATGlobalContextRelationRegression.restoredHeterogeneousCompletion
/- AXIOM_AUDIT_END -/
