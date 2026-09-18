import ConstitutiveSearch.SAT.ExplicitStackedSymmetricFamily

namespace ConstitutiveSearch.Tests.SATExplicitStackedSymmetricFamilyRegression

open ConstitutiveSearch
open SAT

abbrev formula3 : Cnf :=
  explicitStackedSymmetricFamily 3

theorem formula3_clause_count :
    formula3.length = 6 := by
  exact stackedSymmetricBlocks_length 3 3

abbrev root3 :
    GeneratedStructuralBranchContext formula3 :=
  explicitStackedRoot 3

def trajectory3 :=
  explicitStackedTrajectory 3

theorem trajectory3_trace_length :
    trajectory3.trajectory.widthTrace.length = 7 := by
  change
    (explicitStackedTrajectory 3).trajectory.widthTrace.length = 7
  exact explicitStackedTrajectory_length 3

theorem trajectory3_width_bound :
    ∀ width : Nat,
      width ∈ trajectory3.trajectory.widthTrace →
        width ≤ 2 := by
  intro width member
  exact
    explicitStackedTrajectory_width_le_two
      3
      width
      member

def allTrue : Assignment :=
  fun _ => true

theorem allTrueSatisfies :
    Satisfies allTrue formula3 :=
  .cons rfl
    (.cons rfl
      (.cons rfl
        (.cons rfl
          (.cons rfl
            (.cons rfl .nil)))))

def rootContinuation :
    GeneratedStructuralBranchContinuation root3 :=
  ⟨allTrue, True.intro⟩

theorem rootContinuation_accept :
    GeneratedStructuralBranchAccept
      root3
      rootContinuation :=
  allTrueSatisfies

theorem root_viable :
    FrontierViable
      (generatedStructuralBranchSystem formula3)
      [root3] := by
  exact
    ⟨.head rootContinuation,
      rootContinuation_accept⟩

theorem endpoint_viable_iff :
    FrontierViable
        (generatedStructuralBranchSystem formula3)
        [root3] ↔
      FrontierViable
        (generatedStructuralBranchSystem formula3)
        [trajectory3.finish] :=
  explicitStackedTrajectory_viable_iff 3

theorem endpoint_viable :
    FrontierViable
      (generatedStructuralBranchSystem formula3)
      [trajectory3.finish] :=
  endpoint_viable_iff.mp root_viable

end ConstitutiveSearch.Tests.SATExplicitStackedSymmetricFamilyRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATExplicitStackedSymmetricFamilyRegression.formula3_clause_count
#print axioms ConstitutiveSearch.Tests.SATExplicitStackedSymmetricFamilyRegression.trajectory3
#print axioms ConstitutiveSearch.Tests.SATExplicitStackedSymmetricFamilyRegression.trajectory3_trace_length
#print axioms ConstitutiveSearch.Tests.SATExplicitStackedSymmetricFamilyRegression.trajectory3_width_bound
#print axioms ConstitutiveSearch.Tests.SATExplicitStackedSymmetricFamilyRegression.rootContinuation
#print axioms ConstitutiveSearch.Tests.SATExplicitStackedSymmetricFamilyRegression.rootContinuation_accept
#print axioms ConstitutiveSearch.Tests.SATExplicitStackedSymmetricFamilyRegression.root_viable
#print axioms ConstitutiveSearch.Tests.SATExplicitStackedSymmetricFamilyRegression.endpoint_viable_iff
#print axioms ConstitutiveSearch.Tests.SATExplicitStackedSymmetricFamilyRegression.endpoint_viable
/- AXIOM_AUDIT_END -/
