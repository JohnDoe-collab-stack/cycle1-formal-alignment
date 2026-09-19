import ConstitutiveSearch.WitnessCompleteSequentialization
import ConstitutiveSearch.SAT.TrajectoryDerivedClosure

/-!
# Provenance-complete sequentialization for SAT trajectories

TrajectoryDerivedClosure reconstructs a primitive search from the exact
variables constituted by a FlipSymmetricTrajectory.

This module proves that the reconstructed primitive search is complete on its
own announced witness type: every ProvenanceStructuralFlipWitness can be
rediscovered by the local provenance search.

Consequently, every finite TransportCode whose atoms are restricted to the
trajectory provenance can be converted directly into an executable
PrimitiveHitPath, and then executed sequentially, without first invoking global
ClosureSearch to rediscover the composed code.
-/

namespace ConstitutiveSearch
namespace SAT

/--
The finite provenance search finds some executable witness for every
provenance-restricted structural flip witness.
-/
theorem provenanceStructuralFlipSearch_witnessComplete
    (rootFormula : Cnf) :
    ∀ vars : List Var,
      (provenanceStructuralFlipSearch
        rootFormula
        vars).WitnessComplete := by
  intro vars
  induction vars with
  | nil =>
      intro source target witness
      cases witness.member
  | cons head rest inductionHypothesis =>
      intro source target witness
      cases headFound :
          (generatedStructuralFlipAtSearch
            rootFormula
            head).find
              source
              target with
      | some relation =>
          simp only [
            provenanceStructuralFlipSearch,
            headFound
          ]
          intro impossible
          cases impossible
      | none =>
          have varNeHead :
              witness.var ≠ head := by
            intro varEq
            have relationAtHead :
                GeneratedStructuralFlipAtRelation
                  head
                  source
                  target := by
              simpa only [varEq] using
                witness.relation
            exact
              (generatedStructuralFlipAtSearch_found_of_relation
                relationAtHead)
                headFound
          have memberRest :
              witness.var ∈ rest := by
            rcases
                List.mem_cons.mp
                  witness.member with
              headEq | tailMember
            · exact
                False.elim
                  (varNeHead headEq)
            · exact tailMember
          let tailWitness :
              ProvenanceStructuralFlipWitness
                (rootFormula := rootFormula)
                rest
                source
                target :=
            { var := witness.var
              member := memberRest
              relation := witness.relation }
          have tailNonNone :
              (provenanceStructuralFlipSearch
                rootFormula
                rest).find
                  source
                  target ≠
                none :=
            inductionHypothesis
              tailWitness
          cases tailFound :
              (provenanceStructuralFlipSearch
                rootFormula
                rest).find
                  source
                  target with
          | none =>
              exact
                False.elim
                  (tailNonNone tailFound)
          | some foundWitness =>
              simp only [
                provenanceStructuralFlipSearch,
                headFound,
                tailFound
              ]
              intro impossible
              cases impossible

namespace FlipSymmetricTrajectory

/--
The primitive search reconstructed from a certified trajectory is complete on
every primitive witness whose variable is carried by that trajectory's
provenance.
-/
theorem primitiveSearch_witnessComplete
    {rootFormula : Cnf}
    {start finish :
      GeneratedStructuralBranchContext rootFormula}
    {length : Nat}
    (trajectory :
      FlipSymmetricTrajectory
        start
        finish
        length) :
    trajectory.primitiveSearch.WitnessComplete := by
  unfold primitiveSearch
  exact
    provenanceStructuralFlipSearch_witnessComplete
      rootFormula
      trajectory.decisionVars

/--
Any already constituted closure code over the trajectory provenance has a
direct primitive-hit path with the same number of atoms.

This theorem does not run bounded global closure.
-/
theorem transportCode_hasPrimitiveHitPath
    {rootFormula : Cnf}
    {start finish :
      GeneratedStructuralBranchContext rootFormula}
    {length : Nat}
    (trajectory :
      FlipSymmetricTrajectory
        start
        finish
        length)
    {source target :
      GeneratedStructuralBranchContext rootFormula}
    (code :
      TransportClosure
        (ProvenanceStructuralFlipWitness
          (rootFormula := rootFormula)
          trajectory.decisionVars)
        source
        target) :
    ∃ path :
        PrimitiveHitPath
          trajectory.primitiveSearch
          source
          target,
      path.length = code.size :=
  code.hasPrimitiveHitPath_of_witnessComplete
    trajectory.primitiveSearch
    trajectory.primitiveSearch_witnessComplete

/--
Any already constituted provenance-restricted closure code can be executed
sequentially with one primitive query per atom and zero composition-candidate
search.
-/
theorem transportCode_hasSequentialExecution
    {rootFormula : Cnf}
    {start finish :
      GeneratedStructuralBranchContext rootFormula}
    {length : Nat}
    (trajectory :
      FlipSymmetricTrajectory
        start
        finish
        length)
    (candidates :
      List
        (GeneratedStructuralBranchContext
          rootFormula))
    (fuel : Nat)
    (fuelPositive : 0 < fuel)
    {source target :
      GeneratedStructuralBranchContext rootFormula}
    (code :
      TransportClosure
        (ProvenanceStructuralFlipWitness
          (rootFormula := rootFormula)
          trajectory.decisionVars)
        source
        target) :
    ∃ path :
        PrimitiveHitPath
          trajectory.primitiveSearch
          source
          target,
      path.length = code.size ∧
        (path.sequentialStats
            candidates
            fuel).primitiveQueries =
          code.size ∧
        (path.sequentialStats
            candidates
            fuel).compositionCandidates =
          0 :=
  code.hasSequentialExecution_of_witnessComplete
    trajectory.primitiveSearch
    trajectory.primitiveSearch_witnessComplete
    candidates
    fuel
    fuelPositive

end FlipSymmetricTrajectory

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.provenanceStructuralFlipSearch_witnessComplete
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.primitiveSearch_witnessComplete
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.transportCode_hasPrimitiveHitPath
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.transportCode_hasSequentialExecution
/- AXIOM_AUDIT_END -/
