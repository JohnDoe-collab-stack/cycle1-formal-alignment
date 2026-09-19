import ConstitutiveSearch.WitnessCompleteCompositionCharacterization
import ConstitutiveSearch.SAT.ProvenanceSequentialization

/-!
# Composition need characterized by SAT trajectory provenance

The primitive search reconstructed from a FlipSymmetricTrajectory is
witness-complete on its provenance-restricted generator type.

Therefore a global composition requirement between two states can be recognized
without executing global ClosureSearch:

* the trajectory-derived primitive search misses directly; and
* there already exists a provenance-restricted TransportCode of size at least
  two between the endpoints.

Any such code is directly sequentializable by the previous provenance theorem.
-/

namespace ConstitutiveSearch
namespace SAT

namespace FlipSymmetricTrajectory

/--
For a certified SAT trajectory, global composition requirement is equivalent to
direct primitive miss plus an already constituted provenance-restricted code of
size at least two.
-/
theorem globalCompositionRequired_iff_provenanceCode
    {rootFormula : Cnf}
    {start finish :
      GeneratedStructuralBranchContext rootFormula}
    {length : Nat}
    (trajectory :
      FlipSymmetricTrajectory
        start
        finish
        length)
    (source target :
      GeneratedStructuralBranchContext rootFormula) :
    PrimitiveHitPath.GlobalCompositionRequired
        trajectory.primitiveSearch
        source
        target ↔
      trajectory.primitiveSearch.find
          source
          target =
        none ∧
        ∃ code :
            TransportClosure
              (ProvenanceStructuralFlipWitness
                (rootFormula := rootFormula)
                trajectory.decisionVars)
              source
              target,
          2 ≤ code.size :=
  PrimitiveHitPath.globalCompositionRequired_iff_code_of_witnessComplete
    trajectory.primitiveSearch
    trajectory.primitiveSearch_witnessComplete
    source
    target

/--
A known provenance code of size at least two behind a direct miss already
supplies the corresponding global-composition certificate, with no global
closure run.
-/
theorem globalCompositionRequired_of_provenanceCode
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
    (directMiss :
      trajectory.primitiveSearch.find
          source
          target =
        none)
    (code :
      TransportClosure
        (ProvenanceStructuralFlipWitness
          (rootFormula := rootFormula)
          trajectory.decisionVars)
        source
        target)
    (codeSize :
      2 ≤ code.size) :
    PrimitiveHitPath.GlobalCompositionRequired
      trajectory.primitiveSearch
      source
      target :=
  (trajectory.globalCompositionRequired_iff_provenanceCode
    source
    target).2
    ⟨directMiss,
      ⟨code, codeSize⟩⟩

end FlipSymmetricTrajectory

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.globalCompositionRequired_iff_provenanceCode
#print axioms ConstitutiveSearch.SAT.FlipSymmetricTrajectory.globalCompositionRequired_of_provenanceCode
/- AXIOM_AUDIT_END -/
