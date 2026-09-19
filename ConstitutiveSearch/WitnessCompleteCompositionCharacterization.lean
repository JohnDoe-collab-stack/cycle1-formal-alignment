import ConstitutiveSearch.WitnessCompleteSequentialization

/-!
# Characterizing global composition need from constituted codes

Under witness-complete primitive search, a global composition requirement can
be recognized without running bounded global ClosureSearch.

It is exactly:
* a direct primitive miss between the endpoints; and
* an already constituted TransportCode between those endpoints containing at
  least two primitive atoms.

Witness completeness turns the code directly into an executable primitive-hit
path, while the reverse direction compiles such a path back into a code.
-/

namespace ConstitutiveSearch

universe uGenerator

namespace PrimitiveHitPath

/--
Under witness-complete primitive search, global composition requirement is
equivalent to a direct primitive miss together with an already constituted
TransportCode containing at least two primitive atoms.

This characterization does not execute bounded global ClosureSearch.
-/
theorem globalCompositionRequired_iff_code_of_witnessComplete
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator)
    (complete :
      primitive.WitnessComplete)
    (source target : State) :
    GlobalCompositionRequired
        primitive
        source
        target ↔
      primitive.find source target = none ∧
        ∃ code :
            TransportClosure
              Generator
              source
              target,
          2 ≤ code.size := by
  constructor
  · intro required
    exact
      ⟨required.1,
        globalCompositionRequired_hasCode
          required⟩
  · intro knownCode
    rcases knownCode with
      ⟨directMiss, code, codeSize⟩
    rcases
        code.hasPrimitiveHitPath_of_witnessComplete
          primitive
          complete with
      ⟨path, pathLength⟩
    refine
      ⟨directMiss,
        ⟨path, ?_⟩⟩
    rw [pathLength]
    exact codeSize

end PrimitiveHitPath

end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.PrimitiveHitPath.globalCompositionRequired_iff_code_of_witnessComplete
/- AXIOM_AUDIT_END -/
