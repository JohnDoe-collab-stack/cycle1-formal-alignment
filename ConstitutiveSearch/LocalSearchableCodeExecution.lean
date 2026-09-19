import ConstitutiveSearch.SearchableTransportCode

/-!
# Candidate-free local execution of searchable transport codes

SearchableTransportCode shows that a constituted code can be converted to a
primitive-hit path without running global closure.

This module fixes the local execution policy completely:
* no intermediate candidate list;
* fuel exactly one on every primitive atom.

For every searchable code, that policy executes exactly one primitive query per
atom and zero composition-candidate inspections.

Thus candidate generation and global closure fuel are unnecessary once the
relevant composed code is already constituted locally.
-/

namespace ConstitutiveSearch

universe uGenerator

namespace TransportCode

/--
Exact local execution package for one constituted code.

The path is executed with the minimal local ClosureSearch control:
empty candidate list and fuel one.
-/
structure LocalSequentialExecution
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator)
    {source target : State}
    (code :
      TransportCode
        Generator
        source
        target) : Prop where
  path :
    PrimitiveHitPath
      primitive
      source
      target
  pathLength :
    path.length =
      code.size
  primitiveQueries :
    (path.sequentialStats
        []
        1).primitiveQueries =
      code.size
  compositionCandidates :
    (path.sequentialStats
        []
        1).compositionCandidates =
      0

/--
Every searchable constituted code admits the minimal local execution policy.
No global candidate list and no global closure fuel are needed.
-/
theorem localSequentialExecution_of_searchable
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator)
    {source target : State}
    (code :
      TransportCode
        Generator
        source
        target)
    (searchable :
      code.SearchableBy primitive) :
    LocalSequentialExecution
      primitive
      code := by
  rcases
      code.hasSequentialExecution_of_searchable
        primitive
        []
        1
        (by decide)
        searchable with
    ⟨path,
      pathLength,
      primitiveExact,
      compositionExact⟩
  exact
    { path := path
      pathLength := pathLength
      primitiveQueries := primitiveExact
      compositionCandidates := compositionExact }

/--
A direct primitive miss together with a searchable constituted code of size at
least two simultaneously certifies:
* genuine global composition requirement;
* candidate-free local sequential execution of the same constituted code.
-/
theorem directMiss_searchableCode_hasLocalExecution
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator)
    {source target : State}
    (directMiss :
      primitive.find source target =
        none)
    (code :
      TransportCode
        Generator
        source
        target)
    (searchable :
      code.SearchableBy primitive)
    (codeSize :
      2 ≤ code.size) :
    PrimitiveHitPath.GlobalCompositionRequired
        primitive
        source
        target ∧
      LocalSequentialExecution
        primitive
        code := by
  constructor
  · exact
      (PrimitiveHitPath.globalCompositionRequired_iff_searchableCode
        primitive
        source
        target).2
        ⟨directMiss,
          ⟨code,
            searchable,
            codeSize⟩⟩
  · exact
      localSequentialExecution_of_searchable
        primitive
        code
        searchable

end TransportCode

end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.TransportCode.LocalSequentialExecution
#print axioms ConstitutiveSearch.TransportCode.localSequentialExecution_of_searchable
#print axioms ConstitutiveSearch.TransportCode.directMiss_searchableCode_hasLocalExecution
/- AXIOM_AUDIT_END -/
