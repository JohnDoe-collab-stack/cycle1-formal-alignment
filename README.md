# Structural foundations — constitutive determination, relative alignment, and representation boundary

**English** | [Français](README_fr.md)

> **This repository develops and machine-checks in Lean a constructive framework for following a single constitutive determination across distinct layers without collapsing those layers into one another.**
>
> Objects are individuated before they are read, their roles are determined by the relations that constitute them, dependencies are tested on weakened carriers, and only proven determinations are reconstructed and transported.
>
> In the circular instance, this makes it possible to construct an exact operational continuation whose status changes without loss of constitution, identify its residual occurrence with the fresh identity of constitutive alignment, and prove that this identity persists coherently through every supplied finite extension and across distinct exact realizations.
>
> A separate representation-boundary branch proves a constructive diagonal non-representability result. It does not generate the operational exit and is not used to justify constitutive persistence.

---

## 1. Theoretical unit

The theoretical unit of this project is neither a particular module nor a final theorem.

It is the demonstrated continuity of a **single determination** across several distinct and interdependent layers.

```text
constitution
    ↓
individuated occurrence
    ↓
structural determination
    ↓
extension / continuation
    ↓
change of status
    ↓
exact realization
    ↓
finite persistence
    ↓
transport between realizations
    ↓
readout
```

These layers are related, but they are not identified.

The project deliberately preserves distinctions such as:

```text
occurrence ≠ readout

constitution ≠ realization

realization ≠ admission

admission ≠ independent norm satisfaction

identity ≠ equality of observed values

operational exit ≠ representation exit
```

The central question is therefore not merely:

> What value does an object have?

but first:

> What makes this occurrence this occurrence, which relations constitute its role, and what must be preserved for us to prove that the same determination persists through transformation?

Roles are established before their representations, transported without merging the layers, and only then made available to independent readouts.

---

## 2. Method of relational constitutive roles

The development follows a methodological discipline extracted from the circular instance.

Its condensed form is:

```text
individuate
→ relate
→ separate
→ reconstruct
→ transport
→ diagnose
```

### Individuate

Occurrences are constructed as proof-relevant objects before values are assigned to them.

Two occurrences are not identified merely because some readout gives them the same value.

### Relate

An occurrence is determined through the structural relations in which it participates:

```text
formation
provenance
source
target
position
succession
composition
agreement with a structural role
```

A relational constitutive role is therefore not merely a label attached to an already-given object. It describes how the occurrence is determined within the construction.

### Separate

When it is unclear whether a property must be primitive, the method weakens the carrier while preserving previously established layers.

It then constructs separating models.

For example, the development establishes on weakened carriers that:

```text
exact local agreement + injectivity
⇏ structural order
```

and:

```text
exact local agreement
+ injectivity
+ preserved order
+ intermediate position
⇏ participation in a constitutive composition
```

A countermodel is used to establish a dependency boundary, not merely to illustrate one.

### Reconstruct

After separation, the actual construction structure is reintroduced.

Properties such as precedence and adjacency then become derivable from exact agreement together with the dependent composability of real histories.

The method therefore tries to minimize primitives without impoverishing the object.

A property should not remain primitive when it can already be reconstructed from a more fundamental constitutive structure.

### Transport

A change of representation is accepted as faithful only when the relevant occurrences remain exactly recoverable.

A faithful history interpretation provides forward and backward occurrence maps, pointwise round-trip laws, and structural agreements.

Identity is not inferred from equality of final values, equal cardinality, or a similarity score.

### Diagnose

Only after constitution and preservation have been established are operational and normative statuses compared.

The method keeps distinct:

```text
Construction(H)

FaithfulRealization(A, H)

Regime(H)

Norm(H)
```

A typed exit preserves the candidate and the positive evidence that remains valid while carrying the proof of the exact property that fails.

The result is therefore a **structural diagnosis**, not merely a negative classification.

The complete methodological development is documented in:

[`docs/en/relational_constitutive_roles_method.md`](docs/en/relational_constitutive_roles_method.md).

---

## 3. Order of dependence

The intended order of construction is:

```text
presentation
→ possible formations
→ individuated occurrences
→ exact role/occurrence agreement
→ succession and composition
→ structural invariants
→ faithful concrete realizations
→ derived readings and numerical invariants
→ independently defined norm and operational regime
→ adequacy
→ diagnosis
```

This order is methodological rather than chronological source order.

Its purpose is to prevent a later layer from silently defining an earlier one.

For example:

- a readout must not define occurrence identity;
- a numerical invariant must not define the structure whose invariant it is;
- a regime must not define the independent norm against which its adequacy is evaluated;
- a representation must not retroactively constitute the object it represents.

---

## 4. Constitutive foundation

A `CircularPresentation` determines the data and formation rules of the circular instance.

From it, the development constructs:

```text
PositiveConstitution
        ↓
GeneratedStep
        ↓
History
        ↓
RootedGeneratedHistory
        ↓
History.Occurrence
```

Occurrences are generated inside a dependently typed history rather than extracted from an external sequence of values.

The canonical deployment of the perimeter is:

```text
perimeterDeployment P
```

and the generator remains applicable at its boundary, producing:

```text
oneStepAfterPerimeter P
```

as a genuine strict constitutive continuation.

---

## 5. Local exactness reconstructs global structure

For a circular presentation `P` and a rooted generated history `H`, an exact local realization provides an occurrence of `H` for every non-closing perimeter position together with exact structural agreement.

The central reconstruction theorem is:

```text
ExactNonClosingRealization P H
→
PerimeterExtension P H
```

implemented by:

```lean
ExactNonClosingRealization.toPerimeterExtension
```

The canonical perimeter is therefore reconstructed as an exact initial factor of the history.

This does **not** mean the history is exhausted by the perimeter.

The distinction is essential:

```text
every structural requirement has an exact witness
≠
every occurrence belongs to the covered requirement family
```

The openness left by this distinction is precisely what permits a further continuation to be constructed without invalidating the already-established perimeter realization.

Injectivity is derived from exact agreement rather than separately postulated. Precedence and adjacency are tested on weakened carriers and reconstructed on the actual history carrier.

---

## 6. Residual determination

A positive extension introduces a new part whose residual occurrence can be determined constructively.

The residual analysis is factorized so that the actual determination depends only on a weaker residual core rather than on the entire historical exact-internal-realization contract.

Schematically:

```text
rich historical contract
        ↓
residual determination core
        +
positive new part
        ↓
unique residual occurrence
```

The weakening is genuine in the general class: `SegmentedResidualRoleStrictness.lean` contains positive separators where residual determination still succeeds although the richer exact internal realization or its compatible reconstruction is unavailable.

Conversely, the development characterizes conditions under which richer exact internal structure can be reconstructed.

The factorization therefore separates:

```text
exact determination of the new residual
≠
exact individuation and persistence of all old occurrences
```

The conservation path back to the actual circular producer is explicit. The weak and rich constructions select the same positive occurrence, exposed by results including:

```lean
SegmentedResidualRole.positiveExtension_result_occurrence

StrongPerimetralTurning.oneStepCoreResidualOccurrence_agrees_with_weak

StrongPerimetralTurning.oneStepCoreResidualOccurrence_agrees_with_consumedTurning
```

Thus the weakened derivation is not a competing residual construction. It factorizes the one already used by the circular producer.

---

## 7. Operational turning and change of status

The circular instance realizes the abstract segmented-turning mechanism.

The canonical perimeter is admitted by the operational regime and satisfies the independently defined specification.

The strict continuation:

```text
h⁺ := oneStepAfterPerimeter P
```

is nevertheless internally generated and remains exactly realizable in every supplied `ConcreteContinuationAlgebra P`.

At the same time:

```text
¬ CircularRefinement P h⁺

¬ CircularSpecificationSatisfaction P h⁺
```

The second refutation is proved through the independent specification rather than inferred merely from regime rejection.

The canonical candidate therefore has the status:

```text
internally generated                 yes
constitutively continuous            yes
exactly realizable                   yes
admitted by the current regime       no
satisfies the current specification  no
```

This is the operational phenomenon called **structural OOD** in the project.

It is an architectural interpretation of the formal result, not statistical OOD.

The crucial distinction is:

```text
change of status
≠
loss of determination
```

---

## 8. Identity

In this project, **identity** is an architectural interpretation of verified structural transport laws.

It means the persistence of a constitutive determination across distinct layers through exact transports.

Identity is not defined by:

```text
same readout
same label
same final state
same number of elements
```

Instead, the project proves the correspondences required to track the occurrence itself.

This permits differences of status and representation to remain visible while the determination is preserved.

In condensed form:

```text
same determination
≠ same status
≠ same realization
≠ same readout
```

Identity is the persistence of the first across transformations in which the others may vary.

---

## 9. The operational residual is the fresh constitutive identity

The generic one-step constitutive alignment exposes an exact old/fresh decomposition:

```text
Initial ⊕ Unit
    ≃
Extended
```

The fresh component is not a second object introduced beside the operational residual.

In the actual circular instance, the repository proves:

```text
one-step alignment fresh
=
residual occurrence consumed by operational turning
```

through:

```lean
StructuralEntrypoint.oneStepAlignmentFreshIsConsumedResidual
```

The identification is definitionally grounded: the two descriptions ultimately reduce to the same occurrence term. The alignment layer therefore introduces no independently constructed object that is subsequently matched with the residual.

The corresponding concrete theorem:

```lean
canonicalAlignmentRealization_fresh_eq_residualConcreteOccurrence
```

transports this identity into every canonical realization induced by a supplied `ConcreteContinuationAlgebra`.

The mechanism is therefore:

```text
before the boundary
───────────────────
the new residual is determined

at the boundary
───────────────
that residual is the fresh constitutive identity

after the boundary
──────────────────
the fresh identity becomes an old identity
for every later extension
```

This old/fresh transition is the bridge from residual determination to finite persistence.

---

## 10. Relative alignment

Alignment does not mean making two realizations numerically similar or semantically identical.

For this project:

> **Alignment is the coherent persistence of a constitutive determination across distinct exact realizations and constitutive extensions.**

This sentence is an architectural interpretation of the verified transport and naturality equations.

At one step, old identities remain old, the fresh identity remains distinct from them, and exact realization transports preserve both branches.

At finite depth, the same mechanism is iterated over the actual histories produced by `generate` and `appendGenerated`.

Each generated stage contributes one fresh identity while retaining every identity already constituted.

Schematically:

```text
depth n

old₀
old₁
...
oldₙ₋₁
+
freshₙ
        ↓ extension

depth n+1

old₀
old₁
...
oldₙ₋₁
oldₙ        ← previous fresh
+
freshₙ₊₁
```

The project proves that identities born at distinct depths remain distinct after embedding into a common later carrier.

---

## 11. Finite persistence and naturality

For finite depths, the project proves:

- persistence of previously constituted identities;
- exactly one fresh identity per generated stage;
- distinction of identities born at different depths;
- composition of vertical extensions;
- composition of horizontal transports between realizations;
- pointwise independence from the supplied `DepthExtension` witness;
- naturality between extension and change of realization.

The central square is:

```text
realization A at depth s
        ───── extension in A ─────→
realization A at depth t
        │                           │
        │ transport A→B             │ transport A→B
        │                           │
        ↓                           ↓
realization B at depth s
        ───── extension in B ─────→
realization B at depth t
```

with pointwise commutation:

```text
T[A,B]^t(E[A]^{s,t}(x))
=
E[B]^{s,t}(T[A,B]^s(x)).
```

Thus:

```text
extend then change realization
=
change realization then extend
```

Extension through intermediate depths and transport through intermediate realizations compose coherently.

The repository has no infinite-history object and no ω-stage concrete carrier. Persistence is nevertheless uniform in arbitrary finite depth rather than given by a separate theorem for each depth.

---

## 12. Persistence of the operational residual

Because the first fresh identity is exactly the operational residual occurrence, the general finite-persistence machinery applies to that operationally produced object.

The public façade exposes:

```lean
finiteOperationalResidualPersists
```

and:

```lean
finiteOperationalResidualNaturality
```

The established chain is therefore:

```text
operational residual
        ↓
fresh constitutive identity
        ↓
finite persistence
        ↓
exact realization transport
        ↓
naturality across realizations
```

This does **not** transport the negative admission status itself through every later depth.

What persists is the identity of the occurrence that marked the first operational boundary.

---

## 13. Exact realization and the structural bus

A concrete realization is not accepted merely because it produces an output.

An `ExactHistoryInterpretation` provides:

```text
free occurrence → concrete occurrence

concrete occurrence → free occurrence

backward(forward(x)) = x

forward(backward(y)) = y
```

together with structural agreement for the realized occurrence.

For the canonical perimeter, the project has exact correspondences:

```text
perimeter positions
        ≃
free occurrences
        ≃
concrete occurrences
```

For two supplied exact realizations `A` and `B`, their coordination is induced through this common structural index.

It is not introduced as an independent pairwise matching.

Schematically:

```text
                 structural identity
                 /                 \
                /                   \
               ↓                     ↓
        realization A          realization B
```

The induced transport satisfies:

```text
T[A,B](c_A(p)) = c_B(p)
```

and through a third realization:

```text
T[B,C](T[A,B](x)) = T[A,C](x).
```

This architecture is referred to as a **structural bus**.

It provides exact co-indexation.

It does not assert semantic agreement between independently supplied values, and the abstract bus interface itself does not assert uniqueness among all possible exact buses.

---

## 14. Readouts come after constitution

Once occurrences and their exact correspondences have been established, arbitrary readouts may be attached:

```text
Occurrence → Value
```

The value type is independent of the constitution.

A readout may be:

- injective;
- non-injective;
- constant;
- numerical;
- symbolic;
- type-valued.

None of these possibilities changes occurrence identity.

Readout transport is reindexing over an already-established structural transport.

The direction is:

```text
constitution of occurrences
→ exact correspondences
→ open family of readouts
```

not:

```text
matching readouts
→ reconstructed identity
```

An equality of readout values is never used as a substitute for equality of constituted occurrences.

---

## 15. Relative norm and operational regime

The project distinguishes four levels:

```text
Construction(H)

F_A(H) := ExactConcreteRealization A H

R(H)   := CircularRefinement P H

S(H)   := CircularSpecificationSatisfaction P H
```

They answer different questions:

| Layer | Question |
|---|---|
| constitution | can the object be formed? |
| faithful realization | is the object exactly preserved in this implementation? |
| regime | is the object operationally admitted? |
| norm | does the object satisfy the independent specification? |

The norm is not defined as “whatever the regime accepts.”

Instead, the project constructs:

```text
R(H) → S(H)

S(H) → H = perimeterDeployment P

S(H) → R(H)
```

through:

```lean
circularRefinement_soundSpecification

CircularSpecificationSatisfaction.eq_perimeter

circularSpecification_complete
```

Regime and norm therefore classify the same histories in the circular instance while retaining distinct witness types, definitions, and proof routes.

The point is not to collapse them into one notion.

The point is to make their adequacy a theorem.

---

## 16. Structural diagnosis

A regime exit is not represented merely by:

```text
¬ Regime(candidate)
```

It preserves the candidate and the positive evidence that remains valid.

The canonical diagnostic retains, on the same constructed history:

```text
candidate

exact realization

regime rejection

independent specification rejection

adequacy information
```

The method can therefore state precisely:

> this object still exists,
> this structure is still preserved,
> this implementation still realizes it exactly,
> and this exact operational or normative property is what no longer holds.

This is the project’s notion of relative diagnosis.

---

## 17. Mediated coherence

The repository also isolates a generic mechanism for mediated commutation.

Its fundamental result is **observed commutation without any faithfulness assumption**:

```lean
MediatedTransitionCoherence.observed_commutation
```

Literal equality can then be recovered when the relevant observed values are reflected:

```lean
MediatedTransitionCoherence.commute_of_local_reflection
```

Global injectivity is one sufficient way to provide that reflection:

```lean
MediatedTransitionCoherence.commute
```

The distinction is important:

```text
observed commutation
does not require faithfulness

literal commutation
requires reflection of the relevant equality
```

The repository does not claim that the local-reflection premise is, in the presence of all the other hypotheses, automatically a strictly weaker logical condition than the literal conclusion itself.

At the finite-alignment level, adjacent naturality squares can also be pasted.

The regression suite includes a model with a provably non-injective intermediate observation in which outer observed commutation is retained; terminal reflection recovers the outer literal square.

---

## 18. Representation boundary

`RepresentationBoundary` is a separate branch.

It does not produce the operational continuation and it does not establish constitutive persistence.

Its autonomous kernel receives an evaluator:

```text
eval : Code → Code → Prop
```

and defines:

```lean
diagonalStatus eval code := ¬ eval code code
```

It then proves constructively that this diagonal predicate is not internally representable:

```lean
diagonalStatus_notRepresentable
```

and therefore that global representation closure fails:

```lean
noGlobalRepresentationClosure
```

This is a semantic diagonal non-representability result.

It is not a formalization of Gödel incompleteness, syntax, provability, or arithmetization.

---

## 19. Circular status representation

The circular operational regime and independent specification have proposition-level statuses:

```text
CircularRegimeStatus P H

CircularSpecificationStatus P H
```

obtained by observing their witness types through `Nonempty`.

The established witness maps provide their proposition-level adequacy.

A supplied exact representation of one of these selected statuses can therefore be transported to the other.

The representation-boundary application combines:

```text
exact representation of selected determined statuses

+

non-representability of the evaluator's diagonal status
```

without identifying the operational candidate with the diagonal predicate.

The two exits remain distinct:

```text
operational exit
=
a constituted history whose admission status changes

representation exit
=
a predicate not internally representable by an evaluator
```

No theorem converts one object into the other.

---

## 20. Selected machine-checked results

| Result | Main Lean anchor |
|---|---|
| exact local realization reconstructs the perimeter | `ExactNonClosingRealization.toPerimeterExtension` |
| strict continuation after the perimeter exists | `oneStepAfterPerimeter`, `oneStepAfterPerimeterStrict` |
| generic positive residual core yields a unique residual occurrence | `SegmentedResidualRole.positiveCore_hasUniqueResidualOccurrence` |
| actual one-step residual occurrence | `StrongPerimetralTurning.oneStepCoreResidualOccurrence` |
| continuation remains exactly realizable | `exactlyInterpretHistory` |
| continuation leaves the operational regime | `oneStepAfterPerimeter_notCircularRefinement` |
| continuation fails the independent specification | `oneStepAfterPerimeter_notSpecificationSatisfaction` |
| first alignment fresh = consumed operational residual | `oneStepAlignmentFreshIsConsumedResidual` |
| finite persistence of the operational residual | `finiteOperationalResidualPersists` |
| naturality of residual persistence | `finiteOperationalResidualNaturality` |
| extensions compose | `Alignment.FiniteConstitutiveAlignment.Realization.extend_comp` |
| transports between realizations compose | `Alignment.FiniteConstitutiveAlignment.Realization.transport_comp` |
| extension and change of realization commute | `Alignment.FiniteConstitutiveAlignment.Realization.extend_transport_natural` |
| identities born at distinct depths remain distinct | `Alignment.IteratedCarrier.fresh_ne_fresh_of_depth_ne` |
| readout distinctions already present remain persistent | `Alignment.ReadoutPersistence` |
| observed mediated squares commute without faithfulness | `MediatedTransitionCoherence.observed_commutation` |
| literal equality follows when relevant values are reflected | `MediatedTransitionCoherence.commute_of_local_reflection`, `commute` |
| adjacent mediated squares paste | `Alignment.MediatedTransitionPasting` |
| diagonal status is not internally representable | `diagonalStatus_notRepresentable` |
| global representation closure fails | `noGlobalRepresentationClosure` |

---

## 21. What the project does not claim

The current development does not establish:

- semantic agreement between independently supplied readouts;
- unconditional uniqueness of every exact correspondence;
- a universal theory of every possible alignment problem;
- behavioural alignment of arbitrary AI systems;
- guarantees for trained large-scale machine-learning models;
- an infinite-history object or an ω-stage concrete carrier;
- equality between operational exit and representation exit;
- a Gödel incompleteness theorem;
- universal non-representability independent of the supplied evaluator;
- that the method of relational constitutive roles is already a universal metatheorem.

Finite persistence is nevertheless quantified uniformly over arbitrary finite target depth.

---

## 22. Source architecture

### Structural and residual foundations

- [`SegmentedResidualRole.lean`](SegmentedResidualRole.lean)  
  isolates the dependencies required for residual determination, reconstruction conditions, and compatibility with the richer historical API.

- [`SegmentedResidualRoleStrictness.lean`](SegmentedResidualRoleStrictness.lean)  
  supplies positive separators showing where the weaker residual core and richer internal-realization contract diverge.

- [`AbstractSegmentedTurning.lean`](AbstractSegmentedTurning.lean)  
  defines generic boundary, regime-classification, turning, and obstruction structures independently of circularity.

- [`ExactTypeTransport.lean`](ExactTypeTransport.lean)  
  provides constructive exact two-sided transports and their composition laws.

### Circular producer

- [`StrongPerimetralTurning.lean`](StrongPerimetralTurning.lean)  
  implements the circular presentation, constitutive generator, histories, local/global reconstruction, concrete realization, operational regime, independent norm, and circular turning instance.

### Alignment and persistence

- [`Alignment/Constitutive.lean`](Alignment/Constitutive.lean)  
  defines generic exact one-step old/fresh constitutive alignment.

- [`Alignment/FinitePersistence.lean`](Alignment/FinitePersistence.lean)  
  derives finite persistence, cross-depth identity structure, realization transport, composition, and naturality.

- [`Alignment/ReadoutPersistence.lean`](Alignment/ReadoutPersistence.lean)  
  attaches readouts downstream of identity and proves persistence of already-established distinctions.

- [`MediatedTransitionCoherence.lean`](MediatedTransitionCoherence.lean)  
  provides the generic observed-commutation and reflection kernel.

- [`Alignment/MediatedTransitionCoherence.lean`](Alignment/MediatedTransitionCoherence.lean)  
  instantiates mediated coherence for finite constitutive alignment.

- [`Alignment/MediatedTransitionPasting.lean`](Alignment/MediatedTransitionPasting.lean)  
  proves composition and pasting of adjacent mediated naturality squares.

### Circular persistence instance

- [`StrongPerimetralTurning/ConstitutivePersistence.lean`](StrongPerimetralTurning/ConstitutivePersistence.lean)  
  connects the circular one-step continuation to generic constitutive alignment and identifies the fresh identity with the operational residual occurrence.

- [`StrongPerimetralTurning/IteratedConstitutivePersistence.lean`](StrongPerimetralTurning/IteratedConstitutivePersistence.lean)  
  instantiates finite persistence on histories actually generated by the circular producer.

### Public structural façade

- [`StructuralEntrypoint.lean`](StructuralEntrypoint.lean)  
  presents the principal verified structural junctions at human scale without becoming a dependency of their proofs.

### Representation boundary

- [`RepresentationBoundary/DiagonalizationKernel.lean`](RepresentationBoundary/DiagonalizationKernel.lean)  
  contains the autonomous constructive diagonal kernel.

- [`RepresentationBoundary/CircularStatusRepresentation.lean`](RepresentationBoundary/CircularStatusRepresentation.lean)  
  applies that kernel to proposition-level circular statuses.

- [`RepresentationBoundary.lean`](RepresentationBoundary.lean)  
  is the import-only public aggregator of the representation-boundary branch.

### Validation and executable examples

- [`Tests/ResidualAuditRegression.lean`](Tests/ResidualAuditRegression.lean)  
  tests the residual-core factorization and separator behaviour.

- [`Tests/DynamicAlignmentRegression.lean`](Tests/DynamicAlignmentRegression.lean)  
  exercises finite persistence and identity separation.

- [`Tests/MediatedTransitionCoherenceRegression.lean`](Tests/MediatedTransitionCoherenceRegression.lean)  
  tests mediated commutation and the load-bearing hypotheses of the generic kernel.

- [`Tests/MediatedTransitionPastingRegression.lean`](Tests/MediatedTransitionPastingRegression.lean)  
  includes the non-faithful-middle pasting regression.

- [`Examples/ConcreteContinuation/LoggedAlgebra.lean`](Examples/ConcreteContinuation/LoggedAlgebra.lean)  
  supplies a constructive non-identity concrete realization.

- [`Examples/Alignment/IteratedReadout.lean`](Examples/Alignment/IteratedReadout.lean)  
  computes non-constant readouts across generated stages and distinct realizations.

---

## 23. Documentation

For the complete arguments and methodological details:

- [Structural foundations](docs/en/structural_foundations.md)
- [Circular instance — relative alignment](docs/en/relative_alignment.md)
- [Method of relational constitutive roles](docs/en/relational_constitutive_roles_method.md)
- [Representation boundary](docs/en/representation_boundary.md)
- [Verified architecture map](docs/en/verified_architecture_map.md)
- [Build and axiom audit](audit/AUDIT_BUILD.txt)
- [Authorship disclosure](AI_AUTHORSHIP.md)

French counterparts are provided for the scientific documentation.

---

## 24. Reproduction

The repository is a standalone artifact: no private source history is required to build or inspect it.

With `elan`, or an equivalent environment that reads `lean-toolchain`:

```bash
lake clean
lake build
lake build AuditRegression
```

Verify the scientific-source manifest on Linux or macOS:

```bash
bash scripts/verify-manifest.sh
```

On PowerShell 7:

```powershell
pwsh -NoProfile -File scripts/verify-manifest.ps1
```

or Windows PowerShell:

```powershell
powershell.exe -NoProfile -ExecutionPolicy Bypass -File scripts/verify-manifest.ps1
```

`MANIFEST.sha256` covers the published Lean sources and the canonical scientific documents listed in it.

Repository metadata and access documents are outside that scientific-source manifest. In particular, the manifest does not hash-anchor:

```text
README.md
README_fr.md
lean-toolchain
lakefile.toml
lake-manifest.json
.github/workflows/lean.yml
audit/AUDIT_BUILD.txt
MANIFEST.sha256
```

Their identity is fixed by the audited Git commit rather than by `MANIFEST.sha256`.

The project CI exercises the development on Linux and Windows.

---

## 25. Constructivity and audit discipline

The scientific development is designed to remain constructive.

The repository scans and audits relevant source declarations for dependencies or constructs such as:

```text
axiom
sorry
admit
Classical
noncomputable
propext
Quot.sound
```

Every Lean source ends with an explicit `#print axioms` audit block.

Those blocks name a selected set of declarations in each file: coverage is complete in some small modules and intentionally partial in larger modules such as `StrongPerimetralTurning.lean`.

Every declaration named in those source audit blocks is reported by Lean as depending on no axiom.

On the currently audited tree, the full build emits 1,161 lines of the form:

```text
does not depend on any axioms
```

and zero lines reporting:

```text
depends on axioms
```

Separating models and regression tests are used not only to demonstrate success cases but also to test dependency boundaries and prevent stronger claims from silently entering through overconstrained definitions.

---

## 26. Scope

The complete verified instance is currently circular/perimetral.

The method of relational constitutive roles is broader as a methodological extraction, but it is not yet a universal Lean metatheorem.

A major next scientific test would be an independently constructed second non-circular domain using the same discipline:

```text
individuate
→ relate
→ separate
→ reconstruct
→ transport
→ diagnose
```

without redesigning the method around that second instance.

Such an instantiation would help distinguish what belongs to the general method from what is specific to circular geometry.

---

## 27. Condensed view

The project can be summarized by two movements.

### Constitutive movement

```text
local structural determination
        ↓
exact reconstruction
        ↓
internally generated continuation
        ↓
residual occurrence
        ↓
change of operational/normative status
        │
        │ without loss of constitution
        ↓
fresh constitutive identity
        ↓
finite persistence
        ↓
coherent transport across realizations
        ↓
readout only afterwards
```

### Representation movement

```text
determined proposition-level statuses
        ↓
exact representation
        ↓
representation transport

and independently

evaluator
        ↓
diagonal status
        ↓
non-representability
        ↓
failure of global representation closure
```

The two movements are structurally related but formally distinct.

The first studies how a determination persists through construction, extension, realization, and change of status.

The second studies the boundary of exact representation relative to an evaluator.

---

## 28. Guiding principle

The guiding principle of the project is:

> **Preserve the finest available individuation and the relations that constitute it; test each dependency on the weakest carrier where it can be separated; reconstruct only what follows from restored structure; transport only determinations whose preservation has been proved; and diagnose a boundary by retaining, on the same object, both the positive witnesses of what remains and the negative proof of what ceases to hold.**

Within the circular instance, this discipline supports the following architectural interpretation:

> **Differences of status are preserved while exact transports allow one constitutive determination to pass coherently through distinct layers and realizations.**

In this architectural sense:

```text
identity
=
persistence of a constitutive determination
through exact transports

alignment
=
coherent persistence of that identity
across distinct realizations and extensions
```

These are interpretations constrained by the verified transport, persistence, and naturality theorems.

They do not identify the layers being crossed.

Their separation is precisely what makes the persistence meaningful.

---

## License and citation

The project is distributed under Apache-2.0.

Citation metadata is provided in [`CITATION.cff`](CITATION.cff).

## Authorship

> **Conceptual-authorship and AI-generation disclosure.**
>
> The project owner declares that the essential ideas and research direction are their own, and that the entire textual and code content of this repository — Lean sources, formal statements, proofs, examples, documentation, translations, scripts, metadata, audit materials, and repository organization — was written by models in OpenAI's ChatGPT series under human direction through successive interactions.
>
> See [`AI_AUTHORSHIP.md`](AI_AUTHORSHIP.md) for the complete bilingual disclosure.
