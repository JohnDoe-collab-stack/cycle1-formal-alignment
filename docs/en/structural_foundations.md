# Structural foundations

*From relational constitution to relative and reflective alignment*

**English** | [Français](../fr/fondements_structurels.md)

This document presents the repository's complete architecture: relational
constitution, dependently typed construction, faithful realization, relative
alignment, and reflective diagonal non-closure. Its guiding principle is to
preserve the finest-grained individuation and the relations that constitute it,
then to project, classify, quotient, represent, or measure only after proving
what is preserved.

## Architectural thesis

> **Architectural thesis.** Taking Gödel's diagonal lesson seriously as an
> architectural constraint means that design cannot remain static or globally
> closed. It must be dynamic, relative, and locally determined.

The decisive pattern is diagonal: resources internal to a construction can
produce a case that escapes a proposed global closure while preserving the
construction that produced it. **Structural OOD** names the operational form of
this pattern: the candidate remains internally generated and, like every rooted
generated history in this development, admits an exact concrete realization as
its status changes relative to the regime.

Cycle 1 machine-checks this operational architecture on
`oneStepAfterPerimeter P`: an internally generated strict continuation remains
exactly realizable in every `ConcreteContinuationAlgebra P`, while its regime
and normative status are precisely determined. Cycle 2 verifies the reflective
architecture: exact representation of the aligned statuses is preserved, and a
diagonal status locates the boundary of global representability.

The four distinctions below form the first structural decomposition of this
thesis. Priority of individuation supports local determination; the separation
of local totality from globality prevents premature global closure; succession
provides an internal dynamics without an external clock; and time and the
global are derived from trajectories rather than presupposed as a completed
framework.

## 1. Overall architecture

```text
structural foundation
  relational constitution
  → dependently typed construction
  → faithful realization
  ↓
Cycle 1 — relative alignment
  operational regime and independent norm
  → witness transformation in each direction
  → exact adequacy
  ├── one-occurrence continuation
  │     → localized operational exit
  │     → structural OOD
  │
  └── proposition-level observation by `Nonempty`
        → equivalence of the two inhabited statuses
        → pullback and transport to codes
        → exact representation of determined statuses
        + evaluator diagonalization
        → non-representable diagonal status
        → failure of global reflective closure
```

The diagram is a dependency graph, not one theorem. Its bifurcation occurs only
after the two Cycle 1 witness transformations have established adequacy. The
operational branch continues through `oneStepAfterPerimeter`; the reflective
branch begins by observing the inhabitability of the two adequate witness
families. No edge runs from the operational exit to diagonalization.

| Transition | Status | Main Lean anchor |
|---|---|---|
| constitution → history | verified | `RootedGeneratedHistory` |
| roles → exact realization | verified | `ExactNonClosingRealization` |
| realization → faithful concrete transport | verified | `exactlyInterpretHistory` |
| regime witness → norm witness | verified | `circularRefinement_soundSpecification` |
| norm witness → regime witness | verified | `circularSpecification_complete` |
| two witness maps → exact adequacy | verified | `circularNormativeAdequacy`, `circularRefinement_adequateAlong` |
| continuation → operational exit | verified | `oneStepAfterPerimeter`, `RegimeExit` |
| adequacy → equivalence of inhabited statuses | verified | `circularStatusAdequacy` |
| coded equivalence → transported representation | verified | `transportRepresentation` |
| evaluator → diagonal status outside representation | verified | `diagonalStatus_notRepresentable` |
| diagonal status → global non-closure | verified | `noGlobalReflectiveClosure` |
| complete chain → architecture beyond global closure | architectural interpretation | synthesis of both cycles |

## 2. The four distinctions

### 2.1 Individuation definitionally precedes identity

Constitutions are built together with their formations. Their readings are then
extracted without being used to define their identity.

For a reading:

```text
ρ : O → V
```

the equality:

```text
ρ(x) = ρ(y)
```

does not in general imply:

```text
x = y
```

Formations, provenances, positions, and roles may therefore remain distinct
when some readings coincide. The priority of individuation does not remove
equality from the occurrence type; it only prevents that individuation from
being defined retrospectively by an extensional reading.

### 2.2 Totality is local and is not globality

A realization may satisfy exactly all the requirements of a perimeter without
exhausting the possible constructions beyond it. A locality that is total
relative to its requirements is therefore not maximal in the space of
constructions.

This distinction makes the central result of the circular application
intelligible:

```text
locally complete perimetral deployment
  +
effectively constructible free continuation
```

### 2.3 Succession is indexed by a total locality

In the perimetral realization, generated steps depend on the presentation and
the source constitution. No external clock is required to define their
succession.

### 2.4 Time and the global are derived from the trajectory

Histories compose steps. Their prefixes define a structural precedence. Here,
time denotes that precedence and the global denotes the composed history,
relative to the given presentation.

The four distinctions therefore form an order of dependence:

```text
presentation
→ locality and roles
→ formed occurrences and local realization
→ succession
→ history
```

Then:

```text
history → prefix precedence        → time
history → composition              → global
history → concrete interpretation  → readings
```

A reading does not constitute the occurrence it reads. A local totality does
not constitute a globality. A history is not indexed by an external clock. Time
and the global are obtained from its structure.

## 3. Relational constitutive roles

The method determines an occurrence by its constitution and by the relations in
which it participates before reducing it to a reading, classification, or value.

```text
individuation
→ formation
→ occurrence
→ relational role
→ succession and composition
→ invariants
→ readings and classifications
```

This order rules out several premature identifications:

```text
same reading
≠ same occurrence

same role
≠ same occurrence without additional faithfulness

being positioned between two occurrences
≠ participating in their constitutive composition

being admitted by a regime
≠ satisfying an independent specification
```

A **relational constitutive role** is the role of an occurrence determined by
the structural relations in which it participates within a constitution.
*Constitutive* means that the role is not an external classification added
afterward; *relational* means that it cannot be reduced to an isolated property
of the occurrence. Formation, provenance, source, target, succession, locality,
and participation may all contribute to that determination without allowing a
reading to redefine the occurrence retrospectively.

The stabilized methodological principle is:

> **Preserve the finest-grained individuation and the relations that constitute
> it, and then project, classify, quotient, represent, or measure only after
> proving that the forgotten information is not required for the determination
> at hand.**

### 3.1 Realizing a role exactly

A locality provides roles or requirements to be realized. Realizing a role is
not merely a matter of assigning a label. A structural agreement must be
established between the effectively constituted occurrence and the required
role.

In the perimetral application, `RequirementOccurrenceAgreement` records exact
equality between the source cursor of an occurrence and the canonical cursor
corresponding to a `NonClosingPosition`. In a rooted generated history, that
structural address reconstructs the complete source state, canonical target,
and generated `LocatedStep`.

```text
required role
+ individuated occurrence
+ exact structural agreement
```

Agreements on source, target, compatibility, and provenance are then derived
from this exact structural address. This is a normalization of the primitive
data, not a strict weakening: the cursor and complete located-step formulations
reconstruct one another within rooted generated histories.

### 3.2 Exact coverage without exhaustiveness

`ExactNonClosingRealization` provides:

```text
for each non-closing requirement
  one occurrence that realizes it exactly

for two distinct requirements
  two distinct occurrences
```

It does not state that these occurrences exhaust the whole history. A history
may therefore realize all required requirements exactly while still containing
additional occurrences.

```text
exact coverage of requirements
≠ exhaustive classification of occurrences
```

### 3.3 Order and adjacency derived in the actual history

Local exactness on a weakened carrier does not by itself determine order or
adjacency. In a genuine `RootedGeneratedHistory`, however, composability makes
it possible to reconstruct both:

```lean
ExactNonClosingRealization.preservesPrecedence
ExactNonClosingRealization.preservesNext
```

These theorems establish, respectively, the canonical precedence and canonical
constitutive adjacency of the realized occurrences.

```text
ExactNonClosingRealization
+ RootedGeneratedHistory
→ correct precedence
+ correct constitutive adjacency
```

The local status is therefore:

```text
ExactNonClosingRealization   local primitive
precedence                   derived
adjacency                    derived
participation                carried by History
relevant contiguity          derived
```

## 4. Minimizing primitives with separating models

The method does not consist in accumulating primitives, but in determining
which ones are genuinely independent. The development uses weakened carriers
and separating models for this purpose.

`SemanticTrace` retains locally valid `GeneratedStep` values and individuated
occurrences, but removes the global composability imposed by `History`.

### 4.1 Permuted trace

```text
p2, p1, p3
```

This trace admits an exact and injective local realization while reversing the
first two requirements. Local exactness alone therefore does not determine
order. `NonClosingPrecedes` and `SemanticOrderPreserved` represent that property
separately on the weakened carrier.

### 4.2 Interleaved trace

```text
p1, extra1, p2, extra2, p3
```

This trace preserves local exactness and order, but contains additional
occurrences between the canonical realizations. It shows that an intermediate
position does not determine participation in a constitutive composition.

`SemanticTrace.Between` describes the position. `ExactSemanticBridgeSegment`
additionally requires an exact correspondence with the occurrences of a
`GeneratedHistory` that would actually constitute the bridge. The theorems for
the interleaved example refute the existence of such a bridge between two
canonically adjacent requirements.

```text
intermediate position
≠ participation in constitutive composition
```

Relevant contiguity is therefore not primitive. It can be derived from
constitutive adjacency and the irreflexivity of generation.

### 4.3 Minimization procedure

```text
1. propose a candidate determination
2. weaken the carrier without destroying the notions already established
3. seek a model that preserves the weaker layers
   while violating the candidate property
4. decide whether that violation must be admitted or rejected
5. if the property is necessary, introduce it at the minimal level
6. reintroduce actual composition
7. check whether the property then becomes derivable
8. retain as primitives only determinations that cannot be reconstructed
```

The absence of a countermodel in an already overconstrained construction
language is not sufficient to establish that a property is primitive.

## 5. Structural measure and exact preservation

The term **structural measure** does not refer here to a sigma-additive measure
on an algebra of sets. It denotes the exact determination carried by
occurrences, their correspondences, and their indexings before any numerical
evaluation.

### 5.1 Cardinal determination before calculation

Under the defined faithfulness conditions, `positiveContinuation_exactlyOne`
proves that a positive continuation contains exactly one occurrence. The proof
first establishes existence and uniqueness; the numerical value `1` may then be
read as an invariant.

```text
relational structure
→ existence and uniqueness
→ cardinal invariant
→ numerical reading 1
```

Composition is structural as well. `History.append` joins histories while
distinguishing the occurrences contributed by each.

### 5.2 Preservation in concrete realizations

For every supplied `ConcreteContinuationAlgebra P`, `exactlyInterpretHistory`
constructs two inverse correspondences between occurrences of the free history
and those of its concrete realization. The round trips recover the original
occurrences exactly.

```text
free occurrences ⇄ concrete occurrences
```

`ConcreteOccurrenceAgreement` also relates each occurrence to the sources,
targets, and steps it interprets. Within the interface under consideration,
this rules out the loss, merging, or addition of an occurrence without a
counterpart.

Preservation is therefore richer than an equality of cardinalities. It concerns
an equivalence of occurrences accompanied by the specified structural
agreements.

It follows that two concrete realizations supplied for the same history preserve
the same occurrence determination, since each is related exactly to the common
free history. This sentence is a derived consequence of the two exact
interpretations, not the name of an additional binary theorem.

```text
preserved occurrence structure
⇒ structural and quantitative invariants
⇒ numerical readings
```

### 5.3 Numerical readings as consequences

A classification need not precede every quantitative determination.
`positiveContinuation_exactlyOne` directly provides a cardinal determination
from relational structure. In the perimetral application,
`samePerimeter_length_eq` establishes:

```text
CircularRefinement P history
→ history.history.length
  = (perimeterDeployment P).history.length
```

`History.length_append` proves additivity of length under concatenation. The
numerical equality is derived from structural classification, not the reverse.
Totality is therefore not defined by additivity: numerical readings follow an
already constituted and preserved structure.

### 5.4 Persistence before readout

The old/fresh occurrence split now extends to every positively supplied finite
depth. Exact realization transport and finite constitutive extension are both
derived from the same index, and their pointwise commuting square is proved on
the actual Cycle 1 histories. Consequently, a readout assembled afterward by
finite extension retains a distinction from the depth at which its identities
were constituted.
The theorem is polymorphic in the finite depth, realizations, and value type;
the executable three-step example establishes only its demonstrated scope.

## 6. Cycle 1 — Relative alignment and operational exit

The circular application connects the three modules:

- [`SegmentedResidualRole.lean`](../../SegmentedResidualRole.lean) isolates the
  dependencies consumed by the abstract residual-occurrence derivation and
  characterizes exact reconstruction;
- [`SegmentedResidualRoleStrictness.lean`](../../SegmentedResidualRoleStrictness.lean)
  gives a positive separator for the strict weakening;
- [`AbstractSegmentedTurning.lean`](../../AbstractSegmentedTurning.lean) connects it
  to regime classification and exit;
- [`StrongPerimetralTurning.lean`](../../StrongPerimetralTurning.lean) constructs the
  histories, perimeter, interpretations, and alignment instance.

The complete rich contract projects to a strictly weaker residual kernel in the
general class: the separator kernel has a positive unique residual occurrence
although its old occurrences admit no exact internal realization.  For a fixed
kernel, a compatible exact completion is constructively recoverable exactly
from internal labels for every old occurrence together with injectivity of the
old embedding.  Positivity supplies the internal-label condition.  In the
actual `StrongPerimetralTurning` producer, the old embedding is injective and
the reconstructed maps agree pointwise with `requirementToOccurrence` and
`occurrenceToRequirement`.

It distinguishes compatibility of a junction, identification of the endpoints,
and the continuation actually produced. In the four-node example, the junction
from the fourth node to the first is compatible, but the generated step produces
a constitution beyond the perimeter.

### 6.1 Independent norm and regime

For a history `H`:

```text
F_A(H) := ExactConcreteRealization A H
S(H)   := CircularSpecificationSatisfaction P H
R(H)   := CircularRefinement P H
```

The norm is a two-field structure:

```text
CircularSpecificationSatisfaction P H
  ├─ local : ExactNonClosingRealization P H
  └─ trajectory :
       StrictConstitutivePrefix (perimeterDeployment P) H
       → P.TotalLoop
```

The formal proof establishes:

```text
R(H) → S(H)                         soundness
S(H) → H = perimeterDeployment P    carrier completeness
S(H) → R(H)                         regime completeness
```

The regime and the norm classify exactly the same histories without identifying
their witness structures.

### 6.2 Canonical contrast

| Property | `perimeterDeployment P` | `oneStepAfterPerimeter P` |
|---|---:|---:|
| exact local realization | ✓ | ✓ |
| correct precedence | ✓ | ✓ |
| correct constitutive adjacency | ✓ | ✓ |
| exact concrete realization for every supplied algebra | ✓ | ✓ |
| `CircularSpecificationSatisfaction` | ✓ | ✗ |
| `CircularRefinement` | ✓ | ✗ |

`oneStepAfterPerimeter P` is the canonical witness of departure from the norm.
It remains constructible and, like every rooted generated history, admits an
exact concrete realization in every supplied algebra. The departure is located
precisely at the trajectory obligation and is derived relative to the explicit
`rejectInitialContraction` field of the supplied `CircularPresentation`.

```text
capacity to continue
≠ normative admission

local faithfulness
≠ global trajectory alignment
```

### 6.3 Typed exit and adequacy

`RegimeExit` is polymorphic over an arbitrary carrier. It combines:

```text
candidate
faithful : Faithful candidate
inadmissible : Regime candidate → False
```

`UniformRegimeExit` fixes the candidate before implementations vary and requires
its faithfulness in every supplied implementation.
`oneStepUniformPerimetralRegimeExit` provides the canonical circular instance.

The normative interface is instantiated on `RootedGeneratedHistory P` for
`P : CircularPresentation`, while `NormativeAdequacy`, `AdequateAlong`, and
`SpecRelativeHistoryExit` are parametric in the norm and the regime.

In the `circularNormativeAdequacy` instance, adequacy is global and constant
over the occurrence index:

```text
RegimeAdequateAtOccurrence S R H o
  =
(R H → S H) × (S H → R H)
```

`oneStepSpecRelativeHistoryExit` composes faithful realization, rejection by the
regime, and adequacy. Normative refutation remains separately proved by
`oneStepSpecRelativeHistoryExit_notSpecification`.

### 6.4 Structural OOD and generalization

Within this framework, generalization leads to a distinction between:

```text
constitutive extension
transport between realizations
regime preservation or change
```

An extension prolongs a construction. A transport changes its concrete
interpretation while preserving the occurrences and agreements guaranteed by
the interface. Regime preservation separately asks whether the construction
retains its admission status.

These operations separate three possibilities:

- a construction may continue exactly without retaining its status;
- the same structure may change realization while preserving its guaranteed
  determinations;
- a regime exit may be localized without removing the already established
  witnesses of faithfulness.

### 6.5 Structural definition

At documentation level, structural OOD is defined by:

```text
OOD_struct(P,R,x) :=
  Constructible_P(x)
  ∧ ¬ Admissible_R(x)
```

It distinguishes:

```text
1. constructible and admitted
2. constructible but outside the regime
3. not constructible in the presentation under consideration
```

The second situation is structural OOD relative to the regime: a determined,
constructible candidate whose admission status has changed.

The circular application provides a witness of the corresponding schema:
`oneStepAfterPerimeter P` exists, is a strict constitutive extension of the
perimetral deployment, and remains exactly interpretable in every
`ConcreteContinuationAlgebra P`, while `CircularRefinement P` is refuted for
this candidate. This is the precise point at which the diagonal architectural
motif is realized: the construction produces its own regime-exit witness.

```text
regime exit
  structural diagnosis

failure of an independent specification
+ rejection by a regime adequate to that specification
  relative-alignment diagnosis
```

Structural OOD records the regime exit; relative misalignment additionally
records failure of the independent norm. In the circular instance, both facts
are established directly.

### 6.6 Interpretive consequence

Within this framework, generalizing means preserving the determinations that
remain while localizing the status changes produced by extension. This is the
architectural reading of the verified constructions.

## 7. Cycle 2 — Reflective alignment and diagonal non-closure

Cycle 2 extends the established Cycle 1 adequacy to proposition-valued statuses,
then studies their exact representation within an evaluator and constructs its
diagonal boundary.

The original Cycle 1 families remain proof-relevant types. Cycle 2 observes only
their inhabitability:

```text
CircularRegimeStatus P H
  := Nonempty (CircularRefinement P H)

CircularSpecificationStatus P H
  := Nonempty (CircularSpecificationSatisfaction P H)
```

The two Cycle 1 maps yield the genuine proposition-level equivalence
`circularStatusAdequacy`. A decoder pulls these statuses back to predicates on
codes, and `transportRepresentation` preserves exact representation across
their pointwise logical equivalence.

Independently, `Cycle2.DiagonalizationKernel` defines, for every evaluator
`eval : Code → Code → Prop`:

```text
diagonalStatus eval code := ¬ eval code code
```

`diagonalStatus_notRepresentable` proves constructively that no evaluator row
represents this status exactly; `noGlobalReflectiveClosure` refutes the claim
that every predicate on the code space is internally representable.

The bridge theorem `exactCircularStatusRepresentation_hasDiagonalOutside`
packages the exact coexistence:

```text
the selected regime status is represented exactly
the propositionally equivalent normative status is represented exactly
the evaluator's diagonal status is not internally representable
```

This is the central result of reflective alignment: determined exactness is
preserved through the adequacy transport, while global representational closure
is constructively refuted.

### 7.1 Distinct operational and representational exits

| Level | Candidate | Classified by | Certified loss |
|---|---|---|---|
| operational | `oneStepAfterPerimeter P` | `CircularRefinement P` and the independent norm | admission and normative satisfaction |
| representational | `diagonalStatus eval` | `InternallyRepresentable eval` | exact internal representation |

The first candidate is a history; the second is a predicate on codes. No theorem
converts either exit into the other. Their connection is architectural: each
localizes a boundary without erasing the positive structure established before
that boundary.

## 8. Architectural consequence — beyond global closure

> **The ambition of global closure is not merely encountered as a limit. It is
> architecturally superseded by a framework in which non-closure is
> constitutive, boundaries are determined locally and relatively, and
> construction continues beyond them.**

Cycle 1 separates continued construction and faithful realization from normative
admission. Cycle 2 combines exact representation of the particular aligned
statuses with a constructed boundary of global representability. Together they
replace an undifferentiated demand for closure with explicit objects, regimes,
adequacy maps, preserved witnesses, and localized exits.

## 9. Formal interfaces and distinctions

The document uses four statement statuses throughout:

| Status | Meaning |
|---|---|
| **Verified in Lean** | definition, construction, or named theorem in either formal cycle |
| **Derived consequence** | explicit composition of already verified Lean results |
| **Architectural interpretation** | theoretical synthesis grounded in the verified chain |
| **Documentary concept** | terminology defined at documentation level, including structural OOD |

`circularNormativeAdequacy` defines exact relative adequacy as a pair of maps
between witness types, and `circularRefinement_adequateAlong` supplies those maps
from soundness and completeness. Cycle 2 then observes their inhabitability by
`Nonempty`, producing the proposition-level `↔` used for representation
transport.

Structural OOD names the core status change of an internally constructible
candidate relative to a regime. `RegimeExit`, `UniformRegimeExit`, and
`SpecRelativeHistoryExit` successively retain faithfulness, implementation
uniformity, and normative adequacy around that core.

The operational and representational exits remain distinct formal objects. Their
architectural unity lies in the same discipline: preserve exact positive
information and localize the boundary at which a specified status changes.

## 10. Map of the main Lean results

| Role | Declaration |
|---|---|
| exact agreement between role and occurrence | `RequirementOccurrenceAgreement` |
| exact local realization | `ExactNonClosingRealization` |
| derived precedence | `ExactNonClosingRealization.preservesPrecedence` |
| derived adjacency | `ExactNonClosingRealization.preservesNext` |
| unique residual occurrence | `positiveExtension_hasUniqueResidualOccurrence` |
| one-occurrence continuation | `positiveContinuation_exactlyOne` |
| exact concrete interpretation | `exactlyInterpretHistory` |
| exact regime classification | `ExactRegimeClassification` |
| typed exit | `RegimeExit` |
| uniform exit | `UniformRegimeExit` |
| independent norm | `CircularSpecificationSatisfaction` |
| soundness | `circularRefinement_soundSpecification` |
| carrier completeness | `CircularSpecificationSatisfaction.eq_perimeter` |
| regime completeness | `circularSpecification_complete` |
| normative adequacy | `circularNormativeAdequacy` |
| relative diagnosis | `oneStepSpecRelativeHistoryExit` |
| derived length equality | `samePerimeter_length_eq` |
| proposition-level Cycle 1 adequacy | `circularStatusAdequacy` |
| pullback of a status to codes | `PullbackStatus` |
| representation transport | `transportRepresentation` |
| diagonal status | `diagonalStatus` |
| diagonal non-representability | `diagonalStatus_notRepresentable` |
| global reflective non-closure | `noGlobalReflectiveClosure` |
| exact aligned statuses with a diagonal exterior | `exactCircularStatusRepresentation_hasDiagonalOutside` |

The Cycle 1 library is assembled from the Lean roots listed in
`lakefile.toml`. The independent diagonal kernel is in
`Cycle2/DiagonalizationKernel.lean`; the bridge from Cycle 1 adequacy is
confined to `Cycle2/ReflectiveAlignment.lean`.

## 11. General conclusion

Cycle 1 realizes a precise chain of dependence:

```text
preserved individuation
→ structural roles and agreements
→ succession and composition
→ histories and trajectories
→ invariants
→ numerical readings
```

This architecture then makes it possible to distinguish formally:

```text
construction
faithful realization
admission by a regime
satisfaction of an independent norm
adequacy of the regime to that norm
```

The result preserves the witnesses of what remains determined and localizes
exactly the property whose preservation becomes impossible when a candidate's
status changes.

> **The complete contribution is an architecture of preservation and localized
> exit: preserve occurrences and constitutive relations across realizations;
> prove exact adequacy between regime and autonomous norm; retain the positive
> witnesses carried beyond an operational boundary; then transport the
> proposition-level adequacy into a reflective layer where exact determined
> representation coexists with a constructed failure of global closure.**

Cycle 1 is mathematically closed relative to `CircularPresentation`. Cycle 2 is
stabilized as a self-contained constructive reflective extension. Their
articulation is the architecture of the repository.

## 12. Documentation and authorship

Companion documents:

- [Cycle 1 — relative alignment](relative_alignment.md);
- [method of relational constitutive roles](relational_constitutive_roles_method.md);
- [Cycle 2 — reflective alignment](reflective_alignment.md);
- [French structural synthesis](../fr/fondements_structurels.md).

The project owner is the source of the project's essential ideas and research
direction. This document was written from start to finish by models in OpenAI's
ChatGPT model series, under human direction and through successive interactions.
See the [full bilingual declaration](../../AI_AUTHORSHIP.md).
