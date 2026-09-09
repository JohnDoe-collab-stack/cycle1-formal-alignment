# Cycle 1 — Structural foundations

*From relational constitution to relative alignment*

**English** | [Français](../fr/fondements_structurels.md)

> **AI-generation disclosure.** The project owner declares that this document
> was written from start to finish by models in OpenAI's ChatGPT model series,
> under human direction and through successive interactions. See the
> [full bilingual declaration](../../AI_AUTHORSHIP.md).

> **This document presents the conceptual framework that makes the cycle 1
> formal proof of relative alignment possible.** Its guiding principle is to
> preserve the finest-grained individuation and the relations that constitute
> it, and then to project, classify, quotient, or measure only after proving
> that the forgotten information is not required for the determination at hand.

The complete proof of soundness, carrier completeness, and regime completeness
is presented separately:

- [formal proof — English](formal_relative_alignment_proof.md);
- [preuve formelle — français](../fr/preuve_formelle_alignement_relatif.md).

## Status of statements

This document distinguishes three statuses so as not to conflate proof and
interpretation:

| Status | Meaning |
|---|---|
| **Verified in Lean** | definition, construction, or named theorem in the cycle 1 modules |
| **Derived consequence** | explicit composition of already verified Lean results |
| **Conceptual proposal** | vocabulary or theoretical reading introduced by the documentation |

The four distinctions are structural principles realized and controlled in the
perimetral application. They are not claimed as four independent universal
theorems. The notion of structural OOD introduced below is a conceptual
proposal; it is not yet a Lean definition.

## 1. The four distinctions

### 1.1 Individuation definitionally precedes identity

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

### 1.2 Totality is local and is not globality

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

### 1.3 Succession is indexed by a total locality

In the perimetral realization, generated steps depend on the presentation and
the source constitution. No external clock is required to define their
succession.

### 1.4 Time and the global are derived from the trajectory

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

## 2. The method of relational constitutive roles

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

### 2.1 Realizing a role exactly

A locality provides roles or requirements to be realized. Realizing a role is
not merely a matter of assigning a label. A structural agreement must be
established between the effectively constituted occurrence and the required
role.

In the perimetral application, `RequirementOccurrenceAgreement` imposes exact
equality between the `LocatedStep` of an occurrence and the canonical step
corresponding to a `NonClosingPosition`.

```text
required role
+ individuated occurrence
+ exact structural agreement
```

Agreements on source, target, compatibility, and provenance are then derived
from this finer agreement.

### 2.2 Exact coverage without exhaustiveness

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

### 2.3 Order and adjacency derived in the actual history

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

## 3. Minimizing primitives with separating models

The method does not consist in accumulating primitives, but in determining
which ones are genuinely independent. The development uses weakened carriers
and separating models for this purpose.

`SemanticTrace` retains locally valid `GeneratedStep` values and individuated
occurrences, but removes the global composability imposed by `History`.

### 3.1 Permuted trace

```text
p2, p1, p3
```

This trace admits an exact and injective local realization while reversing the
first two requirements. Local exactness alone therefore does not determine
order. `NonClosingPrecedes` and `SemanticOrderPreserved` represent that property
separately on the weakened carrier.

### 3.2 Interleaved trace

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

### 3.3 Minimization procedure

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

## 4. Relational constitutive roles

A **relational constitutive role** is the role of an occurrence determined by
the structural relations in which it participates within a constitution.

The term *constitutive* indicates that the role is not an external
classification added afterward. The term *relational* indicates that it cannot
be reduced to an isolated property of the occurrence.

An occurrence may be determined simultaneously by:

```text
its formation
its provenance
its source and target
its place in a succession
its role relative to a locality
its participation in a composition
```

without allowing a reading to redefine its individuation retrospectively.

The stabilized methodological principle is:

> **Preserve the finest-grained individuation and the relations that constitute
> it, and then project, classify, quotient, or measure only after proving that
> the forgotten information is not required for the determination at hand.**

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

## 6. Circular application and relative alignment

The circular application connects the three modules:

- [`SegmentedResidualRole.lean`](../../SegmentedResidualRole.lean) establishes the
  abstract result on residual occurrences;
- [`AbstractSegmentedTurning.lean`](../../AbstractSegmentedTurning.lean) connects it
  to regime classification and exit;
- [`StrongPerimetralTurning.lean`](../../StrongPerimetralTurning.lean) constructs the
  histories, perimeter, interpretations, and alignment instance.

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

`oneStepAfterPerimeter P` is a canonical counterexample, not a model of the
norm. It remains constructible and faithfully realizable, but fails precisely
on the trajectory obligation.

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

The normative interface has a different level of generality.
`NormativeAdequacy`, `AdequateAlong`, and `SpecRelativeHistoryExit` are
parametric in the norm and the regime, but their current carrier remains
specialized to `RootedGeneratedHistory P` for `P : CircularPresentation`.

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

The detailed proof of these results is not repeated here; it appears in the two
versions of the formal document linked at the beginning.

## 7. Generalization and structural OOD

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

These operations are not equivalent:

- a construction may continue exactly without retaining its status;
- the same structure may change realization while preserving its guaranteed
  determinations;
- a regime exit may be localized without removing the already established
  witnesses of faithfulness.

### 7.1 Proposed documentary definition

The following notation introduces a conceptual reading; it is not a Lean
declaration of cycle 1:

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

The second situation is structural OOD relative to the regime. It is neither a
construction error nor an absence of determination.

The circular application provides a witness of the corresponding schema:
`oneStepAfterPerimeter P` exists, is a strict constitutive extension of the
perimetral deployment, and remains exactly interpretable in every supplied
concrete algebra, while `CircularRefinement P` is refuted for this candidate.

```text
regime exit
  structural diagnosis

failure of an independent specification
+ rejection by a regime adequate to that specification
  relative-alignment diagnosis
```

Structural OOD and relative misalignment are therefore not identified. In the
circular instance, failure of the norm is proved directly and is not inferred
from rejection by the regime alone.

### 7.2 Interpretive consequence

Within this framework, generalizing does not mean erasing changes of status. It
means preserving the determinations that remain and localizing those that can no
longer be maintained. This formulation is a theoretical reading of the verified
constructions, not a universal theorem about OOD in learning systems.

## 8. Numerical reading as a consequence

A classification need not precede every quantitative determination.
`positiveContinuation_exactlyOne` directly provides a cardinal determination
from the relational structure.

```text
constituted and preserved structure
⇒ invariants
⇒ numerical readings
```

In the perimetral application, `samePerimeter_length_eq` establishes:

```text
CircularRefinement P history
→ history.history.length
  = (perimeterDeployment P).history.length
```

`History.length_append` proves additivity of length under concatenation. The
numerical equality of lengths is deduced from structural classification, not the
other way around.

Totality is therefore not defined by additivity. The numerical law belongs to
the reading and composition under consideration; it does not retrospectively
determine the status of the whole.

## 9. Map of the main Lean results

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

## 10. Stabilized conclusion

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

The result is not merely that a candidate is accepted or rejected. It preserves
the witnesses of what remains determined and localizes exactly the property
whose preservation becomes impossible.

> **The structural contribution of cycle 1 is a method of preservation and
> diagnosis: preserve occurrences and their relations across realizations,
> derive invariants before their numerical readings, and then distinguish the
> continuation of a construction from preservation of its normative status.**

The first mathematical cycle is closed. What follows belongs to documentation,
translation, audit, and versioning, without modifying the stabilized Lean
definitions.
