# Method of relational constitutive roles

*Individuation, primitive minimization, faithful transport, and normative diagnosis*

**English** | [Français](../fr/methode_roles_constitutifs_relationnels.md)

Navigation: [structural synthesis](structural_foundations.md) ·
[Cycle 1 — relative alignment](relative_alignment.md) ·
[Cycle 2 — reflective alignment](reflective_alignment.md)

> **This document presents the method extracted from cycle 1: individuate
> occurrences before their readings, determine their roles through the
> relations that constitute them, test the independence of properties on
> weakened carriers, and then reconstruct and transport only those
> determinations whose preservation has been proved.** Applied to relative
> alignment, this method localizes a normative break in a construction that
> continues to exist and to remain faithfully realizable.

Complementary documents:

- [formal proof of relative alignment — English](relative_alignment.md);
- [preuve formelle d'alignement relatif — français](../fr/alignement_relatif.md);
- [structural foundations — English](structural_foundations.md);
- [fondements structurels — français](../fr/fondements_structurels.md);
- [reflective alignment — English](reflective_alignment.md);
- [alignement réflexif — français](../fr/alignement_reflexif.md).

## Abstract

A formalization loses its diagnostic power when it identifies an occurrence
too early with its reading, a position with a participation, coverage with
exhaustiveness, or a possible construction with an admissible construction. The
method of relational constitutive roles organizes the design of a formalism so
as to prevent these collapses.

It begins with dependently typed occurrences, constituted by a formation and
embedded in relations of provenance, source, target, succession, and
composition. It then expresses the realization of a requirement by an exact and
injective structural agreement. To determine which properties must be
primitive, it deliberately weakens the carrier and constructs separating
models: a permuted trace preserves local exactness without preserving order; an
interleaved trace preserves exactness and order without guaranteeing
participation in a constitutive composition. When the actual composability of
histories is reintroduced, precedence and adjacency become derivable.

The same discipline governs changes of representation. A faithful concrete
realization is not merely an evaluation function: it provides inverse
correspondences between occurrences together with agreements on their steps,
sources, and targets. Cardinal and numerical invariants are then read as
consequences of this structural preservation.

Finally, the method separates construction, realization, regime, and norm. A
norm is defined independently of the regime intended to implement it; their
adequacy is proved in both directions; and a typed exit preserves the candidate
and its positive witnesses of faithfulness while carrying the refutation of its
admission. In the circular application, `oneStepAfterPerimeter` is exactly such
a witness: a strict continuation, an exact local realization, an exact concrete
realization for every supplied algebra, yet rejected by the regime and directly
failing the norm.

The methodological contribution is therefore not a new label for a particular
proof. It is a procedure for design and audit:

```text
individuate
→ relate
→ separate
→ reconstruct
→ transport
→ diagnose
```

## Document architecture

The argument is organized into five complementary parts:

| Part | Sections | Function |
|---|---:|---|
| **Foundations** | 1–6 | delimit the method, its statuses, its vocabulary, and exact agreement between role and occurrence |
| **Separation and reconstruction** | 7–10 | test dependencies on weakened carriers, then reconstruct order, adjacency, and participation |
| **Preservation** | 11–12 | define faithful transport and derive structural and numerical invariants |
| **Normative diagnosis** | 13–14 | separate norm and regime, prove their adequacy, and summarize the canonical witness |
| **Reuse and audit** | 15–20 | provide a protocol, failure criteria, explicit scope, and Lean anchors |

Sections 1 through 14 reconstruct the argument. Sections 15 through 19 turn
that argument into a reusable and auditable procedure. The conclusion condenses
its guiding principle.

## 1. Object of the method

The method answers the following question:

> How can one formally determine what constitutes an occurrence, what a
> realization must preserve of it, which properties are primitive or derived,
> and where a construction ceases to satisfy a norm without ceasing to be
> constructible?

It targets situations in which several levels risk being conflated: the
constructed object, its representation, its evaluation, and its normative
status. These levels may coincide in one example without being identical. A
rigorous method must keep them distinct long enough to make their relationships
provable.

Cycle 1 provides a complete instance of this approach. It contains:

- a language of free constructions;
- individuated occurrences in histories;
- exactly realized perimetral requirements;
- weakened carriers used to test the independence of certain properties;
- concrete interpretations that preserve occurrences;
- an operational regime;
- an autonomous norm;
- soundness and completeness theorems;
- a minimal exit that preserves faithfulness while losing normative status.

The method is not limited to the vocabulary of circularity. Its complete
application, however, is currently verified in Lean only for the structures of
cycle 1. Moving from a formal instance to a reusable method therefore requires a
careful distinction between proof, methodological extraction, and proposed
generalization.

## 2. Status of statements

Four statuses are used in this document.

| Status | Meaning | Example |
|---|---|---|
| **Verified in Lean** | definition, construction, or theorem present in the cycle 1 modules | `ExactNonClosingRealization.preservesNext` |
| **Derived consequence** | explicit composition of verified Lean results | two exact realizations of the same history preserve the same occurrence structure through their common free history |
| **Methodological extraction** | design rule justified by the organization of definitions, proofs, and separating models | weaken the carrier to test whether a property is primitive |
| **Proposed generalization** | principle intended for other domains but not yet proved as a universal metatheorem | use the method for every alignment architecture |

Transitions between these levels must never remain implicit. A theorem about
`RootedGeneratedHistory P` does not become, by reformulation alone, a theorem
about every dynamic system. Conversely, the fact that a methodological
principle is not a universal theorem does not erase its content: its
justification may rest on a verified instance, effective countermodels, and an
exact reconstruction of dependencies.

The document therefore follows this convention:

```text
named Lean declaration
  → verified formal fact

indicated composition of Lean declarations
  → derived consequence

design rule extracted from that organization
  → methodological proposal

extension to another domain or more general carrier
  → generalization program
```

This convention makes it possible to state the method strongly without
attributing to the Lean kernel a scope it does not yet have.

## 3. Structural vocabulary

The method rests on a vocabulary whose levels must remain distinct.

### 3.1 Presentation

A presentation fixes the types and rules from which constructions may be
formed. In the cycle 1 application, `CircularPresentation` provides, among other
things, the explicit and implicit types, compatibilities, differences,
provenances, perimeter, and obstruction to a total loop.

The presentation does not yet classify every history as admitted or rejected.
It supplies the conditions of their constitution.

### 3.2 Constitution and formation

A constitution is an object whose construction records the data that formed it.
`FreeConstitution` does not represent only a value reached: it preserves the
structure required to recover formation, provenance, and the transported
obstruction.

Formation answers the question:

```text
by which typed act was this object constituted?
```

It precedes the external readings that may subsequently be applied to it.

### 3.3 Step and occurrence

A `GeneratedStep` connects a source and a target according to the rules of the
presentation. An occurrence is an individuated appearance of such a step in a
`History`.

The distinction is essential: two occurrences may carry steps whose readings
coincide while remaining different positions in the history.
`History.Occurrence` preserves that individuation.

### 3.4 Relational constitutive role

A **relational constitutive role** is the determination of an occurrence by the
structural relations in which it participates within a constitution.

The term *constitutive* means that these relations contribute to determining
what the occurrence is in the construction under study. The term *relational*
means that the role cannot be reduced to an isolated property or a label carried
by the occurrence.

Schematically:

```text
Role(P, H, r, o)
```

where:

- `P` is the presentation;
- `H` is the constituted history;
- `r` is the expected requirement or structural position;
- `o` is the occurrence realizing that role.

The role may depend simultaneously on:

```text
formation(o)
provenance(o)
source(o)
target(o)
position(o, H)
succession(o, H)
participation(o, composition)
agreement(o, r)
```

This notation is a methodological presentation, not a new Lean declaration. In
cycle 1, its content is realized by several types and relations rather than by a
single structure named `Role`.

### 3.5 Carrier

The carrier is the type of objects over which a property is studied. Changing
the carrier changes the available relations and therefore what can be proved.

A `SemanticTrace` and a `RootedGeneratedHistory` may carry similar steps, but
only the latter imposes the global composability of a generated history. The
choice of carrier is therefore not a representational detail: it is part of the
hypotheses of the argument.

## 4. The collapses the method must prevent

The methodological need appears when an abstraction that is correct for one
task becomes destructive for another. Four collapses are especially important.

### 4.1 Reading and occurrence

A reading assigns a value to an occurrence:

```text
ρ : Occurrence → Value
```

The equality `ρ(x) = ρ(y)` is not sufficient to conclude `x = y`. The two
occurrences may differ through their formation, provenance, position, or role
in a composition. Identifying them through their reading would destroy exactly
the data needed to audit their trajectory.

The problem is not the use of a reading. It is its retrospective use as a
principle of individuation. A reading may be relevant after the occurrence has
been constructed; it must not replace without proof the relations that
constituted that occurrence.

### 4.2 Position and participation

An occurrence may be situated between two others in a list without
participating in a generated history that connects their states. An order
relation gives positional information; constitutive participation requires a
correspondence with the occurrences of an effectively typed composition.

```text
intermediate position
≠ occurrence of a constitutive bridge
```

Conflating these notions would allow any interleaved datum to be treated as part
of the construction connecting its neighbors, even when its sources, targets,
or generation mode are incompatible with that composition.

### 4.3 Coverage and exhaustiveness

Exactly realizing all requirements of a locality does not mean that the history
contains nothing else.

```text
every requirement has an exact witness
≠
every occurrence is the witness of a requirement
```

The first proposition is coverage. The second is an exhaustive classification.
Identifying them would exclude by definition every continuation beyond the
covered domain and make the phenomenon under diagnosis disappear.

### 4.4 Constructibility and admissibility

A generator may produce a step that the regime rejects. This situation is
neither contradictory nor incomplete if construction and regime have been
defined separately.

```text
Constructible(x)
≠ Admissible(x)
```

Collapsing the two notions turns every regime exit either into an inability to
construct or into an unlocalized error. Separating them instead preserves the
produced object, the properties it still satisfies, and the proof of the exact
property it no longer satisfies.

## 5. Order of dependence

The method imposes an order of construction intended to make every dependency
auditable.

```text
presentation
→ possible formations
→ individuated occurrences
→ agreements between requirements and occurrences
→ succession and composition
→ internal structural invariants
→ concrete realizations and preservation proofs
→ derived numerical readings
→ independently defined norms and operational regimes
→ adequacy proofs
→ diagnoses
```

This order does not claim that every theory must use exactly the types of cycle
1. It states a discipline: do not silently use a later layer to define an
earlier one.

### 5.1 Individuation before reading

A reading presupposes an already constituted domain of occurrences. If it is
used to define that domain, equality of readings merges by construction the
occurrences that the analysis might have needed to distinguish.

### 5.2 Composition before global time

In cycle 1, precedence comes from prefix structure and globality from the
composition of histories. No external clock is required to create the order of
steps after the fact.

### 5.3 Faithfulness before numerical invariants

An equality of cardinalities may conceal a permutation, a merge followed by an
addition, or a compensated loss. Equivalence of occurrences and structural
agreements must be established before their cardinality is read as a meaningful
invariant.

### 5.4 Norm before regime adequacy

If the norm is defined as “what the regime accepts,” soundness becomes
tautological and completeness loses its critical function. The autonomy of the
norm is a condition for a diagnosis of relative alignment.

## 6. Realizing a role exactly

The realization of a role must specify what is preserved between a requirement
and an occurrence.

### 6.1 Three levels of agreement

One may distinguish:

```text
1. label agreement
2. partial agreement on selected projections
3. exact structural agreement
```

A label agreement merely states that an occurrence has received the name of the
role. A partial agreement compares, for example, its source or value. An exact
agreement concerns structural data fine enough for the useful agreements to be
derived from it.

In the perimetral application, `RequirementOccurrenceAgreement` requires:

```lean
occurrence.locatedStep.source.1 =
  (perimeterPositionSource P position).1
```

The primitive equality concerns the exact source cursor. Rooted deterministic
generation and cursor acyclicity reconstruct the source state and complete
`LocatedStep`; agreements on target, compatibility, and provenance then follow.
This is not a strict weakening of the former complete-step formulation: each
form reconstructs the other on rooted generated histories. The method thus
stores the smallest structural address currently justified by the productive
class, while retaining the complete agreement as a derived theorem.

### 6.2 Exact coverage with derived injectivity

`ExactNonClosingRealization P history` contains:

```text
realize
  : NonClosingPosition P.perimeter
  → History.Occurrence history.history

agreement
  : every position agrees exactly with its occurrence
```

The two fields have different functions:

- `realize` provides a witness for every requirement;
- `agreement` establishes that the witnesses are not arbitrary.

Injectivity is not an independent hypothesis. The theorem
`ExactNonClosingRealization.realize_injective` derives it from `agreement`:
two requirements realized by the same occurrence would have equal canonical
located steps, contradicting the strict cursor order between distinct canonical
occurrences. Thus exact agreement already prevents several requirements from
being absorbed by one occurrence. Omitting agreement would remove both the
structural content and this derivation of injectivity. Omitting the realization
function would reduce the statement to a global property without accessible
witnesses.

### 6.3 Why exactness does not imply exhaustiveness

The structure contains no inverse function classifying every occurrence as a
non-closing requirement. This omission is intentional.

```text
requirements → occurrences
```

is not replaced by:

```text
requirements ⇄ all occurrences of the history
```

A history may therefore contain the expected exact realizations and an
additional continuation. This openness is required to formulate the candidate
`oneStepAfterPerimeter` without denying the correct realization of the perimeter
that it contains.

## 7. Minimizing primitives

A robust formalization must distinguish genuinely independent properties from
properties that are merely difficult to prove in the current presentation.

Here the method proceeds by formal experimentation: it changes the assumptions,
constructs separating models, and observes which properties survive.

### 7.1 Propose a candidate determination

One starts with a property whose status is uncertain:

- order of occurrences;
- adjacency;
- contiguity;
- participation in a composition;
- exhaustiveness;
- preservation under interpretation.

The question is not only “can it be proved?” but:

> On exactly which structures does this property depend?

### 7.2 Weaken the carrier

A weakened carrier must remove the structure suspected of producing the
property without destroying the layers already established.

`SemanticTrace` preserves a list of generated `LocatedStep` values and
individuates occurrences by their indices. It therefore retains:

- the complete local data of steps;
- the distinction between occurrences;
- an exact and injective local realization.

It removes, however, the global composability required by `History`.

### 7.3 Construct a separating model

A separating model satisfies the weaker properties while refuting the candidate
property. Its function is not to simulate the whole system, but to show that a
supposed implication does not follow from the stated assumptions alone.

```text
weak structure W
+ property A verified in W
+ property B refuted in W
→ A is not sufficient to determine B at this level
```

### 7.4 Reintroduce the structure

Once independence has been established on the weak carrier, the actual
construction constraints are reintroduced. Two outcomes are possible:

1. the property remains independent and must be added explicitly;
2. it becomes derivable from the reintroduced structure.

The second case is methodologically important. It avoids adding as primitive a
property already imposed by a more fundamental composability.

### 7.5 Minimality criterion

A primitive is justified when:

- the property is required for the intended use;
- it cannot be reconstructed from the retained primitives;
- a separating model demonstrates its independence at the weaker level;
- adding it does not silently reintroduce a layer that the method seeks to
  analyze separately.

The absence of a countermodel in an already overconstrained language of
construction is not evidence of primitiveness.

## 8. Two separating models

The permuted and interleaved traces of cycle 1 are not merely pedagogical
examples. They play distinct logical roles in the dependency analysis.

### 8.1 Permuted trace: exactness without order

The trace:

```text
p2, p1, p3
```

retains the three canonical steps but reverses the first two occurrences.
`permutedExampleRealization` nevertheless supplies an exact and injective local
realization. The theorem `permutedExample_not_order_preserved` refutes
`SemanticOrderPreserved` for this realization.

The resulting separation is:

```text
local exactness
+ injectivity
⇏ structural order
```

It shows that order cannot be extracted from local agreement alone on the
`SemanticTrace` carrier.

### 8.2 Interleaved trace: order without participation

The trace:

```text
p1, extra1, p2, extra2, p3
```

retains the canonical requirements in their order. The result
`interleavedExample_order_preserved` explicitly establishes that preservation.
Additional occurrences are nevertheless placed between the canonical
realizations.

`SemanticTrace.Between` is sufficient to express their position. To express
their participation in a generated composition, `ExactSemanticBridgeSegment`
requires inverse correspondences with the occurrences of a `GeneratedHistory`,
together with exact agreement of located steps. `EffectiveConstitutiveBridge`
assembles that segment into a constitutive bridge with the relevant endpoints.

The theorems:

```lean
interleavedExample_no_effective_bridge_p1_p2
interleavedExample_no_effective_bridge_p2_p3
```

show that the interleaved occurrences do not constitute an effective bridge
between canonically adjacent requirements.

The resulting separation is:

```text
local exactness
+ injectivity
+ preserved order
+ intermediate position
⇏ participation in a constitutive composition
```

### 8.3 What the two models establish together

The two traces form a chain of separation:

```text
exact agreement
  does not impose order on a weak carrier

exact agreement + order
  do not impose constitutive participation

actual composition of a History
  supplies the constraints required for reconstruction
```

The method therefore does not conclude that order or adjacency are always
primitive. It localizes the level at which they are not yet determined, then
seeks the structure from which they can be derived.

## 9. Reconstructing order and adjacency

The transition from `SemanticTrace` to `RootedGeneratedHistory` reintroduces the
dependently typed composability of steps. The target of one step and the source
of the next are no longer merely juxtaposed data: they participate in the
construction of the history itself.

### 9.1 Precedence

In an actually generated history, an exact local realization cannot reverse two
structurally ordered requirements without producing an impossible loop in the
strict future relation of cursors.

The theorem:

```lean
ExactNonClosingRealization.preservesPrecedence
```

transforms a proof of `NonClosingPrecedes` between two requirements into a proof
of `History.OccurrencePrecedes` between their realized occurrences.

```text
exact agreement
+ injectivity
+ history composability
+ irreflexivity of structural future
→ correct precedence
```

Order therefore need not be added as a field of `ExactNonClosingRealization` on
the strong carrier.

### 9.2 Adjacency

Precedence alone does not exclude a positive gap. For canonically adjacent
requirements, however, such a gap would produce, after transport of the exact
endpoints, a strict future from a cursor to itself.

The theorem:

```lean
ExactNonClosingRealization.preservesNext
```

transforms `NonClosingNext` into `History.OccurrenceNext`.

```text
canonical adjacency of requirements
+ exact local realization in a History
→ constitutive adjacency of occurrences
```

### 9.3 Methodological result

The same properties change status with the carrier:

| Property | `SemanticTrace` | `RootedGeneratedHistory` |
|---|---:|---:|
| exact local agreement | expressible | expressible |
| injective individuation | expressible | expressible |
| canonical precedence | additional primitive | derived |
| canonical adjacency | not imposed | derived |
| constitutive composability | absent | constitutive of the carrier |

A primitive is therefore never “primitive in itself.” It is primitive relative
to a language, a carrier, and the determinations already available.

## 10. Constitutive participation and composition

Participation means that an occurrence actually belongs to the construction
connecting two states. It cannot be reduced either to visual proximity in a
sequence or to a numerical comparison of positions.

### 10.1 Why “between” is insufficient

`SemanticTrace.Between trace left right` is a subtype of indices satisfying:

```text
left < occurrence ∧ occurrence < right
```

This relation is exact as a positional relation. By itself, it says nothing
about the existence of a `GeneratedHistory` between the target of `left` and
the source of `right`.

### 10.2 Certifying participation

`ExactSemanticBridgeSegment` requires:

- a map from intermediate occurrences to occurrences of the bridge;
- an inverse map;
- both round-trip laws;
- agreement of the `LocatedStep` values.

This structure separates three questions:

```text
is the occurrence positioned in the interval?
does the occurrence belong to the generated bridge?
is the step it carries exactly the step in the bridge?
```

`EffectiveConstitutiveBridge` adds the typed bridge between the selected
endpoints. Participation then becomes a property of composition rather than a
spatial metaphor.

### 10.3 Design rule

Whenever an analysis uses terms such as *segment*, *chain*, *trajectory*,
*interval*, or *intermediate step*, it must specify whether it means:

1. a position in a representation;
2. an abstract order;
3. participation in an effectively constructed composition.

Moving from one to another requires a proof. This rule extends beyond the
perimetral example: it applies to any formalization in which a sequence of data
may be mistaken for a valid trajectory.

## 11. Faithful transport between realizations

A formal construction may receive several concrete interpretations. The method
must then specify what remains invariant when the representation changes.

### 11.1 An evaluation is not yet a faithful realization

A function:

```text
interpret : FreeObject → ConcreteObject
```

may lose, merge, or invent distinctions. Even if its final value appears
correct, it does not guarantee that occurrences of the free construction can be
audited in the concrete realization.

The faithfulness required by cycle 1 concerns histories and their occurrences,
not only their terminal states.

### 11.2 Structure of an exact interpretation

`ExactHistoryInterpretation A freeHistory concreteHistory` contains:

```text
forwardOccurrence
  : free occurrences → concrete occurrences

backwardOccurrence
  : concrete occurrences → free occurrences

forwardBackward
  : backward after forward = free identity

backwardForward
  : forward after backward = concrete identity

occurrenceAgreement
  : structural agreement for every free occurrence
```

The round-trip laws establish an equivalence of occurrences. Together they rule
out:

- loss of a free occurrence;
- merging of two free occurrences;
- addition of a concrete occurrence without a free counterpart.

### 11.3 Concrete agreement

`ConcreteOccurrenceAgreement` relates a free occurrence to its concrete
occurrence through:

- exact equality of the concrete source with the interpretation of the free
  source;
- exact equality of the concrete target with the interpretation of the free
  target;
- heterogeneous equality of the expected concrete step;
- the `ConcreteStepAgreement` witness supplied by the algebra.

The occurrence equivalence therefore does not float above the steps. It is
accompanied by the agreements that give it structural meaning.

### 11.4 Uniform construction

For every supplied `ConcreteContinuationAlgebra P`,
`exactlyInterpretHistory A history` constructs an exact interpretation of every
`GeneratedHistory`.

The methodological consequence is:

> Implementation independence does not mean that every possible implementation
> is faithful. It means that the same result is obtained for every
> implementation that explicitly satisfies the required faithfulness
> interface.

This quantification is essential. It prevents a conditional proof about an
interface from being turned into an absolute claim about every imaginable
implementation.

### 11.5 Comparing two concrete realizations

If two supplied concrete algebras exactly realize the same free history, each of
their occurrence structures is equivalent to that of the free history. By
composition through that common carrier, they therefore preserve the same
occurrence determination.

This is a derived consequence of two calls to `exactlyInterpretHistory`, not the
name of an additional binary theorem. The distinction illustrates the general
discipline of this document: separate what Lean names directly from what is
obtained by composing verified results.

### 11.6 Adding a readout without reconstructing the object

Once occurrences have been constituted, an occurrence-indexed readout with
values in a type `V` is simply:

```text
History.Occurrence history → V
```

`History.OccurrenceReadout` makes this interface explicit. Its codomain is
arbitrary, but the interface does not automatically construct such a function
and gives it no faithfulness, injectivity, or compatibility property. Whenever
such properties are required, they remain separate obligations.

`perimeterReadout` and `occurrenceReadoutOfPerimeter` reindex a readout along
the exact correspondence between non-closing positions and occurrences of the
deployment. Their two pointwise round-trip laws show that this reindexing loses
no value.

Likewise, `ExactHistoryInterpretation.pullbackReadout` and
`ExactHistoryInterpretation.pushforwardReadout` transport a readout between a
free history and its concrete realization. The occurrence round trips
immediately yield the corresponding pointwise laws for readouts.

The consequence is architectural:

```text
constitution of occurrences
→ exact correspondences
→ open family of readouts
```

Conceptually, occurrences and their exact correspondences form a **structural
bus** onto which independent readouts can be connected after constitution. The
term names the connection architecture already formalized here, not an
additional mathematical primitive.

The readout is added after constitution and does not alter it. An arbitrary
function nevertheless remains only a value assignment; its meaning does not
follow from reindexing alone. Finally, `History.length` is a global readout of
the history, not a direct specialization of a readout indexed by its
occurrences. The two levels must remain distinct.

## 12. Invariants and numerical readings

The method places structural determination before its quantitative reading.

### 12.1 Existence and uniqueness before the number

The abstract theorem
`SegmentedResidualRole.positiveExtension_hasUniqueResidualOccurrence`
establishes that a faithfully segmented positive extension has a unique
residual occurrence.

In the perimetral application, `positiveContinuation_exactlyOne` establishes:

```text
History.ExactlyOne labelled.continuation
```

The number `1` is not posited as primitive data. It is the cardinal reading of a
proof of existence and uniqueness.

```text
faithful segmented structure
→ existence of a residual occurrence
→ uniqueness
→ cardinality 1
```

### 12.2 Composition and length

`History.append` composes two histories while preserving their typed junction.
`History.length_append` then proves:

```text
length (append firstHistory continuation)
  = length firstHistory + length continuation
```

Additivity is a property of this reading of composition. It defines neither the
composition nor the totality of the history.

### 12.3 Classification and equality of length

`samePerimeter_length_eq` derives from `CircularRefinement P history` that:

```text
history.history.length
  = (perimeterDeployment P).history.length
```

The proof goes through the structural classification of the regime, which
reduces the history to the canonical perimetral deployment. Numerical equality
is therefore a consequence of classification; it is not used to define that
classification.

### 12.4 Meaning of “structural measure”

In this document, a structural measure is a determination carried by
occurrences, correspondences, and indexings before its numerical evaluation. It
does not mean a sigma-additive measure on an algebra of sets.

The methodological rule is:

> Before interpreting a number as an invariant, identify the structure of which
> it is a reading and prove that this structure is preserved by the
> transformations under consideration.

## 13. From the structural to the normative

The method becomes a method of relative alignment when it adds an independent
norm and a regime whose adequacy to that norm must be proved.

### 13.1 Four levels to separate

For a history `H` and an algebra `A`:

```text
Construction(H)
F_A(H) := ExactConcreteRealization A H
R(H)   := CircularRefinement P H
S(H)   := CircularSpecificationSatisfaction P H
```

These levels answer four different questions:

| Level | Question |
|---|---|
| construction | can the object be formed? |
| faithful realization | is the object preserved in this implementation? |
| regime | does the operational mechanism admit the object? |
| norm | does the object satisfy the independent specification? |

A normative exit is visible only if these questions have not been identified by
definition.

### 13.2 Defining an autonomous norm

`CircularSpecificationSatisfaction P H` has two fields:

```text
local
  : ExactNonClosingRealization P H

trajectory
  : StrictConstitutivePrefix (perimeterDeployment P) H
    → P.TotalLoop
```

The local field requires exact realization of the non-closing requirements. The
trajectory field gives closure an independent meaning: a strict continuation
of the perimetral deployment would have to determine a total loop.

The definition does not mention `CircularRefinement`. This independence makes
the comparison non-tautological.

### 13.3 Proving adequacy

Three results close the comparison:

```text
R(H) → S(H)
  circularRefinement_soundSpecification

S(H) → H = perimeterDeployment P
  CircularSpecificationSatisfaction.eq_perimeter

S(H) → R(H)
  circularSpecification_complete
```

The first is soundness of the regime relative to the norm. The second classifies
the carrier of the norm. The third uses that classification to transport the
canonical regime witness.

The resulting agreement is extensional: the norm and the regime classify the
same histories. Their witness structures are not identified.

### 13.4 Classifying without conflating witnesses

`ExactRegimeClassification` retains two transformations:

```text
Regime candidate → candidate = canonical
candidate = canonical → Regime candidate
```

This structure does not replace regime witnesses with a Boolean proposition. It
preserves the constructive directions needed for their subsequent use.

### 13.5 Constructing a typed exit

`RegimeExit Faithful Regime` combines on the same carrier:

```text
candidate
faithful     : Faithful candidate
inadmissible : Regime candidate → False
```

An exit is therefore not reducible to `¬ Regime candidate`. It preserves a
positive witness explaining what remains valid about the rejected object.

`UniformRegimeExit` specializes the family of faithfulness witnesses to:

```text
(implementation : Implementation)
→ Faithful implementation candidate
```

The candidate is chosen before the implementation. This structure expresses a
uniformity that would not be supplied by a family of candidates each depending
on its implementation.

### 13.6 Relating the exit to the norm

`NormativeAdequacy` separates the type of specifications from the family of
regimes. In the current interface, its carrier is specialized to
`RootedGeneratedHistory P`. `AdequateAlong` requires an adequacy witness at every
occurrence of the history.

In `circularNormativeAdequacy`, the content of adequacy is global and constant
over that index:

```text
(R H → S H) × (S H → R H)
```

`SpecRelativeHistoryExit` then composes:

- a typed regime exit;
- faithfulness of the same candidate;
- adequacy of the regime to the norm along occurrences of the candidate.

Failure of the norm must nevertheless remain proved. Adequacy and regime
rejection may permit it to be derived in some frameworks, but the method favors
retaining a direct proof when available, so as to localize the exact normative
obligation that fails.

## 14. Condensed study of the canonical witness

The candidate:

```text
h⁺ := oneStepAfterPerimeter P
```

condenses the method on one object. The detailed constructions and signatures
belong to the [Cycle 1 proof](relative_alignment.md); the method retains only
the dependency pattern needed for reuse:

```text
constructed strict continuation
  `oneStepAfterPerimeterStrict`

+ exact local realization and reconstructed order
  `oneStepAfterPerimeter_nonClosingRealization`

+ exact concrete realization in every supplied algebra
  `oneStepUniformPerimetralRegimeExit`

+ exact adequacy between regime and independent norm
  `circularNormativeAdequacy`, `circularRefinement_adequateAlong`

+ operational rejection
  `oneStepAfterPerimeter_notCircularRefinement`

+ direct failure of the trajectory obligation
  `oneStepAfterPerimeter_notSpecificationSatisfaction`

= relative diagnosis retaining both positive and negative evidence
  `oneStepSpecRelativeHistoryExit`
```

The candidate remains constructed, locally exact, correctly ordered, and
faithfully realizable. What is lost is operational admission and the
trajectory-level normative obligation. Preserving this positive information is
what turns a refutation into a structural diagnosis.

## 15. Reuse protocol

The method can be applied to a new domain through the following protocol. Each
phase has a question, an expected output, and a characteristic risk.

### Phase 1 — Delimit the presentation

**Question.** What are the primitive data and formation rules?

**Output.** A presentation type and constructors that do not yet use the final
normative classification.

**Risk.** Encoding the expected regime directly in the construction rules and
making every exit impossible by definition.

### Phase 2 — Individuate occurrences

**Question.** What makes two appearances two distinct occurrences?

**Output.** A type of occurrences indexed by the construction that preserves
position, formation, or provenance according to the needs of the audit.

**Risk.** Quotienting occurrences by an impoverished reading.

### Phase 3 — Define expected roles

**Question.** Which local requirements must the construction realize?

**Output.** A type of roles or structural positions independent of the
occurrences that will realize them.

**Risk.** Defining a role as the label already carried by an occurrence.

### Phase 4 — Define exact agreement

**Question.** Which equality or correspondence guarantees that an occurrence
actually realizes a role?

**Output.** An agreement structure fine enough to derive the relevant
projections.

**Risk.** Accumulating partial agreements without a common kernel, or requiring
an equality stronger than the intended use demands.

### Phase 5 — Separate coverage, injectivity, and exhaustiveness

**Question.** Does every role have a witness? Do two distinct roles have
distinct witnesses? Must every occurrence be classified?

**Output.** Three explicit decisions instead of one ambiguous notion of
“complete realization.”

**Risk.** Excluding continuations by conflating coverage with exhaustiveness.

### Phase 6 — Identify candidate properties

**Question.** Must order, adjacency, participation, or contiguity be primitive?

**Output.** A list of dependencies to test.

**Risk.** Adding every desired property as a field before studying its
relationships to the others.

### Phase 7 — Construct a weakened carrier

**Question.** Which structure can be removed while retaining the notions already
established?

**Output.** An experimental model in which candidate implications become
genuinely testable.

**Risk.** Choosing a carrier that remains too constrained, so that the desired
countermodel is excluded by construction.

### Phase 8 — Produce separating models

**Question.** Can the weaker layers be retained while the candidate property is
violated?

**Output.** A typed countermodel or a proof that the proposed separation is
impossible under the retained assumptions.

**Risk.** Using an example that also destroys an assumption supposedly being
preserved.

### Phase 9 — Reintroduce actual composition

**Question.** Which properties become derivable on the complete carrier?

**Output.** Reconstruction theorems and a minimal list of primitives.

**Risk.** Retaining both a property as primitive and the structure from which it
is already derivable.

### Phase 10 — Define faithful transport

**Question.** Which occurrences and agreements must survive a change of
representation?

**Output.** Forward and backward maps together with structural agreements for
the transported occurrences.

**Risk.** Certifying only the final state or an equality of cardinalities.

### Phase 11 — Extract invariants

**Question.** Which numerical values or classifications are determined by the
preserved structure?

**Output.** Derived invariants accompanied by their structural dependencies.

**Risk.** Using a numerical invariant to redefine the structure retrospectively.

### Phase 12 — Define norm and regime separately

**Question.** Which independent property expresses what must be satisfied, and
which operational mechanism decides admission?

**Output.** Two distinct type families over the same carrier.

**Risk.** Defining the norm through the regime and making adequacy tautological.

### Phase 13 — Prove soundness and completeness

**Question.** Is the regime exact relative to the norm?

**Output.** Transformations in both directions, possibly accompanied by a
classification of the canonical carrier.

**Risk.** Conflating extensional equivalence of carriers with equality of
witness structures.

### Phase 14 — Construct a minimal exit

**Question.** Is there a first candidate that preserves construction and
faithfulness while leaving the regime or the norm?

**Output.** A concrete object with positive witnesses and negative refutations.

**Risk.** Choosing a candidate that already fails to be constructed or
faithfully realized.

### Phase 15 — Produce the diagnosis

**Question.** Which exact property is lost, and which properties remain
preserved?

**Output.** A typed structure combining the candidate, its faithfulness
witnesses, its rejection, the relevant adequacy, and, when possible, a direct
normative refutation.

**Risk.** Reducing the diagnosis to a Boolean or a negation without preserving
positive witnesses.

### Condensed view

```text
presentation
  ↓
individuated occurrences
  ↓
roles + exact agreement + injectivity
  ↓
weakened carriers + separating models
  ↓
minimal primitives + reconstructed properties
  ↓
faithful transport + invariants
  ↓
independent norm ⇄ regime
  ↓
minimal exit preserving its positive witnesses
  ↓
diagnosis of the exact break
```

## 16. Failure criteria and audit checks

An application of the method must be rejected or revised when one of the
following problems appears.

### 16.1 Circular individuation

Occurrences are defined by the value the interpretation is expected to produce.
Transport can then no longer show that it preserves their identity: that
identity already depends on transport.

### 16.2 Merely nominal role

The role is reduced to a label without agreement on constitutive data. The proof
certifies a declared classification, not realization of a requirement.

### 16.3 Allegedly exhaustive coverage

A function from requirements to occurrences is presented as a bijection without
an inverse or proof of surjectivity. Every conclusion excluding additional
occurrences is then unjustified.

### 16.4 Inadequate separating carrier

The weak carrier destroys the local exactness it was supposed to preserve, or
silently retains the composability it was supposed to remove. The countermodel
no longer separates the stated properties.

### 16.5 Participation reduced to position

The presence of an index between two others is used as evidence of membership
in their composition. Constraints on source, target, and generation are absent.

### 16.6 Faithfulness reduced to final output

Two realizations are declared equivalent because they have the same terminal
state or the same number of steps. Their occurrences, agreements, or order may
nevertheless have changed.

### 16.7 Norm defined by the regime

The specification directly contains a proof of admission or is defined as the
image of the operational classifier. Soundness then ceases to provide an
independent check.

### 16.8 Diagnosis without positive information

The exit is represented only by `¬ Regime candidate`. Nothing establishes that
the candidate is constructible, that it preserves local requirements, or that
it remains faithfully interpretable.

### 16.9 Generalization without quantifiers

A result valid for every implementation satisfying an interface is restated as
a result valid for every implementation. The interface condition must remain
visible.

### 16.10 Conflation of documentary statuses

A methodological extraction or proposed generalization is presented as a Lean
theorem. Every important claim must be connected to its status and, when formal,
to a precise declaration.

## 17. Scope after Cycles 1 and 2

### 17.1 What cycle 1 actually establishes

Cycle 1 provides a formal instance in which:

- occurrences are dependently typed and remain individuated;
- non-closing requirements have an exact and injective realization;
- order and adjacency are separated on a weak carrier and then reconstructed in
  actual histories;
- intermediate position is distinguished from constitutive participation;
- free and concrete occurrences are related by inverse correspondences with
  structural agreement;
- an autonomous norm and an operational regime are adequate in both directions;
- a minimal continuation remains exactly realizable in every supplied algebra
  while failing the norm and the regime;
- the break is localized without erasing the construction.

### 17.2 What Cycle 2 adds — and does not add

Cycle 2 observes the Cycle 1 regime and norm through `Nonempty`, transports
their proposition-level equivalence through exact representation, and combines
that determined exactness with a diagonal status outside global reflective
closure. This confirms that the method's discipline of preservation before
projection remains relevant at the reflective level.

Cycle 2 is not, however, a second non-perimetral instance of the method. It
reuses the Cycle 1 adequacy and adds a representation layer; it does not supply
a new domain with independently reconstructed relational constitutive roles.

### 17.3 What the current development does not yet establish

It does not prove:

- that every alignment problem naturally has relational constitutive roles;
- that the method is complete for discovering all primitive dependencies;
- that every relevant norm can be expressed on the current carrier;
- that the normative interface is polymorphic over an arbitrary carrier;
- that structural OOD already constitutes a general formalized theory;
- that conclusions about the circular instance apply directly to contemporary
  learning systems.

These limits do not weaken the proved result. They define the work required to
turn the methodological extraction into a more general theory.

### 17.4 Future formal steps

A natural program would include:

1. isolating a generic Lean structure for relational constitutive roles;
2. parameterizing the normative interface over an arbitrary carrier equipped
   with an occurrence type;
3. formalizing a notion of morphism that preserves roles and their agreements;
4. expressing separating models through a generic structure-reduction
   interface;
5. defining a typed schema of structural OOD that distinguishes construction,
   regime, and norm;
6. instantiating the framework in at least one second, non-perimetral domain;
7. comparing retained primitives and reconstructed theorems across the two
   instances.

A second instance is especially important. It would separate what genuinely
belongs to the method from what depends on the circular geometry of the first
case.

## 18. Map of Lean anchors

| Methodological function | Main declaration |
|---|---|
| individuated occurrence in a history | `History.Occurrence` |
| exact agreement between requirement and occurrence | `RequirementOccurrenceAgreement` |
| exact and injective coverage | `ExactNonClosingRealization` |
| weakened experimental carrier | `SemanticTrace` |
| exact coverage on the weak carrier | `SemanticExactNonClosingRealization` |
| explicit order on the weak carrier | `SemanticOrderPreserved` |
| permutation countermodel | `permutedExample_not_order_preserved` |
| intermediate position | `SemanticTrace.Between` |
| exact participation in a bridge | `ExactSemanticBridgeSegment` |
| effective constitutive bridge | `EffectiveConstitutiveBridge` |
| interleaving countermodels | `interleavedExample_no_effective_bridge_p1_p2`, `interleavedExample_no_effective_bridge_p2_p3` |
| reconstructed precedence | `ExactNonClosingRealization.preservesPrecedence` |
| reconstructed adjacency | `ExactNonClosingRealization.preservesNext` |
| abstract residual uniqueness | `positiveExtension_hasUniqueResidualOccurrence` |
| one-occurrence continuation | `positiveContinuation_exactlyOne` |
| concrete occurrence agreement | `ConcreteOccurrenceAgreement` |
| exact history interpretation | `ExactHistoryInterpretation` |
| construction of exact interpretation | `exactlyInterpretHistory` |
| additivity of length | `History.length_append` |
| length equality derived from the regime | `samePerimeter_length_eq` |
| exact regime classification | `ExactRegimeClassification` |
| typed exit | `RegimeExit` |
| uniform exit | `UniformRegimeExit` |
| independent circular norm | `CircularSpecificationSatisfaction` |
| soundness | `circularRefinement_soundSpecification` |
| normative carrier completeness | `CircularSpecificationSatisfaction.eq_perimeter` |
| regime completeness | `circularSpecification_complete` |
| adequacy interface | `NormativeAdequacy`, `AdequateAlong` |
| specification-relative exit | `SpecRelativeHistoryExit` |
| canonical witness | `oneStepAfterPerimeter` |
| canonical uniform exit | `oneStepUniformPerimetralRegimeExit` |
| canonical relative diagnosis | `oneStepSpecRelativeHistoryExit` |
| direct normative refutation | `oneStepSpecRelativeHistoryExit_notSpecification` |

## 19. Reproduction and audit

The cited Lean results are distributed across:

- [`SegmentedResidualRole.lean`](../../SegmentedResidualRole.lean);
- [`AbstractSegmentedTurning.lean`](../../AbstractSegmentedTurning.lean);
- [`StrongPerimetralTurning.lean`](../../StrongPerimetralTurning.lean).

After installing `elan`, or an equivalent environment capable of reading
`lean-toolchain`, compile the project with:

```bash
lake build
```

From the repository root, verify the integrity manifest on Linux or macOS with:

```bash
bash scripts/verify-manifest.sh
```

On Windows PowerShell:

```powershell
powershell -ExecutionPolicy Bypass -File scripts/verify-manifest.ps1
```

An audit of a future adaptation should additionally verify:

1. that occurrences are not defined by their readings;
2. that every stated agreement appears in an identifiable type or theorem;
3. that separating models actually preserve the weaker layers;
4. that properties described as derived are accompanied by their
   reconstruction;
5. that interpretations provide round-trip laws;
6. that the norm does not definitionally depend on the evaluated regime;
7. that every exit preserves a positive witness of faithfulness;
8. that quantifiers over implementations remain explicit;
9. that conceptual proposals are distinguished from Lean results.

## 20. Conclusion

The method of relational constitutive roles organizes a formalization around
what must be preserved before any reduction: occurrences, their formations, and
the relations that determine their participation in a construction.

Its central move is not to add ever more primitives. It is to test dependencies:
weaken the carrier, construct a separating model, reintroduce the structure, and
observe what becomes derivable. This approach minimizes primitives without
prematurely reducing objects.

Faithful transport extends the same discipline across representations. An
implementation is not certified merely by equality of its final output, but by
exact preservation of the relevant occurrences and agreements. Numerical
invariants may then be read as consequences of an already preserved structure.

In normative analysis, the same method requires a separation between what can
be constructed, what can be faithfully realized, what a regime admits, and what
an independent norm requires. Adequacy between regime and norm becomes a theorem
to establish, not a postulated identity. An exit can then preserve its existence
and faithfulness while carrying the exact proof of its normative break.

The method can be condensed as follows:

> **Preserve the finest-grained individuation and the relations that constitute
> it; test each dependency on the minimal carrier where it can be separated;
> transport, classify, or measure only after proving what is preserved; then
> diagnose a break by retaining on the same object the positive witnesses of
> what remains and the negative proof of what ceases to be satisfied.**

Cycle 1 verifies one complete instance of this method. Cycle 2 transports one
of its established adequacy results into a reflective representation layer but
does not constitute a second domain instance. Generalizing the method therefore
still requires formalizing the methodological interface itself and testing it
on other domains, without erasing the distinction between Lean result, derived
consequence, and theoretical proposal.

## Authorship

> **Conceptual-authorship and AI-generation disclosure.** The project owner
> declares that the project's essential ideas and research direction are
> their own. This document was written from start to finish by models in
> OpenAI's ChatGPT model series, under human direction and through successive
> interactions. See the
> [full bilingual declaration](../../AI_AUTHORSHIP.md).
