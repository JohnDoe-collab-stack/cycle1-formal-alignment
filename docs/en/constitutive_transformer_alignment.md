# Constitutive alignment of transformer systems

**English** | [Français](../fr/alignement_constitutif_transformers.md)

Navigation: [structural synthesis](structural_foundations.md) ·
[method](relational_constitutive_roles_method.md) ·
[Cycle 1 — relative alignment](relative_alignment.md) ·
[Cycle 2 — reflective alignment](reflective_alignment.md)

## 1. Thesis

A transformer architecture does not become persistent, long-horizon coherent,
or reliable merely by adding more context, an external memory, or an output
classifier. Such devices operate on objects they take as already individuated.
The prior problem is to determine what makes an occurrence remain the same
occurrence through its formation, transformation, compression, retrieval, and
later use.

The architectural hypothesis developed here is:

> **A transformer system must constitute its objects through the relations that
> determine their identity, then prove that this constitution is preserved
> across its realizations. Persistent memory, long-horizon reasoning, and the
> prevention of hallucinations then become three consequences of one structural
> fidelity requirement.**

This proposal transposes the method of relational constitutive roles. It does
not reduce those roles to labels attached to model representations. A label
describes an object taken as already given; a constitutive relation participates
in determining the object itself. If that relation is removed or altered, it is
not merely one property of the object that changes: the system no longer has
the same object in the sense relevant to its history.

## 2. Formal starting point

The repository already establishes a complete structural chain on a first
instance:

```text
presentation
  → dependently typed construction
  → occurrences individuated within a history
  → roles and exact agreements
  → faithful realization
  → operational regime and autonomous norm
  → exact adequacy
  → faithfully realizable minimal continuation
  → localized exit from regime and norm
```

Cycle 2 transports the inhabitability of witness families into a
representation layer and proves simultaneously:

```text
exact representation of determined statuses
  + non-representable diagonal status
  → absence of global reflective closure
```

The application to transformers is therefore not an import of these structure
names into an existing architecture. It is the construction of a second
instance of the method whose carrier, occurrences, roles, agreements, and
realizations genuinely belong to transformer systems.

## 3. The fundamental object is neither a token nor a vector

An isolated token is a vocabulary value. An activation vector is an element of
a numerical space. Neither by itself determines the occurrence whose identity
the system must preserve.

The same string can occur several times with different origins, dependencies,
and functions. Conversely, one occurrence may be paraphrased, distributed
across several vectors, or realized on different supports without ceasing to be
the same structural occurrence.

The relevant carrier must therefore be a history of typed transformations:

```lean
State   : Type
Step    : State → State → Type
History : State → State → Type
```

An occurrence is not a value extracted from that history after the fact. It is
indexed by the history that formed it:

```lean
Occurrence : {a b : State} → History a b → Type
```

This dependency preserves at least:

- the occurrence's formation step;
- its source and target states;
- its structural position in the trajectory;
- the occurrences on which its formation depends;
- the obligations in which it participates;
- the transformations through which it was realized.

Two textually identical occurrences remain distinct when their formations
differ. Two materially different realizations can, conversely, correspond
exactly to the same constitutive requirement when faithful agreement and
transport are supplied.

## 4. Constitutive roles and agreements

A role is not a class such as `fact`, `memory`, `premise`, or `error`. It
expresses a relational requirement on which an occurrence's participation in
the construction depends.

Within a transformer trajectory, roles may determine:

- which transformation formed the occurrence;
- which earlier occurrences it constitutively depends on;
- which difference it introduces into the current state;
- which provenance it continues or transforms;
- which obligation it opens, preserves, or satisfies;
- which composition it effectively participates in;
- which occurrences must precede it or be immediately adjacent to it.

This is not an annotation schema. Each retained role must have an agreement
type establishing that a given occurrence actually realizes it. The Cycle 1
model is:

```lean
RequirementOccurrenceAgreement
  (history : History)
  (requirement : Requirement)
  (occurrence : Occurrence history) : Type
```

The agreement must expose the data that make the correspondence exact: source
and target states, formation, dependencies, compatibilities, provenance, or
other domain structure. Identity never follows merely from declaring that an
occurrence bears the correct role.

## 5. Exact realization without forced exhaustiveness

For a family of roles required by a construction, an exact realization must
supply:

```lean
realize           : Role → Occurrence history
realize_injective : Injective realize
agreement         : ∀ role, Agreement role (realize role)
```

Coverage runs from required roles to their occurrences. It does not state that
every occurrence produced by the transformer must already receive one of those
roles. This asymmetry is essential: construction may continue and form new
occurrences without erasing prior local exactness.

Injectivity prevents two constitutively distinct requirements from being
realized by one occurrence merely because their representations are nearby.
Agreement prevents the converse defect: two distinct occurrences do not become
faithful merely because they occupy separate memory locations.

## 6. The transformer as a realization

The transformer is not the source of constitution. It is one possible
realization of a history already specified at the structural level.

Three trajectories must consequently be distinguished:

```text
constitutive history
  = formation of occurrences and their dependencies

execution history
  = concrete transformations performed by the architecture

token trace
  = discrete inputs and outputs of one particular execution
```

They are not identified term by term. One constitutive occurrence may be
realized by several tokens and internal states; one generation step may
contribute to several relations without by itself constituting a complete
occurrence. Realization must therefore associate an occurrence with a
structured execution witness rather than attach its name to a token or vector.

A concrete realization may use tokens, activations, attention states, a cache,
persistent memory, or several supports. Its fidelity does not depend on the
chosen support but on the maps and laws connecting free occurrences with
concrete occurrences:

```lean
forward  : FreeOccurrence history → ConcreteOccurrence realization
backward : ConcreteOccurrence realization → FreeOccurrence history

backward (forward occurrence) = occurrence
forward (backward concrete)   = concrete
```

When an implementation contains more concrete phenomena than the specification
must track, these laws can be restricted to the fibre of constitutively
relevant occurrences. What cannot be replaced is the proof that tracked
occurrences, their agreements, and their necessary relations survive transport.

Vector similarity, plausible linguistic reconstruction, or equality of the
terminal output does not constitute such a proof. Two executions may reach the
same answer while losing a dependency, reversing two occurrences, or
substituting one provenance for another.

Memory, context, and activations are therefore realization supports. They carry
continuity only through the laws that relate them to the constitutive history.

## 7. Four irreducible layers

For a history `H` and candidate continuation `x`, the architecture must keep
four families distinct:

```text
C(H, x)   internal construction of x
F_A(H, x) faithful realization of x in implementation A
R(H, x)   admission of x by the operational regime
S(H, x)   satisfaction by x of an autonomous norm
```

The transformer generator produces construction witnesses. A concrete
realization supplies fidelity witnesses. The regime decides which continuations
are admitted in a given trajectory. The norm independently states what that
trajectory must satisfy.

Relative alignment is not a score, a preference, or agreement between two
outputs. It is constituted by witness transformations:

```text
R(H, x) → S(H, x)    soundness
S(H, x) → R(H, x)    relative completeness
```

Both families concern the same finely individuated candidate. Defining the norm
from the regime's decision would make adequacy tautological and remove the very
control being sought.

## 8. One structural origin for three problems

### 8.1 Persistent memory

Persistent memory is the preservation of constituted occurrences through a
succession of transformations. It is not merely the later availability of a
text or similar content.

A memory is faithful when it recovers an occurrence together with the relations
that determine its identity in the history: formation, provenance,
dependencies, and status relative to the relevant obligations. Paraphrase or
compression is admissible when it realizes an exact transport of this
structure. Without that transport, a system may retrieve similar information
while losing the object to which later reasoning was meant to refer.

### 8.2 Long-horizon reasoning

Long reasoning is a composition of occurrences and obligations, not a large
quantity of intermediate text. Its continuity depends on preserving what makes
each step participate in the trajectory: its effective premises, permitted
transformations, acquired results, and still-open obligations.

The relevant horizon is therefore structural rather than metric. A line of
reasoning may be long in tokens yet structurally broken near its beginning; it
may be heavily compressed yet remain intact if its necessary constitutive
relations are preserved.

### 8.3 Hallucination

Within this framework, hallucination is not primitively a sentence type or a
label assigned to an output. The relevant phenomenon appears when a
continuation remains constructible and concretely realizable while the
agreement required by the autonomous norm is no longer available or is
constructively refuted.

The system must not remove this continuation from the construction space, as
that would conceal the phenomenon. It must retain on the same candidate:

```text
construction witness
+ faithful-realization witness
+ previously preserved structure
+ proof of the first broken obligation
```

Hallucination thereby becomes one possible case of a localized structural exit.
Its exact definition depends on the domain norm; it is identical neither to
operational inadmissibility alone nor to every continuation outside the regime.

## 9. Diagnosis through constitutive exit

An architecture capable of continuing must positively represent what remains
when a boundary is crossed. The generic schema is:

```lean
structure RegimeExit (Faithful Regime : Carrier → Type) where
  candidate    : Carrier
  faithful     : Faithful candidate
  inadmissible : Regime candidate → False
```

For the transformer domain, this diagnostic must be enriched with historical
continuation and, where the norm permits, a direct normative refutation. The
target is a first candidate such that:

```text
it is formed by the system;
it is strictly later than an admitted trajectory;
prior occurrences remain exactly realized;
the new occurrence remains concretely realizable;
one precise constitutive obligation ceases to be satisfied;
regime and norm reject the continuation for explicit reasons.
```

Such a witness would be the transformer analogue of
`oneStepAfterPerimeter`. It would supply a local diagnosis without denying that
the system actually produced a continuation.

## 10. A dynamic, non-closed architecture

Cycle 2 prevents exact representation of some statuses from implying internal
representability of all possible statuses. For an evaluator

```lean
eval : Code → Code → Prop
```

the status

```lean
diagonalStatus eval code := ¬ eval code code
```

is exactly represented by no row of that evaluator. This non-closure does not
destroy the exactness of the particular statuses already represented.

As an architectural consequence, this rules out the project of a transformer
containing a total and final representation of the validity of all its own
constructions. The system must be dynamic, relative to determined norms and
regimes, and able to continue by producing explicit exits when it reaches its
internal boundaries.

Useful reflectivity is therefore not global self-certification. It is exact
representation of determined statuses within an architecture that
constitutively recognizes its non-closure.

## 11. Formal program

The second instance must be developed in the following order.

### 11.1 Transformer presentation

Define states and formation rules without encoding in them the regime or norm
that will later be studied.

### 11.2 Dependent occurrences

Construct a history-indexed occurrence type capable of distinguishing textual
repetitions while retaining their formation.

### 11.3 Constitutive roles and agreements

Define a minimal kernel of relational roles, then use weakened carriers to test
which relations are primitive and which can be reconstructed.

### 11.4 Abstract and concrete realization

First establish an interface independent of numerical architecture, then show
how a transformer execution exactly realizes occurrences and their agreements.

### 11.5 Composition of transports

Prove that successive transports used by attention, compression, retrieval,
and reinjection preserve fidelity. Composition must retain witnesses, not only
a terminal measurement.

### 11.6 Regime, norm, and adequacy

Define both families independently and construct soundness and completeness
maps on a determined domain.

### 11.7 Minimal exit

Construct a minimal continuation that preserves positive witnesses while
localizing the first constitutive break exactly.

### 11.8 Reflective layer

Transport inhabitability of adequate statuses into an internal representation
and integrate diagonal non-closure without identifying it with the operational
exit.

## 12. Criterion for a first implementation

A first implementation is not meant to discover the framework empirically. It
must realize an already defined interface and make its obligations auditable.

It is sufficient if it can:

1. form a history of transformations;
2. individuate each occurrence by its formation;
3. associate roles through verifiable agreements rather than labels;
4. transport occurrences through at least one representation reduction;
5. reconstruct constitutive relations after that transport;
6. distinguish construction, fidelity, regime, and norm;
7. produce an exit candidate retaining its positive witnesses;
8. localize the first broken obligation.

The initial case must have a sufficiently precise decidable norm for witness
transformations to be constructed. Extension to open norms follows this exact
instance rather than replacing it.

## 13. Intended contribution

The contribution is not a new memory, retrieval, or verification variant added
to a model. It is an architecture of constitution and preservation in which:

- objects are individuated by their formation and relations;
- representations are realizations subject to fidelity laws;
- persistence means preservation of constitutive identity;
- reasoning means preserved composition of occurrences and obligations;
- normative break is localized without erasing construction;
- local exactness remains compatible with global reflective non-closure.

The intended result is a system that does not claim to make every
out-of-norm continuation impossible. It makes structurally explicit what is
formed, what is preserved, what is admitted, what satisfies the norm, and the
exact point at which these dimensions cease to coincide.

## 14. Status of this document

The current repository machine-checks the structural kernel, the circular
instance of relative alignment, and the reflective non-closure result. This
document determines the architectural transposition of that framework to
transformer systems. Declarations specific to this second instance must be
added as new Lean objects before they are presented as theorems about
transformers.

## Conception

> **Statement of intellectual conception and AI generation.** The project lead
> states that the essential ideas and research direction of the project are
> their own. This document was written from beginning to end by models in
> OpenAI's ChatGPT series, under human direction and through successive
> interactions. See the
> [full bilingual statement](../../AI_AUTHORSHIP.md).
