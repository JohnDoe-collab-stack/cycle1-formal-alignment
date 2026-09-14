# Cycle 1 — Relative alignment to an independent specification

**English** | [Français](../fr/alignement_relatif.md)

Navigation: [structural synthesis](structural_foundations.md) ·
[method](relational_constitutive_roles_method.md) ·
[Cycle 2 — reflective alignment](reflective_alignment.md)

## Status

**Cycle 1 is mathematically closed.**

The current phase is stabilization. No mathematical definition of Cycle 1 is to
be reopened.

For a presentation `P`, a history `H`, and a concrete interpretation `A`, the
reference result distinguishes:

```text
F_A(H) := ExactConcreteRealization A H
S(H)   := CircularSpecificationSatisfaction P H
R(H)   := CircularRefinement P H
```

These three predicates are not identified. Their relationship is established by
two complementary results:

```text
R(H) → S(H)
S(H) → R(H)
```

together with the exact classification:

```text
S(H) → H = perimeterDeployment P
```

The central contribution is:

> **Cycle 1 builds and machine-checks in Lean a dependently typed kernel for
> relative alignment. It separates construction, faithful realization, regime,
> and independent norm; proves exact adequacy between the norm and the regime on
> their carriers; and produces a one-occurrence continuation which, like every
> rooted generated history, is exactly realizable in every supplied concrete
> algebra and locates the normative break without denying the continuation of
> construction.**

The proof is complete relative to the data of `CircularPresentation`. No
additional principle connecting the norm to the regime after the fact—called an
“external closure bridge” here—is added to obtain soundness or completeness.

---

## 1. Purpose of Cycle 1

Cycle 1 constructs a relative diagnostic in which four levels remain formally
distinct:

```text
constitution / realization
  ExactNonClosingRealization
  ExactConcreteRealization

independent norm
  CircularSpecificationSatisfaction

regime
  CircularRefinement

norm / regime adequacy
  NormativeAdequacy
  AdequateAlong

relative diagnostic
  SpecRelativeHistoryExit
```

The central architectural point is that the norm is not defined by the regime.

```text
norm S
  constructed and tested independently

CircularRefinement
  subsequently evaluated relative to S
```

The regime's rejection of a candidate therefore does not define that candidate's
normative failure.

### 1.1 Internal data of the presentation

`CircularPresentation` contains neither `CircularRefinement` nor
`CircularSpecificationSatisfaction`, and it contains no assumption asserting
their adequacy. It supplies the geometric data of the construction—an initial
node, a nonempty perimeter, a final junction, endpoints, poles, a difference, and
provenance—together with three closure-related operations:

```lean
closeFromIdentification :
  leftEndpoint = rightEndpoint → TotalLoop

loopContractsInitialDifference :
  TotalLoop →
    leftPole initialNode.difference = rightPole initialNode.difference

rejectInitialContraction :
  Provenance initialNode.difference →
  leftPole initialNode.difference = rightPole initialNode.difference → False
```

Rejection of a total loop is derived by composition:

```text
P.TotalLoop
  ↓ P.loopContractsInitialDifference
contraction of the poles of the initial difference
  ↓ P.rejectInitialContraction P.initialNode.provenance
False
```

This derivation is encapsulated by `CircularPresentation.rejectTotalLoop`. The
norm uses it to exclude every strict continuation that would claim to realize a
total loop.

The Lean development also constructs `Example.examplePresentation`, a finite
four-node `CircularPresentation` whose endpoints are distinguished by `Bool`.
The internal presentation data are therefore explicitly inhabited in the
development; the interface is not left without a model.

---

## 2. Four separations that must be preserved

Cycle 1 documentation must explicitly preserve the following distinctions:

```text
realization ≠ norm

norm ≠ regime

regime ≠ adequacy of the regime

candidate diagnostic ≠ regime diagnostic
```

### 2.1 Realization ≠ norm

A candidate may be exactly constituted and faithfully interpreted while failing
the independent norm. Faithful realization guarantees that the requested
structure is realized correctly; it does not determine the candidate's normative
status by itself.

### 2.2 Norm ≠ regime

`CircularSpecificationSatisfaction` is constructed before it is compared with
`CircularRefinement`. The norm has its own positive model and its own canonical
counterexample. Its content is therefore not a translation of the regime.

### 2.3 Regime ≠ adequacy of the regime

`CircularRefinement` is a regime carrying rich operational data.
`NormativeAdequacy` separately expresses the relation between that regime and an
independent specification. Adequacy is not a hidden field of the regime.

### 2.4 Candidate diagnostic ≠ regime diagnostic

Two different results are available for `oneStepAfterPerimeter P`:

```text
semantic diagnostic
  CircularSpecificationSatisfaction P candidate → False

regime diagnostic
  CircularRefinement P candidate → False
```

The first refutation is proved directly from the independent norm. The second is
carried by `RegimeExit`. The semantic diagnostic does not depend on the regime
diagnostic.

---

## 3. The independent norm

The Cycle 1 norm is minimal:

```lean
structure CircularSpecificationSatisfaction
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P) where
  «local» :
    ExactNonClosingRealization P history

  trajectory :
    CircularClosureMeaning P history
```

The `«local»` field uses Lean escaping because `local` is a reserved word. The
norm therefore has exactly two primitive components.

```text
local
  ExactNonClosingRealization

trajectory
  CircularClosureMeaning
```

### 3.1 Local component

`ExactNonClosingRealization` states the exact and injective realization of every
non-closing requirement in a genuine `RootedGeneratedHistory`.

It does not include the following as primitive fields:

```text
precedence
adjacency
participation
relevant contiguity
```

These properties were studied separately before being derived. In particular:

```lean
ExactNonClosingRealization.preservesPrecedence
ExactNonClosingRealization.preservesNext
```

establish preservation of canonical precedence and canonical constitutive
adjacency, respectively. Thus:

```text
ExactNonClosingRealization
+ RootedGeneratedHistory
→ correct precedence
+ correct constitutive adjacency
```

The final local status is:

```text
ExactNonClosingRealization   local primitive
precedence                   derived
adjacency                    derived
participation                carried by History
relevant contiguity          derived
```

### 3.2 Trajectory component

The meaning of closure is independent of the regime:

```lean
abbrev CircularClosureMeaning
    (P : CircularPresentation)
    (history : RootedGeneratedHistory P) : Type _ :=
  StrictConstitutivePrefix
      (perimeterDeployment P) history →
    P.TotalLoop
```

This component expresses an obligation on the trajectory. It does not provide
an operational realization of closure.

---

## 4. The two canonical cases

Cycle 1 is discriminating because the same norm has a canonical positive case
and a canonical negative case.

### 4.1 Positive case: `perimeterDeployment P`

The canonical deployment satisfies both the local and trajectory components.

```text
perimeterDeployment P

ExactNonClosingRealization             ✓
CircularClosureMeaning                 ✓
CircularSpecificationSatisfaction      ✓
CircularRefinement                     ✓
```

Satisfaction of `CircularClosureMeaning` is structurally vacuous on the
canonical deployment: a `StrictConstitutivePrefix` from that deployment to
itself is impossible. This does not weaken the norm's discriminating power. The
obligation becomes active precisely when a strict continuation is supplied, as
the next case shows.

The positive normative result is constructed by:

```lean
perimeterDeployment_specificationSatisfaction
```

The positive canonical regime witness is:

```lean
identityCircularRefinement
```

### 4.2 Negative case: `oneStepAfterPerimeter P`

The one-step free successor preserves exact local structure and concrete
faithfulness, but fails trajectory closure.

“Minimal” has a precise structural meaning here: the continuation suffix carries
exactly one occurrence, as established by `positiveContinuation_exactlyOne`. It
does not mean an optimum of an additional numerical measure.

```text
oneStepAfterPerimeter P

ExactNonClosingRealization             ✓
correct precedence                     ✓
correct adjacency                      ✓
ExactConcreteRealization A             ✓

CircularClosureMeaning                 ✗
CircularSpecificationSatisfaction      ✗
CircularRefinement                     ✗

regime adequate to S                   ✓
SpecRelativeHistoryExit for supplied A ✓
```

The normative break is located exactly in `trajectory`:

```text
local exact       ✓
precedence        ✓ derived
next              ✓ derived

trajectory        ✗
```

The trajectory refutation is direct:

```text
CircularClosureMeaning
        ↓
oneStepAfterPerimeterStrict
        ↓
P.TotalLoop
        ↓
P.rejectTotalLoop
        ↓
False
```

The regime does not occur in this proof.

---

## 5. Central comparison table

| Property | `perimeterDeployment P` | `oneStepAfterPerimeter P` |
|---|---:|---:|
| `ExactNonClosingRealization` | ✓ | ✓ |
| correct precedence | ✓ | ✓ |
| correct constitutive adjacency | ✓ | ✓ |
| faithful concrete realization for every supplied `ConcreteContinuationAlgebra P` | ✓ | ✓ |
| `CircularClosureMeaning` | ✓ | ✗ |
| `CircularSpecificationSatisfaction` | ✓ | ✗ |
| `CircularRefinement` | ✓ | ✗ |
| regime adequate to `S` | ✓ | ✓ |
| negative relative diagnostic for a supplied `ConcreteContinuationAlgebra P` | — | ✓ |

The correct reading of the table is:

> `oneStepAfterPerimeter P` fails neither because local constitution is absent,
> nor because precedence or adjacency is lost, nor because concrete faithfulness
> fails. It fails on the trajectory component of the independent norm.

---

## 6. Structural reconstruction of the perimeter

A decisive step in Cycle 1 is reconstructing a `PerimeterExtension` from exact
local realization alone:

```lean
ExactNonClosingRealization.toPerimeterExtension
```

The result has the form:

```text
ExactNonClosingRealization P H
        ↓
exact copy of canonical occurrences
        ↓
initial factorization of H.history
        ↓
suffix after perimeterHistory P
        ↓
PerimeterExtension P H
```

This reconstruction is structural. It does not use a numerical length, rank, or
external count.

The main auxiliaries are:

```text
embedPerimeterOccurrence
embedPerimeterOccurrence_locatedStep
embedPerimeterOccurrence_injective

History.factorInitialGeneratedStep
History.extractRightOccurrenceAfterSingle

factorDeployRemainingFromExactOccurrences
ExactNonClosingRealization.toPerimeterExtension
```

This step is the constructive lock that enables carrier completeness.

---

### 6.1 Exact one-step constitutive persistence

The canonical continuation also supports a content-independent result that is
separate from its later admission and normative statuses.  Write `I0` for the
free occurrences of the perimeter and `I1` for those of its one-step
continuation.  `ConstitutivePersistence.freeOccurrenceSplit` constructs an
exact two-sided transport:

```text
I0 + Unit  <->  I1
```

Thus every occurrence of the continuation is classified constructively as
either one prior occurrence or the distinguished fresh occurrence.  For every
supplied concrete algebra `A`, exact interpretation gives separate spokes:

```text
I0 <-> C0[A]
I1 <-> C1[A]
```

Transport between two realizations is derived through these shared indices; no
pairwise concrete matching is added.  Lean proves the old/fresh naturality laws
and pointwise path coherence:

```text
T1[A,B](old[A](x)) = old[B](T0[A,B](x))
T1[A,B](fresh[A])  = fresh[B]
T[B,C](T[A,B](x))  = T[A,C](x)
```

A candidate extended transport is also pointwise determined once its action is
fixed on every prior occurrence and on the fresh occurrence.  This is relative
uniqueness under the complete split, not uniqueness of every possible exact
correspondence.

`ExactOneStepConstitutiveAlignment` extracts exactly the transition carrier and
its old/fresh split.  Its separate `Realization` structure contains only the two
concrete carriers and their exact spokes.  It is therefore an exact carrier
realization, not by itself a claim about labels, order, or step semantics.
Neither structure mentions a `CircularPresentation`, admission, a
specification, or a readout.  The canonical Cycle 1 continuation instantiates
this abstraction and additionally proves that the induced old and fresh
elements are the native concrete occurrences `.earlier` and `.last`.  The
logged non-identity algebra supplies a concrete carrier realization of the same
alignment.
These instantiations establish scope; the content-independent signature carries
the generality.  The current development proves that this interface is
sufficient, but does not claim a strict minimality theorem for all of its
fields.

---

## 7. Soundness and completeness

Three closed results establish relative alignment.

### 7.1 Soundness

```text
CircularRefinement P H
→ CircularSpecificationSatisfaction P H
```

Lean declaration:

```lean
circularRefinement_soundSpecification
```

The proof projects the regime's rich data to the norm's two obligations.

```text
CircularRefinement
        |
        +--> extension
        |      ↓
        |  ExactNonClosingRealization
        |
        +--> strictRefinementProducesTotalLoop
               ↓
          CircularClosureMeaning
```

Soundness means that every carrier admitted by `CircularRefinement` satisfies
the independent norm.

### 7.2 Carrier completeness

```text
CircularSpecificationSatisfaction P H
→ H = perimeterDeployment P
```

Lean declaration:

```lean
CircularSpecificationSatisfaction.eq_perimeter
```

The proof uses:

```text
S.«local»
  ↓
ExactNonClosingRealization.toPerimeterExtension
  ↓
PerimeterExtension

continuation
  ├─ root
  │    ↓
  │  H = perimeterDeployment P
  │
  └─ positive
       ↓
     StrictConstitutivePrefix
       ↓
     S.trajectory
       ↓
     P.TotalLoop
       ↓
     P.rejectTotalLoop
       ↓
     False
```

This result deserves the name **carrier completeness**:

```text
S(P,H) → H = perimeterDeployment(P)
```

### 7.3 Regime completeness

```text
CircularSpecificationSatisfaction P H
→ CircularRefinement P H
```

Lean declaration:

```lean
circularSpecification_complete
```

The proof reconstructs no operational field of the regime from closure
semantics. It proceeds through:

```text
S P H
  ↓ eq_perimeter
H = perimeterDeployment P
  ↓ transport
identityCircularRefinement P
  ↓
CircularRefinement P H
```

Regime completeness is therefore obtained by classification of the canonical
carrier. After `CircularPresentation` has been defined, the proof adds no further
principle connecting the norm to the regime.

---

## 8. Asymmetry between soundness and regime completeness

The two comparison directions have different foundations:

```text
R → S
  projection of the regime's rich data

S → R
  carrier classification
  + transport of the canonical witness
```

This asymmetry is essential. It shows that conformity of the regime to the norm
is proved from the framework's internal structures and carrier classification,
without closure data added from outside.

---

## 9. Normative adequacy

The architecture has two levels of generality. `RegimeExit` and
`UniformRegimeExit` are polymorphic over an arbitrary carrier and presuppose
neither histories, perimeters, nor circularity. The normative interface below is
parametric over the norm and regime, but remains specialized to
`RootedGeneratedHistory P` for `P : CircularPresentation`.

This normative interface preserves occurrence indexing:

```lean
structure NormativeAdequacy
    (P : CircularPresentation) where
  AlignmentSpec : Type _
  RegimeAdequateAtOccurrence :
    AlignmentSpec →
    (R : RootedGeneratedHistory P → Type _) →
    (H : RootedGeneratedHistory P) →
    History.Occurrence H.history →
    Type _
```

The circular instance uses a history specification:

```lean
abbrev HistoryAlignmentSpec
    (P : CircularPresentation) :=
  RootedGeneratedHistory P → Type _
```

and a global adequacy relation constant in the occurrence index:

```lean
def circularNormativeAdequacy
    (P : CircularPresentation) :
    NormativeAdequacy P where
  AlignmentSpec := HistoryAlignmentSpec P
  RegimeAdequateAtOccurrence :=
    fun S R H _occurrence =>
      (R H → S H) × (S H → R H)
```

This instance does not project the occurrence to its source, target, cursor, or
reading. On the same history carrier, the interface therefore remains compatible
with later specifications that genuinely depend on the occurrence. Extending the
normative interface to a fully arbitrary carrier would require an additional
generalization, without changing the `RegimeExit` kernel.

Concrete adequacy is:

```lean
circularRefinement_adequateAlong
```

and rests exactly on:

```text
circularRefinement_soundSpecification
circularSpecification_complete
```

---

## 10. Final relative diagnostic

The final package is:

```lean
oneStepSpecRelativeHistoryExit
```

It combines:

```text
candidate
  oneStepAfterPerimeter P

faithful
  ExactConcreteRealization A candidate

inadmissible
  CircularRefinement P candidate → False

adequacy
  AdequateAlong ... candidate
```

The generic `SpecRelativeHistoryExit` structure is not modified to add a
refutation of the norm. The semantic refutation remains separate:

```lean
oneStepSpecRelativeHistoryExit_notSpecification
```

It proceeds directly through:

```lean
oneStepAfterPerimeter_notSpecificationSatisfaction
```

and not through `exit.inadmissible`.

The final diagnostic therefore has three distinct layers:

```text
constitution / realization
  rooted generated candidate
  exact realization available uniformly for every such history

norm
  candidate does not satisfy S

regime
  candidate is rejected
  and the regime is adequate to S
```

Its synthetic form is:

```text
faithful realization
+ failure to satisfy S
+ rejection by a regime proved adequate to S
```

---

## 11. Meaning of “relative alignment” here

Cycle 1 does not formalize a general theory of alignment. Within the present
framework, it establishes a diagnostic relative to an explicit and independent
specification.

The positive case is:

```text
perimeterDeployment P

S                                ✓
CircularRefinement               ✓
```

The negative case is:

```text
oneStepAfterPerimeter P

faithful realization             ✓
S                                ✗
CircularRefinement               ✗
regime adequate to S             ✓
```

The precise statement is therefore:

> The candidate `oneStepAfterPerimeter P` fails relative to `S`, while the
> `CircularRefinement` regime is adequate to that norm and correctly rejects the
> candidate.

`oneStepAfterPerimeter P` is not a regime, and the regime is not misaligned with
`S` in this case.

---

## 12. Lean API map

| Mathematical role | Lean declaration |
|---|---|
| exact local realization | `ExactNonClosingRealization` |
| derived precedence | `ExactNonClosingRealization.preservesPrecedence` |
| derived adjacency | `ExactNonClosingRealization.preservesNext` |
| reconstruction of the perimeter prefix | `ExactNonClosingRealization.toPerimeterExtension` |
| exact one-step split | `ConstitutivePersistence.freeOccurrenceSplit` |
| abstract one-step alignment | `ExactOneStepConstitutiveAlignment` |
| exact realization of an alignment | `ExactOneStepConstitutiveAlignment.Realization` |
| canonical abstract alignment | `ConstitutivePersistence.canonicalOneStepAlignment` |
| agreement with the native old occurrence | `ConstitutivePersistence.concreteOldEmbedding_isEarlier` |
| agreement with the native fresh occurrence | `ConstitutivePersistence.concreteNewOccurrence_isLast` |
| concrete path coherence | `ConstitutivePersistence.extendedConcreteTransport_forward_comp` |
| trajectory norm | `CircularClosureMeaning` |
| independent norm | `CircularSpecificationSatisfaction` |
| positive model of the norm | `perimeterDeployment_specificationSatisfaction` |
| canonical counterexample | `oneStepAfterPerimeter_notSpecificationSatisfaction` |
| carrier completeness | `CircularSpecificationSatisfaction.eq_perimeter` |
| regime completeness | `circularSpecification_complete` |
| soundness | `circularRefinement_soundSpecification` |
| history specification | `HistoryAlignmentSpec` |
| adequacy instance | `circularNormativeAdequacy` |
| adequacy along a history | `circularRefinement_adequateAlong` |
| relative diagnostic | `oneStepSpecRelativeHistoryExit` |
| semantic refutation from the package | `oneStepSpecRelativeHistoryExit_notSpecification` |

---

## 13. Proposition-level reflection in Cycle 2

The Cycle 1 declarations above are maps between proof-relevant witness types:

```text
CircularRefinement P H
  → CircularSpecificationSatisfaction P H

CircularSpecificationSatisfaction P H
  → CircularRefinement P H
```

Cycle 2 observes their inhabitability explicitly:

```text
CircularRegimeStatus P H
  := Nonempty (CircularRefinement P H)

CircularSpecificationStatus P H
  := Nonempty (CircularSpecificationSatisfaction P H)
```

`Cycle2.ReflectiveAlignment.circularStatusAdequacy` then proves the genuine
proposition-level equivalence:

```text
CircularRegimeStatus P H
  ↔ CircularSpecificationStatus P H
```

This bridge is implemented and constructive. It is derived from the two Cycle 1
maps; it neither changes Cycle 1 nor claims an `Equiv` or equality between the
original witness structures. It is the formal point from which Cycle 2
transports established adequacy into the representation layer.

---

## 14. Audit and reproducibility

From the repository root, reproduce the pinned build with:

```bash
lake clean
lake build
```

Then verify the scientific-source manifest with either:

```bash
bash scripts/verify-manifest.sh
```

or:

```powershell
pwsh -NoProfile -File scripts/verify-manifest.ps1
```

The complete environment, source hashes, build counts, and axiom-audit result
are recorded in [`audit/AUDIT_BUILD.txt`](../../audit/AUDIT_BUILD.txt). No
earlier repository or private source history is required.

The final alignment declarations are also audited:

```text
HistoryAlignmentSpec
circularNormativeAdequacy
circularRefinement_adequateAlong
oneStepSpecRelativeHistoryExit
oneStepSpecRelativeHistoryExit_notSpecification
```

Compilation confirms that Lean accepts the current artifacts without warnings.
All `#print axioms` commands in the final blocks report that the inspected
declarations depend on no axioms.

The witness-producing dependent recursions in the local-to-global chain are
written in a structurally executable form, and the compiler emits IR for each
of them. On closed presentations and realizations, the reconstruction reduces
to concrete values. The Lean sources contain no `noncomputable` declaration;
this textual policy check remains distinct from both code-generation tests and
the axiom audit.

---

## 15. Stabilized conclusion

Cycle 1 establishes three closure results:

```text
soundness
  CircularRefinement P H
  → CircularSpecificationSatisfaction P H

carrier completeness
  CircularSpecificationSatisfaction P H
  → H = perimeterDeployment P

regime completeness
  CircularSpecificationSatisfaction P H
  → CircularRefinement P H
```

It also provides a concrete diagnostic on
`h⁺ := oneStepAfterPerimeter P`:

```text
ExactConcreteRealization A h⁺             inhabited for every supplied A
CircularSpecificationSatisfaction P h⁺    directly refuted
CircularRefinement P h⁺                   refuted by the regime
adequacy of the regime to the norm         proved
```

The exact concrete realization is not specific to `h⁺`: the same construction
interprets every rooted generated history. Both refutations are relative to the
supplied `CircularPresentation`, in particular its explicit
`rejectInitialContraction` field.

The alignment proof is complete relative to the presentation and norm of Cycle
1. It does not identify realization, satisfaction, and admission; it separately
proves their relationship and locates their exact separation on the one-step
free candidate.

### Stabilization invariants

Documentation and versioning changes must preserve:

```text
the mathematical definitions and signatures
the CircularSpecificationSatisfaction norm
the CircularRefinement regime
the contrast between the two canonical cases
the absence of an added bridge between norm and regime
the axiomatic-audit results
```

The proposition-level bridge in Section 13 belongs to Cycle 2. It observes the
closed Cycle 1 result without altering its witness types or mathematical content.

### Publication statement

> **Cycle 1 builds and machine-checks in Lean a dependently typed kernel for
> relative alignment. It separates construction, faithful realization, regime,
> and independent norm; proves soundness and completeness of their agreement on
> admitted histories; and constructs a one-occurrence continuation which, like
> every rooted generated history, remains exactly realizable under every
> concrete implementation satisfying the interface while being rejected by
> both the norm and a regime proved adequate to that norm. These refutations are
> relative to the explicit closure obstruction supplied by
> `CircularPresentation`.**

## Authorship

> **Conceptual-authorship and AI-generation disclosure.** The project owner
> declares that the project's essential ideas and research direction are
> their own. This document was written from start to finish by models in
> OpenAI's ChatGPT model series, under human direction and through successive
> interactions. See the
> [full bilingual declaration](../../AI_AUTHORSHIP.md).
