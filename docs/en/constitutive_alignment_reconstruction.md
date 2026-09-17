# Reconstruction of constitutive alignment

**English** | [Francais](../fr/reconstruction_alignement_constitutif.md)

Navigation: [method](relational_constitutive_roles_method.md) · [relative norm/regime alignment](relative_alignment.md) · [architecture map](verified_architecture_map.md)

## Status

This layer formalizes a constructive reconstruction of alignment between two initially distinct constitutive carriers.

It does not replace the established constitutive alignment induced by a shared index. It adds a reverse reconstruction direction and a decision layer relative to explicit relational data.

The following distinction must remain visible:

```text
constitutive alignment
=
coherence and reconstruction of transported identities

normative adequacy
=
relation between a regime and an independent specification
```

The [relative alignment](relative_alignment.md) document mainly treats the second axis. This document treats the first.

Genesis depth is not bounded by any fixed integer. Propagation and reconstruction theorems are parameterized by an arbitrary `n : Nat`. Finiteness enters elsewhere, in the exhaustive search layer, when complete enumerations of carriers and anchors are supplied.

---

## 1. Problem addressed

The historical alignment layer starts from a shared constitutive carrier and derives transports between realizations through that index.

```text
             shared index
             /          \
            v            v
      realization A  realization B
```

The new layer studies a harder problem:

```text
Source                     Target
  |                          |
  v                          v
construction A          construction B

        correspondence ?
```

`Source` and `Target` may be different types. No common initial identity carrier is assumed.

Reconstruction proceeds in stages. The development does not claim to derive semantic correspondence from cardinality alone or from an arbitrary bijection.

---

## 2. Reconstruction from genesis

At a natural depth `n`, consider a terminal exact transport:

```text
T : IteratedCarrier Source n
      <->
    IteratedCarrier Target n
```

`PreservesGenesis T` requires every identity introduced as fresh at a given birth depth to be transported to the identity introduced at the same depth on the target side.

The canonical transport induced by an initial transport is constructed by:

```lean
liftToDepth
```

and automatically preserves genesis:

```lean
liftToDepth_preservesGenesis
```

The reverse direction is constructive. A terminal exact transport preserving all genesis strata can be recursively restricted to its old component until the initial carriers are reached:

```lean
reconstructInitial
```

The central characterization is:

```text
PreservesGenesis T
        <->
T is the canonical lift
 of an exact transport Source <-> Target
```

formalized by:

```lean
preservesGenesis_iff_reconstructible
```

Genesis therefore adds no new alignment degrees of freedom at later depths. A terminal transport compatible with the whole birth stratification is completely determined by an initial transport.

This step does not yet determine which initial identity of `Source` should correspond to which initial identity of `Target`.

---

## 3. Exact localization of ambiguity

The rigidity layer formalizes that terminal ambiguity compatible with genesis is exactly the ambiguity already present at the base.

`InitialForwardRigid Source Target` means that all exact initial transports have the same forward map pointwise.

`GenesisForwardRigid Source Target n` expresses the corresponding uniqueness at depth `n` among exact genesis-preserving transports.

For every supplied natural depth, the development proves equivalence between these two forms of rigidity.

The conceptual consequence is:

```text
genesis
fixes every generated layer

but

genesis alone
does not break a symmetry already present at the base
```

Regression examples on `Bool` exhibit two distinct initial transports whose lifts both preserve genesis. Initial correspondence must therefore be constrained by additional structure.

---

## 4. Separating constitutive profiles

The next layer introduces shared structural observations without postulating a common identity carrier.

A profile has the form:

```text
Carrier -> Probe -> Value
```

`ProfileSeparates profile` means that the complete family of observations distinguishes identities:

```text
same observations on every probe
        ->
same identity
```

`PreservesProfile` states that a map preserves these observations.

Target-side separation is enough to make every profile-preserving forward map pointwise unique.

This layer also shows that a pair of forward and backward resolvers preserving separating profiles need not store inverse laws as primitive assumptions. The two round trips are derived from separation and then assembled into an `ExactTypeTransport`.

The methodological direction is:

```text
separating observations
+
compatible mapping
        ->
derived round trips
```

not:

```text
assumed bijection
        ->
declared structural compatibility
```

---

## 5. Profiles derived from anchored relations

`AnchoredRelationContext` derives profiles from local relations.

It contains:

```text
sourceRelation : Source -> Source -> Value
targetRelation : Target -> Target -> Value

sourceAnchor : Anchor -> Source
targetAnchor : Anchor -> Target
```

together with separation of identities by observations from the anchor family.

For a source identity `s` and a target identity `t`, the relation:

```lean
context.Matches s t
```

states that all their observations relative to corresponding anchors agree.

Anchors are not a complete common identity index. They provide a shared family of relational reference points. The correspondence between all identities is still reconstructed.

Profile separation proves:

```text
a source has at most one compatible target

a target has at most one compatible source
```

Thus `Matches` provides uniqueness but not yet existence.

---

## 6. Positive totality and reconstruction of exact transport

`TotalAnchoredMatching context` provides the two constructive existence obligations:

```text
for every source
there is a target satisfying Matches

for every target
there is a source satisfying Matches
```

The witnesses are positive subtypes. `forward` and `backward` are projected from these witnesses.

Uniqueness of `Matches` then derives:

```text
backward(forward(x)) = x
forward(backward(y)) = y
```

and therefore:

```lean
TotalAnchoredMatching.toExactTransport
```

The exact alignment map is no longer an unconstrained primitive. It is reconstructed from the structural relation and its constructive totality.

Propagation to every natural depth is canonical:

```lean
TotalAnchoredMatching.finiteTransport
TotalAnchoredMatching.finiteTransport_preservesGenesis
```

The historical name `finiteTransport` here means transport at a depth indexed by a natural number. The parameter `depth : Nat` is arbitrary and no maximum depth is imposed.

---

## 7. Directional weakening and strictness

One-sided totality is retained as a result in its own right.

`ForwardAnchoredMatching` produces an injective map:

```text
Source -> Target
```

that preserves anchored observations.

`BackwardAnchoredMatching` provides the symmetric result.

This structure does not manufacture an inverse when none is justified.

Regression tests construct a context in which forward matching exists and is injective while no compatible backward matching exists. Therefore:

```text
forward totality
        ->
structural injection

but

forward totality
        -/->
exact bidirectional alignment
```

This separation prevents structural inclusion from being conflated with exact equivalence.

---

## 8. Executable search over finite enumerations

The previous layer still leaves totality as supplied constructive data.

`FiniteAnchoredMatchSearch` closes that obligation in a precise executable case.

It assumes:

```text
a complete finite anchor listing
a complete finite Source listing
a complete finite Target listing
decidable equality on Value
```

`FiniteListing A` contains an explicit list and a proof that every element of `A` occurs in that list.

The search compares anchored profiles with a Boolean test:

```lean
matchesOn
```

then searches for counterparts:

```lean
findTarget
findSource
```

The global checks are:

```lean
forwardTotalCheck
backwardTotalCheck
```

A successful forward check directly constructs a `ForwardAnchoredMatching`. The backward check symmetrically constructs a `BackwardAnchoredMatching`. If both succeed, the development constructs a `TotalAnchoredMatching`, then exact transport and its propagation to any requested `n : Nat`.

Finiteness is a real hypothesis of this exhaustive search layer. It does not bound the genesis depth of the propagation theorems.

---

## 9. Completeness of decision and negative certificates

The search is not only sound.

`FiniteAnchoredMatchDecision` also proves the converse direction: if a total structural matching exists, the corresponding check must return `true` over complete listings.

Therefore:

```text
forwardTotalCheck = false
        ->
no compatible ForwardAnchoredMatching
```

and symmetrically in the backward direction.

A failed search is therefore a constructive non-existence certificate relative to the supplied anchored context and complete enumerations. It is not merely a heuristic failure.

The module also derives refutation of compatible exact alignment whenever either directional totality fails.

---

## 10. Constructive classification into four regimes

The two directional checks induce four regimes:

```text
exact
forwardOnly
backwardOnly
noDirectionalMatching
```

`FiniteAlignmentClassification.classify` computes the regime directly and retains the corresponding witnesses or refutations.

### `exact`

Both totalities exist. One obtains a `TotalAnchoredMatching`, an initial `ExactTypeTransport`, and exact transport at every requested `n : Nat`.

### `forwardOnly`

Source-to-target totality exists while backward totality fails. The result carries a forward structural injection and a constructive refutation of every compatible exact alignment.

### `backwardOnly`

The symmetric case.

### `noDirectionalMatching`

Neither directional totality exists relative to the considered context. The certificate refutes both directional matchings and compatible exact alignment.

This last status does not mean that the two systems are unrelated in every possible sense. It states precisely that no total anchored matching exists in the chosen interface.

---

## 11. Directional persistence of genesis

Propagation of newly generated identities does not require an initial bijection.

A merely injective initial map can be lifted recursively by:

```lean
DirectionalGenesisPersistence.liftMap
```

If the initial map is injective, its lift remains injective for every `depth : Nat`:

```lean
liftMap_injective
```

It preserves every genesis stratum and commutes with canonical extensions:

```lean
liftMap_preservesGenesis
liftMap_embedFrom
```

A `ForwardAnchoredMatching` therefore yields an injective genesis embedding at every natural depth without manufacturing a backward transport.

Profile separation makes the initial directional matching pointwise unique. This canonicity propagates to every lift:

```lean
forwardMatching_pointwise_unique
finiteForwardEmbedding_pointwise_unique
```

with symmetric backward versions.

In the exact regime, the directional embeddings agree pointwise with the two directions of the reconstructed exact transport.

---

## 12. Reconstruction chain obtained

The formal chain can now be read as:

```text
local relations
        ↓
observations from shared anchors
        ↓
separating profiles
        ↓
Matches relation
        ↓
uniqueness of counterparts
        ↓
constructive totality or executable search
        ↓
directional classification
        ↓
exact / forwardOnly / backwardOnly / noDirectionalMatching
        ↓
exact transport or directional injection
        ↓
canonical propagation of genesis
        ↓
coherence at every requested depth n : Nat
```

This branch complements the historical direction:

```text
shared index already given
        ↓
induced transports
        ↓
naturality
```

with a partial reverse reconstruction:

```text
compatible relational structure
        ↓
initial matching reconstructed or refuted
        ↓
exact initial transport when justified
        ↓
canonical genesis transport
```

---

## 13. What remains open

The new layer substantially weakens the assumption that a shared index is already available, but it does not eliminate all shared structure.

The following remain supplied:

- the common `Anchor` type
- `sourceAnchor` and `targetAnchor`
- the common `Value` type
- the two local relations
- proofs that anchored profiles separate identities
- for executable search, complete finite listings and decidable equality on `Value`

The next structural problem is therefore more precise than before:

> **Under what conditions can the shared anchors, or an equivalent observation structure, themselves be reconstructed from systems presented without this relational mediator?**

The development also does not prove:

- that this interface is minimal among all possible alignment theories
- that roles, readouts, values, statuses, norms, or semantic properties are automatically transported
- that a concrete object at an `omega` stage is constructed
- that executable classification applies to non-enumerable carriers
- that this is a general theory of behavioral alignment for trained AI systems

These limits do not weaken the exact result obtained. They identify the next reconstruction boundary.

---

## 14. Lean API map

| Mathematical role | Lean declaration |
|---|---|
| preservation of all genesis strata | `Alignment.GenesisReconstruction.PreservesGenesis` |
| canonical lift from the base | `Alignment.GenesisReconstruction.liftToDepth` |
| reconstruction of initial transport | `Alignment.GenesisReconstruction.reconstructInitial` |
| genesis / reconstructibility characterization | `Alignment.GenesisReconstruction.preservesGenesis_iff_reconstructible` |
| initial rigidity | `Alignment.GenesisReconstruction.InitialForwardRigid` |
| rigidity at natural depth | `Alignment.GenesisReconstruction.GenesisForwardRigid` |
| profile separation | `Alignment.GenesisReconstruction.ProfileSeparates` |
| shared anchored relational context | `Alignment.GenesisReconstruction.AnchoredRelationContext` |
| observation-defined matching | `AnchoredRelationContext.Matches` |
| constructive bidirectional totality | `Alignment.GenesisReconstruction.TotalAnchoredMatching` |
| reconstructed exact transport | `TotalAnchoredMatching.toExactTransport` |
| constructive finite enumeration | `FiniteAnchoredMatchSearch.FiniteListing` |
| forward totality check | `FiniteAnchoredMatchSearch.forwardTotalCheck` |
| backward totality check | `FiniteAnchoredMatchSearch.backwardTotalCheck` |
| complete forward decision | `FiniteAnchoredMatchDecision.forwardTotalCheck_true_iff_nonempty` |
| complete backward decision | `FiniteAnchoredMatchDecision.backwardTotalCheck_true_iff_nonempty` |
| four-regime classification | `FiniteAlignmentClassification.classify` |
| directional genesis embedding | `DirectionalGenesisPersistence.FiniteGenesisEmbedding` |
| uniqueness of forward matching | `DirectionalGenesisPersistence.forwardMatching_pointwise_unique` |
| uniqueness of forward lift | `DirectionalGenesisPersistence.finiteForwardEmbedding_pointwise_unique` |

---

## 15. Theoretical reading

The result does not say that two systems become aligned merely because a bijection exists between their carriers.

It establishes a more restrictive chain:

```text
sufficiently discriminating relations
+
compatible anchored references
        ↓
structural correspondence defined
        ↓
existence or non-existence decidable in the enumerable case
        ↓
exact transport only when both directions are justified
        ↓
canonical propagation of genesis
```

Constitutive alignment therefore gains a layer of **reconstruction of alignability**. Correspondence is no longer only transported from a shared index already assumed. In the formalized relational setting, it can be reconstructed, classified, propagated, or constructively refuted.