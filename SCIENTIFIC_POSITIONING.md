# Scientific positioning

The detailed theoretical presentation in English is maintained in [LONG_PRESENTATION.md](LONG_PRESENTATION.md).

## 1. Object of the work

This work develops a **constitutive theory of relational determination**.

Its primary problem is not how to represent an object, assign it a value, compare two of its manifestations, or transport an identifier that is already available. It addresses an earlier question:

> **What makes it possible for an occurrence to be determined as this occurrence within a construction, and then to be followed as the same determination when the construction or its realization changes?**

The theory therefore imposes an order of dependency. Constitution precedes representation. The determination of an occurrence precedes its indexing. The identity to be followed must be constituted before its persistence can be demonstrated. Alignment then appears as the coherence of the transports through which that already constituted identity is followed.

```text
constitution
        ↓
relational constitutive roles
        ↓
dependency analysis
        ↓
reconstruction
        ↓
constitutive whole
        ↓
continuation
        ↓
new occurrence
        ↓
residual
        ↓
regime boundary
        ↓
identity
        ↓
persistence
        ↓
alignment
```

The scientific object of the work is therefore not an isolated notion of totality, closure, boundary, or identity. It lies in **the constructive order that connects these notions**.

## 2. Method for determining dependencies

The project seeks to avoid introducing a useful property as primitive merely because it makes a proof easier.

Its method is:

```text
weaken
→ separate
→ reconstruct
```

One starts from a structure in which a result is provable. Some data are then removed. If the result remains derivable, those data are not necessary at that level. If it ceases to be derivable, separating models are used to establish precise non-implications. Additional conditions can then be reintroduced in order to show that a richer structure can be reconstructed from them.

This method does not claim absolute minimality among all possible formalizations. Its aim is to make the effective dependency order explicit within the constructions under study.

This methodological requirement is central: the whole, the new occurrence, the boundary, and identity must not be presupposed in order to explain the structures on which they depend.

## 3. Central constitutive mechanism

### 3.1 From local determination to the constitutive whole

Circularity is the central instance in which the architecture is currently realized in its most complete form.

Within a genuinely generated history, local constitutive exactness makes it possible to reconstruct more structure than is primitively required. Under the appropriate conditions, injectivity, order, and adjacency become derivable. Exact occurrences then support a recursive factorization of the history and the reconstruction of a **canonical perimeter as an initial factor**.

This reconstruction is structural. It does not primitively rely on numerical length.

The reconstructed perimeter delimits the internal roles already realized, distinguishes already constituted occurrences from occurrences introduced by a continuation, provides the canonical representative relative to which the regime is classified, and later supplies the initial carrier for the theory of persistence.

It thereby constitutes a **constitutive whole**:

> **a structural unity whose constitutive relations suffice to canonically determine their own domain of interiority.**

Its completeness is positive. It means that the internal domain is sufficiently determined to be recognized as such. It does not mean that every possibility of construction has been exhausted.

```text
constitutive completeness
≠
exhaustion of constructibility
```

The same construction can continue strictly beyond the perimeter. The constitutive whole is therefore not defined by the absence of an outside. It is defined by the determination of its inside, and that determination makes it possible to identify what later appears as new relative to it.

### 3.2 From the whole to the residual and the boundary

The continuation does not merely supply an additional element. It appears relative to an already constituted inside.

The factorization of the perimeter and its continuation makes it possible to distinguish old from new. Under the required faithfulness conditions, a new occurrence cannot reoccupy an internal role that has already been realized. Contractibility of the residual role then forces the new roles toward the same distinguished role. When the labelling is injective, the corresponding occurrence is unique.

```text
constitutive whole
        ↓
determined internal domain
        ↓
strict continuation
        ↓
new relative to the internal domain
        ↓
residual role
        ↓
unique residual occurrence
```

The residual is therefore neither a mere remainder nor an outside posited in advance. It has a determined constitutive provenance.

The positive continuation then supports the construction of a boundary interpretation and a totalization attempt. In the circular instance, this totalization would seek to absorb the residual into a complete closure of the same regime. Such an absorption would contract a constitutive difference preserved by the construction. The obstruction rejects that possibility.

The result is an exact classification:

```text
admission in the regime
↔
equality with the canonical perimeter
```

The resulting boundary is therefore not the point at which construction becomes impossible. Construction continues. What does not continue is **the constitutive regime itself**.

The perimeter is maximal relative to the regime:

```text
strict extension possible
        ↓
but
        ↓
no strict extension
remains in the same regime
```

The boundary is produced by the combination of two positive facts: the constitutive completeness of the internal domain and the effective possibility of continuation.

### 3.3 From the boundary to identity

The residual occurrence does not disappear once the boundary has been established.

In the canonical constitutive transition, the occurrences of the extension split into all prior occurrences and one fresh occurrence. The development proves that this fresh identity is **exactly the residual occurrence determined by the preceding mechanism**.

```text
residual occurrence
determined at the boundary
        =
fresh identity
of the constitutive transition
```

The fresh identity therefore has a provenance. It is not introduced as a new name or as an arbitrary identifier. It is the occurrence whose novelty relative to the whole has already been determined, whose residual role has been established, and whose uniqueness has been proved.

The project therefore does not begin with a given identity and ask how it persists. It first constructs **the genesis of the determination that will become that identity**.

## 4. Persistence and alignment

Once identity has been constituted, the problem becomes one of tracking it.

The first axis is extension of the construction. Already constituted identities are injected into later depths. Each transition may introduce a fresh identity. Identities introduced at different depths remain distinct when transported into a common later depth.

The second axis is change of realization. Different concrete realizations are coordinated through the same constitutive index. Transport between them is therefore not obtained through an independent matching of concrete objects.

These two axes satisfy a naturality law: extending an identity and then changing realization gives the same result as changing realization and then extending that identity.

Alignment then becomes a derived notion:

> **the coherence of the transports through which an already constituted identity remains tracked across extensions and distinct realizations.**

Bijective exactness alone is not sufficient. The relevant transport must respect the indexing induced by constitution.

The complete chain is therefore:

```text
constitution of the whole
        ↓
determination of the new
        ↓
residual
        ↓
regime boundary
        ↓
genesis of identity
        ↓
persistence
        ↓
coherence of transports
```

## 5. Formal abstraction

The mechanism obtained in the circular instance does not depend entirely on that geometry.

[`AbstractSegmentedTurning.lean`](AbstractSegmentedTurning.lean) explicitly removes the circular presentation, provenance, endpoint difference, loop, and final junction. The module nevertheless retains a boundary generator, strict continuation, residual determination, regime analysis, totalization attempt, and obstruction.

The abstract result provides, among other things, a unique residual occurrence, exact classification relative to the canonical boundary, a continuation strictly distinct from that boundary, a proof that the continuation lies outside the regime, and the impossibility of a strict extension remaining in the regime.

Circularity should therefore be understood as **the rich constitutive instance in which the mechanism is discovered and realized**, not as a universal hypothesis imposed on every future application.

The principal formal connections are exposed in:

- [`StrongPerimetralTurning.lean`](StrongPerimetralTurning.lean) for perimeter reconstruction, continuation, the residual, and regime classification
- [`SegmentedResidualRole.lean`](SegmentedResidualRole.lean) for the residual-determination kernel
- [`AbstractSegmentedTurning.lean`](AbstractSegmentedTurning.lean) for abstraction of the boundary mechanism
- [`StrongPerimetralTurning/ConstitutivePersistence.lean`](StrongPerimetralTurning/ConstitutivePersistence.lean) for the identification of the residual with the fresh identity
- [`Alignment/FinitePersistence.lean`](Alignment/FinitePersistence.lean) for persistence uniform over every `n : Nat` and transport naturality
- [`Tests/DynamicAlignmentRegression.lean`](Tests/DynamicAlignmentRegression.lean) for counterexamples showing that exactness alone is insufficient for coherence

## 6. Comparative positioning

Several traditions already contain important elements of this architecture.

### Autopoiesis

Since the work of Varela, Maturana, and Uribe, autopoiesis has connected organizational circularity, production of unity, and self-maintenance. Later formulations have emphasized endogenous boundary production and the distinction between organization and concrete structure. General formalization of the concept remains debated. A 2012 review underlines persistent ambiguities in its definition, and a 2026 work devoted explicitly to formalization still presents a categorical-thermodynamic calculus as a program rather than as a completed formal system.

The comparison is therefore real, but the present work is not a formalization of autopoiesis and does not propose a criterion of life. Its problem is different: reconstruct a canonical constitutive domain, determine a continuation relative to that domain, and then track the new determination that results.

### Closure of constraints and relational biology

The closure-of-constraints framework of Montévil and Mossio is a particularly close formal neighbor. It characterizes biological organization through the mutual dependence and generativity of constraints, while distinguishing organizational closure from thermodynamic openness. It also provides a way to mark boundaries between interacting biological systems.

Rosen's relational biology develops another strong notion of closure, closure to efficient causation. Later work has shown that a computable expression of this closure can be given in lambda calculus.

These frameworks therefore already establish powerful notions of relational unity and closure. The differential question of the present work is: **what becomes of a determination when the constitutive domain to which it could belong has already been canonically established, yet the construction continues despite that completeness?**

### Mereology and mereotopology

Mereology and mereotopology provide rigorous theories of parts, wholes, interiors, and boundaries. They rule out presenting the constitutive whole as the first positive definition of a whole or of an interior.

The difference concerns the status of the perimeter. Here, the perimeter is not primitively a topological boundary of an already individuated object. It is the result of a reconstruction arising from the exact realization of occurrences in a generated history. It becomes a regime boundary because a strict continuation exists but can no longer receive the same constitutive status.

### Individuation and structuralism

Philosophies of individuation, especially Simondon's, already reject the idea that the individual is a given substance and describe the genesis of new individuations from a metastable preindividual field. The present work shares the emphasis on genesis, but its residual has a different provenance: it appears after the constitution of a canonical internal domain and is determined relative to that domain.

Mathematical structuralism, for its part, holds that an object's identity may depend on its position and relations within a structure. Category theory has long provided the tools of composition and naturality needed to study coherent transports. The project makes no claim of novelty for these notions in isolation. Its question lies upstream: **how does the identity that will later be transported acquire its constitutive provenance?**

## 7. Theoretical differential

After comparison, the contribution cannot honestly be located in any one of the following claims:

```text
relational whole
organizational closure
endogenous boundary
openness despite closure
relational identity
fresh element
transport
naturality
```

All have serious precedents.

The clearest differential appears in their dependency order:

```text
local determinations
        ↓
canonical reconstruction of the domain
        ↓
constitutive whole
        ↓
continuation produced by the same construction
        ↓
new determined relative to the whole
        ↓
unique residual
        ↓
failure of its totalization in the same regime
        ↓
exact constitutive boundary
        ↓
residual = fresh identity
        ↓
coherent persistence of that identity
```

This proposal connects three problems that are often treated separately:

1. constitution of an internal domain
2. determination of what appears as new relative to that domain
3. later persistence of that new determination

This articulation is currently the most precise originality claim of the work.

## 8. Proposed contribution

The project can therefore be presented as a **constructive theory of the genesis and persistence of a relational determination**.

Its central contribution lies in four connected conceptual results:

1. a constitutive domain can be obtained by reconstruction from local determinations rather than assumed as a primitive totality
2. its constitutive completeness can coexist with continued construction, making it possible to determine something new positively relative to an already constituted interior
3. this new occurrence can receive a residual determination whose impossibility of totalization within the same regime yields an exact boundary
4. this same residual occurrence becomes the fresh identity of the transition and can then be tracked across extensions and changes of realization by coherent transports

The central proposal can be stated as follows:

> **A persistent identity can be understood as the coherent continuation of a determination whose genesis has itself been established relative to a constitutive whole.**

## 9. Scope and limits

A substantial part of this architecture is formalized in Lean.

The development establishes, among other things, reconstruction and the role of the perimeter in the circular instance, residual determination, strict continuation, exact classification of an obstructed regime, impossibility of a strict extension remaining in the same regime, the connection between residual and fresh identity, persistence uniform for every `n : Nat`, and naturality between extension and change of realization.

This scope must remain precisely delimited.

- The proved persistence is uniform for every `n : Nat` and imposes no maximum depth. The repository does not, however, construct a concrete carrier at an `ω` stage.
- The **constitutive whole** is a theoretical reading of precise formal structures and theorems. It is not introduced as a universal metaphysical predicate independent of the development.
- Circularity remains the central instance in which the complete architecture is realized, even though the boundary mechanism has already been partially abstracted away from that geometry.
- The formal development does not by itself establish a general biological theory.
- The comparison conducted here defines a precise conceptual differential. It does not constitute an exhaustive proof of historical priority.

## 10. Synthetic positioning

The work studies **how a domain of relational determinations becomes a constitutive whole, how continuation of that same construction makes something new appear relative to that whole, how the impossibility of reabsorbing that new occurrence into the same regime produces a boundary, and how that same new determination then becomes the identity whose persistence can be coherently tracked.**

In the frameworks examined, the principal concepts in this chain have important precedents when considered separately.

The distinctive point lies in their order of genesis and in the formal connections that join them:

```text
constituted whole
→ determined new
→ boundary
→ identity
→ persistence
```

This is the level at which the project's scientific contribution is currently situated.

## Comparative references

- Varela, F. G., Maturana, H. R., Uribe, R. (1974). *Autopoiesis: The organization of living systems, its characterization and a model*. Current Modern Biology 5(4), 187-196. https://doi.org/10.1016/0303-2647(74)90031-8
- Razeto-Barry, P. (2012). *Autopoiesis 40 years later. A review and a reformulation*. Origins of Life and Evolution of Biospheres 42(6), 543-567. https://doi.org/10.1007/s11084-012-9297-y
- Montévil, M., Mossio, M. (2015). *Biological organisation as closure of constraints*. Journal of Theoretical Biology 372, 179-191. https://doi.org/10.1016/j.jtbi.2015.02.029
- Letelier, J.-C., Cárdenas, M. L., Cornish-Bowden, A. (2009). *A computable expression of closure to efficient causation*. Journal of Theoretical Biology 257(3), 489-498. https://doi.org/10.1016/j.jtbi.2008.12.012
- Smith, B. (1996). *Mereotopology: A theory of parts and boundaries*. Data & Knowledge Engineering 20(3), 287-303. https://doi.org/10.1016/S0169-023X(96)00015-8
- *Structuralism in the Philosophy of Mathematics*. Stanford Encyclopedia of Philosophy, substantive revision 2025. https://plato.stanford.edu/entries/structuralism-mathematics/
- *Formalizing autopoiesis: Toward a Categorical-Thermodynamic Calculus of Closure*. BioSystems 268, 105918 (2026). https://doi.org/10.1016/j.biosystems.2026.105918
