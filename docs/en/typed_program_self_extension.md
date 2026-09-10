# Constitutive self-extension of typed programs

**English** | [Français](../fr/auto_extension_programmes_types.md)

Navigation: [neural architecture](constitutive_transformer_alignment.md) ·
[structural foundations](structural_foundations.md) ·
[relative alignment](relative_alignment.md)

## 1. Constructed result

The repository constructs a finite witness in which a new abstraction
positively changes the corpus that determines the next construction:

```text
T₀
→ typed frontier computed from T₀
→ proposal, certification, and incorporation of C₀
→ actually produced T₁
→ the same frontier rule applied to T₁
→ new obligation δ₁
→ second proposal, certification, and incorporation
→ T₂
```

Neither the frontier function nor `typedStep` receives a cycle rank. The second
call consumes the `T₁` produced by the first; it does not read a fixture named
“second state.”

This result connects directly to the Cycle 1 kernel: construction, admission,
norm, and adequacy remain distinct objects. Learning does not define the norm,
and proposal is not yet incorporation.

## 2. Total domain and identity by formation

`TypedProgramDomain.lean` defines two finite program types, an intrinsically
typed language, total evaluation, formation kept separately from behavior, a
positive existential abstraction carrying its interface and typed program, a
finite corpus, independently declared regime and norm witness families, and
the two adequacy transformations.

Extensional equality does not erase formation. Double negation computes the
same value as identity on every Boolean, while their formations are
constructively distinct. Conversely, composing a `pair` output with Boolean
negation returns `none`; typing is never repaired after the fact.

The frontier exhaustively enumerates corpus pairs in a fixed order, constructs
only typed compositions, and returns either the first missing formation with
presence and freshness witnesses or a finite saturation certificate.

## 3. Two passes through one operator

The canonical instance starts from the corpus containing negation alone:

```text
T₀ = [not]
frontier(T₀) = not ∘ not
T₁ = [not, not ∘ not]
frontier(T₁) = not ∘ (not ∘ not)
T₂ = [not, not ∘ not, not ∘ (not ∘ not)]
```

The same `typedStep` constructs both transitions. `TypedStep` is a positive
witness type, and `secondHistory` composes the transitions in the proof-relevant
history already used by the structural foundation.

| Obligation | Lean anchor |
| --- | --- |
| fresh first formation | `firstCertifiedAbstraction_isFresh` |
| first frontier | `firstFrontier_isDoubleNegate` |
| second frontier | `secondFrontier_isTripleNegate` |
| reconstruction of `T₁` | `firstStep_reconstructsCorpus` |
| exact consumption of `T₁` | `secondStep_consumesFirstSuccessor` |
| divergence without incorporation | `firstIncorporation_changesSecondObligation` |
| final aggregate | `compactTypedSelfExtension` |

The first counterfactual preserves acquired capacity and removes only the
incorporation of `C₀`; the frontier remains double negation rather than becoming
triple negation. The second preserves `T₁` but restores capacity from before the
second learning event; no second proposal is produced. The two causal roles are
therefore separated.

## 4. Transformer-producer connection

`programCore` is a local `TransformerCore` instance. Its proposal is a positive
`CertifiedProgramAbstraction`, not a Boolean decoded by a cycle-specific table.
The producer computes the frontier from the corpus in its view and proposes the
candidate only when acquired compositional capacity is sufficient. Total
elaboration rejects absence of a proposal or preserves the exact proposed
abstraction.

The first acquired capacity is carried by `T₁` and becomes the incoming capacity
of the second pass. The second learning event produces exactly the capacity
consumed by the second dynamics. `StrictFreshProbeCausality` constructs, on one
view, parent rejection, prediction change, exact consumption, proposal change,
and learned succession.

## 5. Generated probe and exact refinement

`GeneratedFreshProbeProtocol` carries the sealed descriptor, reserved seed,
total generator, generated value, and equality to the underlying fixed
protocol's probe. In the finite instance, triple-negation formation is
constructively absent from the training corpus, which contains only double
negation.

`TypedTraceRefinement` connects the typed executable boundary to one canonical
discrete trace by full equality. It yields exact prediction consumption and
identity between certificate status and governed effect. A rewritten proposal
or a target corpus missing the first incorporation has no such refinement.

## 6. Separate executable protocol

`experiment/typed_program/` reproduces the same chain in a JSON journal that
Lean never reads. Its worker is stateless. Training receives only the training
view, incoming capacity, and public bounds. Measurement receives a probe input
but no target and cannot update state. An independent total semantics recomputes
the expected response, and every exact worker request is recorded.

After descriptor sealing, a precommitted seed generates a deterministic bit
sequence. A cumulative ledger reserves normalized signatures of training data
and probes; any collision stops the run without resampling. The normalizer
erases technical addresses only, so coherent renaming preserves the generator
key and probe without making a prior exposure fresh again.

The development smoke test and twelve negative mutations pass. No confirmatory
result exists yet: the runner refuses that mode until the sources have been
frozen by a clean commit. Gate N will be declared closed only after that freeze,
one confirmatory run to a new path, and read-only verification.

## 7. Exact scope

Within this finite language, the Lean layer constructively establishes two
linked transitions, dependence of the second frontier on first incorporation,
dependence of the second proposal on acquired capacity, formal probe freshness,
and exact refinement of discrete traces.

It does not establish general program synthesis, learning primitives from
nothing, unbounded autonomy, or an empirical result for a production-scale
trained transformer. These exclusions specify the verified scope.

## Design

> **Intellectual-design and AI-generation disclosure.** The project lead
> states that the essential ideas and research direction are their own. This
> document was written from A to Z by models in OpenAI's ChatGPT series, under
> human direction and through successive interactions. See the
> [full bilingual disclosure](../../AI_AUTHORSHIP.md).
