# Structural foundations — relative and reflective alignment

**English** | [Français](README_fr.md)

> **This repository builds and machine-checks in Lean a constructive,
> dependently typed foundation for relative and reflective alignment.** It first
> proves exact adequacy between an operational regime and an independently
> defined norm on the same constituted histories. From that established
> adequacy, one branch constructs a one-occurrence operational exit which, like
> every rooted generated history, admits an exact concrete realization in every
> supplied algebra; the other observes the two witness families
> propositionally, transports
> their equivalence into a representation layer, and proves that exact
> representation of those determined statuses is compatible with a constructed
> diagonal status outside every global reflective closure of the evaluator.

## Machine-checked entry point

[`StructuralEntrypoint.lean`](StructuralEntrypoint.lean) is the shortest route
to the central Cycle 1 result. Its generic local-to-global entry theorem shows
that exact local realization reconstructs the canonical perimeter as an initial
factor of any rooted generated history; injectivity is derived from exact
agreement rather than assumed. A second entry point combines the canonical
perimeter, its operational and normative adequacy, and a one-occurrence
continuation which, like every rooted generated history, admits an exact
concrete realization in every supplied algebra and lies outside both regime and
specification. A third exposes the canonical inhabitant of a structural bus
whose correspondences are mutually inverse; the interface itself does not
assert that its inhabitant is canonical or unique. Arbitrary readouts are
attached only after that bus has been constituted, independently of their value
type.

## Architecture

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

The split occurs after Cycle 1 adequacy. The diagonal development does not
follow from `oneStepAfterPerimeter`, and no theorem identifies the operational
exit with the representational one.

## Cycle 1 — Relative alignment

For a circular presentation `P` and a rooted generated history `H`, Cycle 1
keeps three witness families distinct:

```text
F_A(H) := ExactConcreteRealization A H
R(H)   := CircularRefinement P H
S(H)   := CircularSpecificationSatisfaction P H
```

`F_A(H)` certifies exact realization in a supplied concrete algebra. `R(H)` is
admission by the operational regime. `S(H)` is satisfaction of a norm defined
independently of that regime.

The proof constructs two maps between witness types:

```text
R(H) → S(H)                         soundness
S(H) → H = perimeterDeployment P    carrier completeness
S(H) → R(H)                         regime completeness
```

`circularNormativeAdequacy` defines adequacy as a pair of maps in these two
directions, and `circularRefinement_adequateAlong` supplies that pair at every
occurrence. This is not an equality or an `Equiv` between the proof-relevant
witness structures.

The canonical candidate

```text
h⁺ := oneStepAfterPerimeter P
```

is a strict continuation of the canonical deployment. It remains locally exact,
preserves canonical precedence and adjacency, and has an
`ExactConcreteRealization A h⁺` for every supplied
`ConcreteContinuationAlgebra P`, as does every rooted generated history.
Nevertheless, both `R(h⁺)` and `S(h⁺)` are constructively refuted. These
refutations are relative to the supplied `CircularPresentation`, in particular
its explicit `rejectInitialContraction` field. The normative refutation is
direct: it does not infer failure of the independent norm merely from rejection
by the regime.

The generic structures `RegimeExit`, `UniformRegimeExit`, and
`NormativeAdequacy` isolate the reusable architecture. The first two are
polymorphic over their carrier. The current normative interface is parametric
in norm and regime but specialized to `RootedGeneratedHistory P`.

## Cycle 2 — Reflective alignment

Cycle 2 first turns the Cycle 1 witness families into propositions:

```text
CircularRegimeStatus P H
  := Nonempty (CircularRefinement P H)

CircularSpecificationStatus P H
  := Nonempty (CircularSpecificationSatisfaction P H)
```

Using the two Cycle 1 maps, `circularStatusAdequacy` proves:

```text
CircularRegimeStatus P H
  ↔ CircularSpecificationStatus P H
```

This `↔` is an equivalence of inhabitability, not an equivalence of the original
witness types. After a decoder pulls the statuses back to predicates on codes,
exact representation transports between them.

Independently, for any evaluator

```lean
eval : Code → Code → Prop
```

the diagonal kernel defines

```lean
diagonalStatus eval code := ¬ eval code code
```

and proves constructively that no row of `eval` represents this predicate
exactly. Hence an evaluator of this shape cannot represent every predicate on
its own code space. `exactCircularStatusRepresentation_hasDiagonalOutside`
combines the two results: the selected regime status and its equivalent
normative status are represented exactly, while the evaluator's diagonal status
remains outside internal representability.

## What is established

| Transition | Status | Main Lean anchor |
|---|---|---|
| constitution → history | verified | `RootedGeneratedHistory` |
| structural roles → exact realization | verified | `ExactNonClosingRealization` |
| free history → faithful concrete realization | verified | `exactlyInterpretHistory` |
| regime witness → norm witness | verified | `circularRefinement_soundSpecification` |
| norm witness → regime witness | verified | `circularSpecification_complete` |
| adequacy → proposition-level status equivalence | verified | `circularStatusAdequacy` |
| continuation → operational exit | verified | `oneStepAfterPerimeter`, `RegimeExit` |
| equivalent coded statuses → transported representation | verified | `transportRepresentation` |
| evaluator → non-representable diagonal status | verified | `diagonalStatus_notRepresentable` |
| diagonal status → failure of global closure | verified | `noGlobalReflectiveClosure` |

The architectural conclusion drawn from this chain is stated separately from
the Lean theorems: global closure is not treated merely as a failed objective,
but is superseded by an architecture in which non-closure is constitutive,
boundaries are determined relative to explicit regimes, and construction can
continue beyond them.

## Distinctions preserved

```text
construction ≠ faithful realization
faithful realization ≠ admission by a regime
regime ≠ independent norm
norm ≠ proof of adequacy
operational exit ≠ representational exit
abstract diagonalization ≠ Gödel's incompleteness theorems
Lean result ≠ derived consequence ≠ architectural interpretation
```

Structural OOD is proposed here as the case of an internally constructible
candidate lying outside an explicit operational regime. It is not identified
with statistical OOD or with relative misalignment. In the circular instance,
the same candidate additionally carries exact realization and a direct proof of
failure of the independent norm.

## Documentation

- [Structural foundations](docs/en/structural_foundations.md) — canonical
  synthesis of the complete architecture.
- [Cycle 1 — Relative alignment](docs/en/relative_alignment.md) — detailed
  proof, signatures, adequacy, and operational exit.
- [Method of relational constitutive roles](docs/en/relational_constitutive_roles_method.md)
  — reusable construction, separation, reconstruction, and audit protocol.
- [Cycle 2 — Reflective alignment](docs/en/reflective_alignment.md) — exact
  representation, diagonalization, and global non-closure.
- [Constitutive neural architecture for relative alignment](docs/en/constitutive_transformer_alignment.md)
  — constructive contracts for causal memory, governed effectuation,
  succession, neural realization, and a finite hard-attention transformer
  instance with exact two-cycle feedback and normative confinement.
- [Build and axiom audit](audit/AUDIT_BUILD.txt) — reproducible factual record.
- [Finite experimental protocol](experiment/README.md) — frozen numerical
  protocol, immutable confirmatory result, controls, traces, and deferred audit.
- [Authorship disclosure](AI_AUTHORSHIP.md) — conceptual authorship,
  AI-generation provenance, and development history.

French counterparts are linked from the top of every scientific document.

## Source architecture

- [`SegmentedResidualRole.lean`](SegmentedResidualRole.lean) proves the abstract
  residual-occurrence result.
- [`AbstractSegmentedTurning.lean`](AbstractSegmentedTurning.lean) defines exact
  regime classification and typed exits.
- [`StrongPerimetralTurning.lean`](StrongPerimetralTurning.lean) implements the
  circular construction, independent norm, relative adequacy, and canonical
  operational exit.
- [`Examples/ConcreteContinuation/LoggedAlgebra.lean`](Examples/ConcreteContinuation/LoggedAlgebra.lean)
  supplies a constructive, observable, non-identity
  `ConcreteContinuationAlgebra` without becoming a dependency of the
  structural foundation or facade.
- [`Cycle2/DiagonalizationKernel.lean`](Cycle2/DiagonalizationKernel.lean)
  implements the abstract constructive diagonal kernel using only `Init`.
- [`Cycle2/ReflectiveAlignment.lean`](Cycle2/ReflectiveAlignment.lean) observes
  Cycle 1 statuses by `Nonempty` and transports their adequacy into the
  representation layer.
- [`Cycle2.lean`](Cycle2.lean) is the import-only public aggregator for Cycle 2.
- [`ConstitutiveAlignment/`](ConstitutiveAlignment) builds the abstract machine,
  causal memory, certified effectuation, typed failures, succession, one-step
  learning causality, reflective bridge, finite reference model, and neural and
  transformer realization contracts and finite transformer dynamics.
- [`ConstitutiveAlignment.lean`](ConstitutiveAlignment.lean) is the public
  aggregator for the constitutive architecture.
- [`experiment/`](experiment) contains the versioned numerical protocol; its
  observations remain separate from the Lean theorems.

No Cycle 1 module imports Cycle 2.

## Reproduction and audit

With `elan`, or an equivalent installation that reads `lean-toolchain`:

```bash
lake clean
lake build
```

Verify the scientific-source manifest on Linux or macOS:

```bash
bash scripts/verify-manifest.sh
```

On Windows PowerShell:

```powershell
pwsh -NoProfile -File scripts/verify-manifest.ps1
```

The pinned build compiles all three Lake libraries, audits 468 declarations through
the final `#print axioms` blocks, and reports no axiomatic dependency. Exact
environment, counts, hashes, and commands are recorded in
[`audit/AUDIT_BUILD.txt`](audit/AUDIT_BUILD.txt).

## Scope, license, and citation

Cycle 1 is complete relative to `CircularPresentation`; it is not a universal
theory of every norm or alignment problem. Cycle 2 is an abstract semantic
diagonal argument, not a formalization of syntax, provability, arithmetization,
or Gödel's incompleteness theorems. The formal cycles and constitutive
architecture are constructive and use no `sorry`, `admit`, declared `axiom`,
`noncomputable` declaration, `Classical`, `propext`, or `Quot.sound`. Lean does
generate auxiliary `.injEq` declarations that depend on `propext`; none of the
444 explicitly audited declarations depends on them or on any other axiom.

The repository is a standalone artifact: no private source history is required
to build or audit it. Code and documentation are distributed under Apache-2.0.
Citation metadata is provided in [`CITATION.cff`](CITATION.cff).

## Authorship

> **Conceptual-authorship and AI-generation disclosure.** The project owner
> declares that the project's essential ideas and research direction are their
> own. Every part of this repository was written from start to finish by models
> in OpenAI's ChatGPT model series, under human direction and through successive
> interactions. See the [full bilingual declaration](AI_AUTHORSHIP.md).
