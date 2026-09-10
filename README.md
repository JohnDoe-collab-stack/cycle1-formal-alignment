# Structural foundations — relative and reflective alignment

**English** | [Français](README_fr.md)

> **Conceptual-authorship and AI-generation disclosure.** The project owner
> declares that the project's essential ideas and research direction are their
> own. Every part of this repository was written from start to finish by models
> in OpenAI's ChatGPT model series, under human direction and through successive
> interactions. See the [full bilingual declaration](AI_AUTHORSHIP.md).

> **This repository builds and machine-checks in Lean a constructive,
> dependently typed foundation for relative and reflective alignment.** It first
> proves exact adequacy between an operational regime and an independently
> defined norm on the same constituted histories. From that established
> adequacy, one branch constructs a minimal, faithfully realizable operational
> exit; the other observes the two witness families propositionally, transports
> their equivalence into a representation layer, and proves that exact
> representation of those determined statuses is compatible with a constructed
> diagonal status outside every global reflective closure of the evaluator.

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
  ├── minimal continuation
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
`ConcreteContinuationAlgebra P`. Nevertheless, both `R(h⁺)` and `S(h⁺)` are
constructively refuted. The normative refutation is direct: it does not infer
failure of the independent norm merely from rejection by the regime.

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
- [Build and axiom audit](audit/AUDIT_BUILD.txt) — reproducible factual record.
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
- [`Cycle2/DiagonalizationKernel.lean`](Cycle2/DiagonalizationKernel.lean)
  implements the abstract constructive diagonal kernel using only `Init`.
- [`Cycle2/ReflectiveAlignment.lean`](Cycle2/ReflectiveAlignment.lean) observes
  Cycle 1 statuses by `Nonempty` and transports their adequacy into the
  representation layer.
- [`Cycle2.lean`](Cycle2.lean) is the import-only public aggregator for Cycle 2.

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

The pinned build compiles both Lake libraries, audits 325 declarations through
the final `#print axioms` blocks, and reports no axiomatic dependency. Exact
environment, counts, hashes, and commands are recorded in
[`audit/AUDIT_BUILD.txt`](audit/AUDIT_BUILD.txt).

## Scope, license, and citation

Cycle 1 is complete relative to `CircularPresentation`; it is not a universal
theory of every norm or alignment problem. Cycle 2 is an abstract semantic
diagonal argument, not a formalization of syntax, provability, arithmetization,
or Gödel's incompleteness theorems. The two formal cycles are constructive and
use no `sorry`, `admit`, declared `axiom`, `Classical`, `propext`, or
`Quot.sound`.

The repository is a standalone artifact: no private source history is required
to build or audit it. Code and documentation are distributed under Apache-2.0.
Citation metadata is provided in [`CITATION.cff`](CITATION.cff).
