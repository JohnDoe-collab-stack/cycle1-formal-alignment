# Structural foundations — relative alignment and representation boundary

**English** | [Français](README_fr.md)

> **This repository builds and machine-checks in Lean a constructive,
> dependently typed foundation for relative alignment, together with an autonomous representation-boundary result.** It first
> proves exact adequacy between an operational regime and an independently
> defined norm on the same constituted histories. From that established
> adequacy, one branch constructs a one-occurrence operational exit which, like
> every rooted generated history, admits an exact concrete realization in every
> supplied algebra; the other observes the two witness families
> propositionally, transports
> their equivalence into a representation layer, and proves that exact
> representation of those determined statuses is compatible with a constructed
> diagonal status outside global representation closure of the evaluator.

## Theoretical unit

The theoretical unit of this project is neither a particular layer nor a final
result, but the demonstrated continuity of a single determination across
several distinct and interdependent layers. Roles are established before their
representations, transported without merging the layers, and only then made
available to independent readouts. This organization requires a global
interpretation of local results.

## Machine-checked entry point

[`StructuralEntrypoint.lean`](StructuralEntrypoint.lean) is the shortest route
to the central circular-instance result. Its generic local-to-global entry theorem shows
that exact local realization reconstructs the canonical perimeter as an initial
factor of any rooted generated history; injectivity is derived from exact
agreement rather than assumed. A second entry point combines the canonical
perimeter, its operational and normative adequacy, and a one-occurrence
continuation which, like every rooted generated history, admits an exact
concrete realization in every supplied algebra and lies outside both regime and
specification. The same continuation instantiates the content-independent
`ExactOneStepConstitutiveAlignment`: its occurrence carrier splits exactly into
the prior occurrences and one fresh occurrence, while each supplied algebra
provides a separate exact carrier realization. At that abstract level this
asserts no independent preservation of labels, order, or step semantics; the
canonical instance additionally proves that its induced old and fresh elements
are the native concrete occurrences. The induced transports preserve both
parts and compose pointwise without an independently supplied pairwise
matching. A third entry point exposes the canonical inhabitant of a structural
bus whose correspondences are mutually inverse; the interface itself does not
assert that its inhabitant is canonical or unique. Arbitrary readouts are
attached only after that bus has been constituted, independently of their value
type. Two supplied concrete realizations are coordinated through the same
perimeter identities rather than by an additional pairwise matching; this gives
exact co-indexation and lossless readout reindexing, but does not assert semantic
compatibility between independently supplied values. Both transports are
pointwise independent of any intermediate realization.

The one-step result is also iterated over the actual circular producer at every
finite depth. Each generated stage adds exactly one fresh occurrence while
retaining all earlier occurrences. Extension through later stages commutes
pointwise with change of exact concrete realization, and both vertical and
horizontal transports are independent of intermediate stages. The vertical
extension is also pointwise independent of the proof-relevant
`DepthExtension` witness, including when its source and target use different
supplied realizations. At depth one, both directions of horizontal transport,
the realized fresh identity, and the vertical old map agree pointwise with the
earlier one-step interface. Readouts remain
downstream: a non-constant executable example preserves values `7` and `11`
from the perimeter and fresh values `10`, `20`, and `30` through three steps in
both the free and logged realizations. This finite theorem does not formalize a
transformer or impose agreement between independently supplied readouts.

## Architecture

```text
structural foundation
  relational constitution
  → dependently typed construction
  → faithful realization
  ↓
Circular instance — relative alignment
  operational regime and independent norm
  → exact adequacy
  → finite persistence / realization transport / naturality
  → one-occurrence continuation and localized operational exit

RepresentationBoundary.DiagonalizationKernel
  evaluator → diagonal status → non-representability
  → failure of global representation closure

circular regime/specification adequacy ───────────────────────────┐
                                           ├─→ RepresentationBoundary.CircularStatusRepresentation
DiagonalizationKernel ─────────────────────┘
  exact representation of selected statuses
  + diagonal representation exit
```

The continuation and dynamic alignment are proved without importing
`RepresentationBoundary`. The diagonal kernel is autonomous and imports only
`Init`. The circular-status representation module is a separate application: it
uses the already established circular regime/specification proposition-level adequacy together with
the diagonal kernel. No theorem identifies the operational exit with the
representation exit.

## Circular instance — relative alignment

For a circular presentation `P` and a rooted generated history `H`, circular instance
keeps three witness families distinct:

```text
F_A(H) := ExactConcreteRealization A H
R(H)   := CircularRefinement P H
S(H)   := CircularSpecificationSatisfaction P H
```

`F_A(H)` certifies exact realization in a supplied concrete algebra. `R(H)` is
admission by the operational regime. `S(H)` is satisfaction of a norm defined
independently of that regime.

In the circular instance, `R(H)` and `S(H)` each hold exactly when
`H = perimeterDeployment P`. They are therefore coextensive on histories, even
though their witness types, definitions, and proof routes remain distinct.

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
Once such an algebra has been supplied, exact realization is a uniform
preservation guarantee rather than a condition selecting histories; the
upstream obligation is the construction of the algebra satisfying the
interface.
Nevertheless, both `R(h⁺)` and `S(h⁺)` are constructively refuted. These
refutations are relative to the supplied `CircularPresentation`, in particular
its explicit `rejectInitialContraction` field. The normative refutation is
direct: it does not infer failure of the independent norm merely from rejection
by the regime.

The generic structures `RegimeExit`, `UniformRegimeExit`, and
`NormativeAdequacy` isolate the reusable architecture. The first two are
polymorphic over their carrier. The current normative interface is parametric
in norm and regime but specialized to `RootedGeneratedHistory P`.

## Representation boundary

The representation-boundary branch is not a second stage of alignment. It first
observes the already established circular regime/specification witness families propositionally:

```text
CircularRegimeStatus P H
  := Nonempty (CircularRefinement P H)

CircularSpecificationStatus P H
  := Nonempty (CircularSpecificationSatisfaction P H)
```

Using the two circular regime/specification witness maps, `circularStatusAdequacy` proves their proposition-level
equivalence. After a decoder pulls those statuses back to predicates on codes,
`transportRepresentation` transports exact representation along that equivalence.

Independently, `RepresentationBoundary.DiagonalizationKernel` defines, for any
evaluator `eval : Code → Code → Prop`,

```lean
diagonalStatus eval code := ¬ eval code code
```

and proves constructively that this predicate is not internally representable.
Consequently `noGlobalRepresentationClosure` refutes representation of every
predicate on the evaluator's own code space.

`localExactRepresentation_hasDiagonalExit` combines the two independent facts:
the selected circular regime status and its equivalent normative status are
represented exactly, while the evaluator's diagonal status remains outside
internal representability.

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
| diagonal status → failure of global closure | verified | `noGlobalRepresentationClosure` |

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
- [circular instance — Relative alignment](docs/en/relative_alignment.md) — detailed
  proof, signatures, adequacy, and operational exit.
- [Method of relational constitutive roles](docs/en/relational_constitutive_roles_method.md)
  — reusable construction, separation, and reconstruction method.
- [Representation boundary](docs/en/representation_boundary.md) — local exact
  representation, diagonalization, and global representation non-closure.
- [Build and axiom audit](audit/AUDIT_BUILD.txt) — reproducible factual record.
- [Authorship disclosure](AI_AUTHORSHIP.md) — conceptual authorship,
  AI-generation provenance, and development history.

French counterparts are linked from the top of every scientific document.

## Source architecture

- [`SegmentedResidualRole.lean`](SegmentedResidualRole.lean) isolates the
  dependencies consumed by the abstract residual-occurrence result,
  characterizes exact reconstruction, and preserves the existing rich API.
- [`SegmentedResidualRoleStrictness.lean`](SegmentedResidualRoleStrictness.lean)
  gives a positive separator: the weak kernel produces its unique residual
  occurrence although no exact internal realization exists on the separator
  types.
- [`AbstractSegmentedTurning.lean`](AbstractSegmentedTurning.lean) defines exact
  regime classification and typed exits.
- [`ExactTypeTransport.lean`](ExactTypeTransport.lean) isolates constructive
  two-sided exact transports independently of circular-instance content.
- [`MediatedTransitionCoherence.lean`](MediatedTransitionCoherence.lean)
  provides the independent constructive kernel for observed commutation,
  local-reflection upgrades, sequential composition, and square pasting.
- [`StrongPerimetralTurning.lean`](StrongPerimetralTurning.lean) implements the
  circular construction, independent norm, relative adequacy, and canonical
  operational exit.
- [`Alignment/Constitutive.lean`](Alignment/Constitutive.lean) defines the
  content-independent exact one-step alignment and derives naturality,
  path coherence, and relative pointwise uniqueness.
- [`Alignment/FinitePersistence.lean`](Alignment/FinitePersistence.lean)
  derives finite vertical persistence, horizontal realization transport, and
  their commuting square from one shared constitutive index.
- [`Alignment/ReadoutPersistence.lean`](Alignment/ReadoutPersistence.lean)
  attaches finite readouts afterward and proves persistence of every
  distinction they already make.
- [`Alignment/MediatedTransitionCoherence.lean`](Alignment/MediatedTransitionCoherence.lean)
  realizes finite-alignment naturality as an instance of the independent
  mediated-transition kernel.
- [`Alignment/MediatedTransitionPasting.lean`](Alignment/MediatedTransitionPasting.lean)
  pastes adjacent finite naturality squares without requiring intermediate
  faithfulness.
- [`StrongPerimetralTurning/ConstitutivePersistence.lean`](StrongPerimetralTurning/ConstitutivePersistence.lean)
  constructs the canonical one-step persistence and instantiates the abstract
  alignment while keeping admission and specification status separate.
- [`StrongPerimetralTurning/IteratedConstitutivePersistence.lean`](StrongPerimetralTurning/IteratedConstitutivePersistence.lean)
  instantiates finite persistence with the real `generate`/`appendGenerated`
  histories and their native free and concrete occurrences.
- [`StructuralEntrypoint.lean`](StructuralEntrypoint.lean) is the human-scale
  facade that presents the verified structural junctions without becoming a
  dependency of their proofs.
- [`Examples/Alignment/IteratedReadout.lean`](Examples/Alignment/IteratedReadout.lean)
  computes and proves a non-constant readout across three generated stages and
  two distinct concrete realizations.
- [`Examples/ConcreteContinuation/LoggedAlgebra.lean`](Examples/ConcreteContinuation/LoggedAlgebra.lean)
  supplies a constructive, observable, non-identity
  `ConcreteContinuationAlgebra` without becoming a dependency of the
  structural foundation or facade.
- [`RepresentationBoundary/DiagonalizationKernel.lean`](RepresentationBoundary/DiagonalizationKernel.lean)
  implements the abstract constructive diagonal kernel using only `Init`.
- [`RepresentationBoundary/CircularStatusRepresentation.lean`](RepresentationBoundary/CircularStatusRepresentation.lean)
  applies the representation boundary to proposition-level circular statuses.
- [`RepresentationBoundary.lean`](RepresentationBoundary.lean) is the import-only
  public aggregator for the representation-boundary branch.

No `Alignment/*` or `StrongPerimetralTurning/*Persistence` module imports `RepresentationBoundary`.

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

On Windows, use PowerShell 7:

```powershell
pwsh -NoProfile -File scripts/verify-manifest.ps1
```

or Windows PowerShell:

```powershell
powershell.exe -NoProfile -ExecutionPolicy Bypass -File scripts/verify-manifest.ps1
```

`MANIFEST.sha256` covers the published Lean sources and the canonical
scientific documents listed in it. Repository metadata and access documents,
including these READMEs, are outside that scientific-source manifest.
Specifically, the manifest does not hash-anchor `lean-toolchain`,
`lakefile.toml`, `lake-manifest.json`, the CI
workflow, `audit/AUDIT_BUILD.txt`, the `MANIFEST.sha256` file itself, or either
README. Their identity is therefore fixed by the audited Git commit, not by
`MANIFEST.sha256`.

Every Lean source ends with an explicit `#print axioms` block. The production
library and the constructive regression library are compiled with:

```bash
lake build
lake build AuditRegression
```

## Scope, license, and citation

The circular instance is complete relative to `CircularPresentation`; it is not a universal
theory of every norm or alignment problem. `RepresentationBoundary` is an
autonomous abstract semantic diagonal argument, not a formalization of syntax,
provability, arithmetization, or Gödel's incompleteness theorems. The source
declarations of both branches are constructive
and use no `sorry`, `admit`, declared `axiom`, `noncomputable` declaration,
`Classical`, `propext`, or `Quot.sound`. Lean may generate auxiliary declarations
internally; the declarations named in the source audit blocks have no axiomatic
dependency.

The repository is a standalone artifact: no private source history is required
to build or inspect it. Code and documentation are distributed under Apache-2.0.
Citation metadata is provided in [`CITATION.cff`](CITATION.cff).

## Authorship

> **Conceptual-authorship and AI-generation disclosure.** The project owner
> declares that the project's essential ideas and research direction are their
> own. Every part of this repository was written from start to finish by models
> in OpenAI's ChatGPT model series, under human direction and through successive
> interactions. See the [full bilingual declaration](AI_AUTHORSHIP.md).
