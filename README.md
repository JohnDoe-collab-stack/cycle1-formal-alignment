# Structural foundations — constitutive determination, persistence, and relative alignment

**English** | [Français](README_fr.md)

> **This repository develops and machine-checks in Lean a constructive framework for constitutive determination, structural reconstruction, finite persistence, and coherent transport across distinct realizations.**

Objects are individuated before they are read. Their structural roles are established before representation, numerical measurement, admission status, or readout values are used. In the circular instance, exact local agreement reconstructs a canonical perimeter as an initial structural factor; a strict continuation can then be generated beyond it, its residual occurrence can be determined uniquely, and that occurrence is identified with the fresh constitutive identity whose persistence is tracked through later finite extensions.

A separate representation-boundary branch proves a constructive diagonal non-representability result. It is formally distinct from the operational exit and is not used to establish constitutive persistence.

---

## Long-form theoretical presentation

The detailed theoretical presentation in English is maintained separately:

- **[Long-form presentation — Constitutive theory of relational determination](LONG_PRESENTATION.md)**

It develops the framework in the following order:

```text
constitution
→ relational constitutive roles
→ dependency analysis
→ separation and reconstruction
→ circular instance
→ perimeter reconstruction
→ residual determination and uniqueness
→ exact regime classification
→ derived structural length
→ identity and indexing
→ finite persistence
→ alignment
```

The long-form document also makes explicit why the reconstructed perimeter matters: it delimits the already constituted internal roles, separates old occurrences from genuinely new ones, supplies the canonical reference for regime classification, and provides the initial occurrence carrier used by the persistence instance.

This README is intentionally shorter. Its role is to identify the formal core, scope, source layout, reproduction commands, and audit surfaces.

---

## Scientific positioning

This project studies how a relational structure can first canonically constitute its own internal domain, then determine what appears as new when the same construction extends beyond that domain. In the circular instance formalized here, this progression connects perimeter reconstruction, residual determination, regime boundary, the genesis of a fresh identity, and the coherent persistence of that identity. The proposed contribution therefore does not lie in an isolated notion of closure, totality, or transport, but in the formal construction of this dependency chain.

See [SCIENTIFIC_POSITIONING.md](SCIENTIFIC_POSITIONING.md) for the detailed comparative positioning.

---

## Formal core

The project separates several layers that must not be collapsed:

```text
occurrence ≠ readout
constitution ≠ realization
realization ≠ admission
admission ≠ independent norm satisfaction
identity ≠ equality of observed values
operational exit ≠ representation exit
```

The main verified structural chain in the circular instance is:

```text
exact local role/occurrence agreement
        ↓
reconstruction of the canonical perimeter as an initial factor
        ↓
strict continuation remains constructible
        ↓
old / new occurrence separation
        ↓
residual determination
        ↓
unique residual occurrence
        ↓
rejection of the positive totalization branch
        ↓
exact classification of the circular regime
        ↓
relative maximality of the perimeter
        ↓
derived structural length
```

The perimeter is not identified by its length. Structural equality/classification is established first; numerical length facts are derived afterward.

The persistence layer then continues with:

```text
unique operational residual
        =
fresh constitutive identity
        ↓
shared constitutive indexing
        ↓
finite extension
        ↓
transport between exact realizations
        ↓
composition + naturality
        ↓
relative alignment
```

An arbitrary exact bijection is not, by itself, an identity-preserving transport. The persistence theorems use transports induced through the shared constitutive index and prove the corresponding coherence laws.

---

## Theoretical vocabulary and formal status

The terms **identity**, **constitutive determination**, and **alignment** are theoretical/architectural readings constrained by explicit Lean constructions and equations.

The Lean development directly verifies the structural ingredients: occurrence individuation, exact local agreement, reconstruction, residual uniqueness, exact transports, indexed realization, injective extension, composition, naturality, readout reindexing, regime classification, and representation-boundary results.

The intended theoretical reading is:

> **Identity is the persistence of an already constituted determination through the transports that preserve its constitutive index.**

and:

> **Alignment is the coherence of those identity transports across distinct realizations and constitutive extensions.**

These sentences organize the verified results; they are not names of additional primitive predicates in Lean.

---

## Key Lean anchors

| Role | Main source |
|---|---|
| residual determination and its weak dependency core | [`SegmentedResidualRole.lean`](SegmentedResidualRole.lean) |
| strictness/separating models for the residual interface | [`SegmentedResidualRoleStrictness.lean`](SegmentedResidualRoleStrictness.lean) |
| abstract boundary/turning and obstructed-regime machinery | [`AbstractSegmentedTurning.lean`](AbstractSegmentedTurning.lean) |
| generic exact bidirectional transport | [`ExactTypeTransport.lean`](ExactTypeTransport.lean) |
| circular construction, local-to-global reconstruction, regime and specification | [`StrongPerimetralTurning.lean`](StrongPerimetralTurning.lean) |
| generic one-step constitutive alignment | [`Alignment/Constitutive.lean`](Alignment/Constitutive.lean) |
| finite indexing, extension, transport, composition and naturality | [`Alignment/FinitePersistence.lean`](Alignment/FinitePersistence.lean) |
| readouts after constitution | [`Alignment/ReadoutPersistence.lean`](Alignment/ReadoutPersistence.lean) |
| circular one-step persistence instance | [`StrongPerimetralTurning/ConstitutivePersistence.lean`](StrongPerimetralTurning/ConstitutivePersistence.lean) |
| circular finite-depth persistence instance | [`StrongPerimetralTurning/IteratedConstitutivePersistence.lean`](StrongPerimetralTurning/IteratedConstitutivePersistence.lean) |
| public structural façade | [`StructuralEntrypoint.lean`](StructuralEntrypoint.lean) |
| representation-boundary kernel | [`RepresentationBoundary/DiagonalizationKernel.lean`](RepresentationBoundary/DiagonalizationKernel.lean) |
| circular status representation | [`RepresentationBoundary/CircularStatusRepresentation.lean`](RepresentationBoundary/CircularStatusRepresentation.lean) |

Two distinct notions of exactness should be kept separate:

- **local constitutive exactness**: exact structural agreement between a role requirement and the occurrence that realizes it;
- **exact transport**: a bidirectional correspondence with pointwise round trips between carrier types.

The project uses both, but they are different formal interfaces.

---

## What the circular instance establishes

For a supplied `CircularPresentation P`:

1. non-closing perimeter roles can be realized by exact occurrences in a generated history;
2. exact local realization reconstructs the canonical perimeter as an initial factor (`ExactNonClosingRealization.toPerimeterExtension`);
3. the generator can still build `oneStepAfterPerimeter P`;
4. the new part has a uniquely determined residual occurrence;
5. admitted positive extensions generate the residual-based totalization attempt rejected by the preserved obstruction;
6. the circular regime is classified exactly by equality with `perimeterDeployment P`;
7. length inequalities/equalities are derived only after the structural prefix and classification results;
8. the one-step residual is the fresh identity of the constitutive-alignment instance;
9. that identity persists through arbitrary later finite depths and naturally across supplied exact concrete realizations.

The construction can therefore continue beyond the perimeter even though the same circular regime cannot continue with it:

```text
constructible continuation
≠
admissible continuation in the same regime
```

---

## Scope and non-claims

The verified scientific instance in this repository is circular/perimetral. The methodology extracted from it is not claimed as a universal metatheorem for every possible domain.

The persistence results are uniform over arbitrary **finite** depth. The repository does not construct an infinite history object or an ω-stage concrete carrier.

The project does **not** infer identity from equal readout values, equal cardinalities, numerical similarity, or arbitrary exact bijections.

Persistence of an occurrence identity does not automatically transport every associated property. Order, provenance, role, readout value, admission status, or another semantic property requires its own preservation theorem when such a theorem is needed.

The representation-boundary branch is separate from the operational branch. No theorem converts the operational exit into the representational diagonal exit or conversely.

Nothing in this repository, by itself, is a theorem of behavioral or normative alignment for an external trained AI system.

---

## Reproduction

The repository uses the pinned Lean toolchain declared in [`lean-toolchain`](lean-toolchain).

From the repository root:

```bash
lake build
lake build AuditRegression
bash scripts/verify-manifest.sh
```

The standard build compiles the scientific modules and registered examples/tests. `AuditRegression` builds the regression/separator library used to prevent conceptual regressions.

Lean source files contain explicit `#print axioms` audit blocks for selected declarations. The authoritative scope is the declarations actually named in those blocks; the presence of a block does not imply that every top-level declaration in a large source file is individually printed.

---

## Scientific-source manifest

[`MANIFEST.sha256`](MANIFEST.sha256) hashes the files explicitly listed in that manifest. `scripts/verify-manifest.sh` verifies that listed scientific-source set.

Files not listed in the manifest are not implicitly covered by it; their identity is fixed by the Git commit. In particular, the repository should be cited or archived by commit when an exact documentary state matters.

---

## Documentation

Primary theoretical presentation:

- [Long-form presentation — English](LONG_PRESENTATION.md)

Method and structural foundations:

- [Relational constitutive roles — method](docs/en/relational_constitutive_roles_method.md)
- [Méthode des rôles constitutifs relationnels](docs/fr/methode_roles_constitutifs_relationnels.md)
- [Structural foundations](docs/en/structural_foundations.md)
- [Fondements structurels](docs/fr/fondements_structurels.md)

Alignment and architecture:

- [Relative alignment](docs/en/relative_alignment.md)
- [Alignement relatif](docs/fr/alignement_relatif.md)
- [Verified architecture map](docs/en/verified_architecture_map.md)
- [Cartographie architecturale vérifiée](docs/fr/cartographie_architecturale_verifiee.md)

Representation boundary:

- [Representation boundary](docs/en/representation_boundary.md)
- [Frontière représentationnelle](docs/fr/frontiere_representationnelle.md)

---

## Authorship and AI-generation disclosure

The project owner declares that the essential ideas and research direction are their own, and that the textual and code content of the repository was produced through models in OpenAI's ChatGPT series under human direction through successive interactions. This includes Lean sources, formal statements and proofs, documentation, translations, scripts, metadata, audit materials, and repository organization.

See [`AI_AUTHORSHIP.md`](AI_AUTHORSHIP.md) for the full disclosure.

---

## License and citation

The repository is licensed under Apache-2.0. See [`LICENSE`](LICENSE).

Citation metadata is provided in [`CITATION.cff`](CITATION.cff).