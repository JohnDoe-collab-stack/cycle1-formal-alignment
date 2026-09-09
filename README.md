# Cycle 1 — A formal proof of relative alignment

**English** | [Français](README_fr.md)

> **AI-generation disclosure.** The project owner declares that every part of
> this repository was written from start to finish by models in OpenAI's
> ChatGPT model series, under human direction and through successive
> interactions. See the
> [full bilingual declaration](AI_AUTHORSHIP.md).

> **This project builds and machine-checks in Lean a dependently typed kernel
> for relative alignment.** It formally separates construction, faithful
> realization, admission by an operational regime, and satisfaction of a norm
> defined independently of that regime. In the circular instance, it proves that
> the norm and the regime accept exactly the same histories. It then constructs
> a minimal continuation that remains exactly realizable under every concrete
> implementation satisfying the interface, yet is rejected by both the regime
> and the norm. The result therefore establishes that the ability to continue
> and local faithfulness do not imply global normative alignment, while precisely
> locating the point at which alignment is lost.

## Central contribution

For a circular presentation `P` and a constituted history `H`, the development
distinguishes three families of witnesses:

```text
F_A(H) := ExactConcreteRealization A H
R(H)   := CircularRefinement P H
S(H)   := CircularSpecificationSatisfaction P H
```

`F_A(H)` states that `H` has an exact concrete realization in an algebra `A`.
`R(H)` expresses its admission by the operational regime. `S(H)` expresses its
satisfaction of a norm defined without reference to `CircularRefinement`.

The proof closes the comparison between `R` and `S` in both directions:

```text
R(H) → S(H)                         soundness
S(H) → H = perimeterDeployment P    carrier completeness
S(H) → R(H)                         regime completeness
```

The regime and the norm therefore classify exactly the same histories. This is
an extensional agreement on their carriers: their witness structures may contain
different data and are not identified with one another.

## Independent norm and classification mechanism

The circular norm combines a local obligation with a trajectory-level
obligation:

```text
CircularSpecificationSatisfaction P H
  ├─ local : ExactNonClosingRealization P H
  └─ trajectory :
       StrictConstitutivePrefix (perimeterDeployment P) H
       → P.TotalLoop
```

The first component requires every non-closing requirement to be realized by a
constituted occurrence that agrees with it exactly. The second gives closure its
trajectory-level meaning: every strict continuation beyond the perimeter
deployment would have to realize a total loop.

Carrier completeness follows this constructive chain:

```text
S(H)
  ↓ exact local realization
PerimeterExtension P H
  ↓ decomposition of the continuation
root continuation
  → H = perimeterDeployment P

positive continuation
  → StrictConstitutivePrefix (perimeterDeployment P) H
  → P.TotalLoop
  → contradiction with rejectTotalLoop
```

The positive branch is impossible. Every history satisfying the norm is
therefore exactly the canonical deployment. Regime completeness then transports
the canonical circular refinement along this equality.

## Machine-checked central theorems

Soundness of the regime relative to the independent norm:

```lean
StrongPerimetralTurning.circularRefinement_soundSpecification
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (refinement : CircularRefinement P history) :
    CircularSpecificationSatisfaction P history
```

Carrier completeness:

```lean
StrongPerimetralTurning.CircularSpecificationSatisfaction.eq_perimeter
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (satisfaction : CircularSpecificationSatisfaction P history) :
    history = perimeterDeployment P
```

Regime completeness:

```lean
StrongPerimetralTurning.circularSpecification_complete
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (satisfaction : CircularSpecificationSatisfaction P history) :
    CircularRefinement P history
```

The second declaration first classifies the carrier as the canonical perimeter
deployment. The third then transports the canonical regime witness; it does not
automatically reconstruct the internal witnesses of the regime from the norm.

## Diagnosed minimal exit

The canonical exit candidate is:

```text
h⁺ := oneStepAfterPerimeter P
```

The same object simultaneously carries the following results:

```text
StrictConstitutivePrefix (perimeterDeployment P) h⁺    inhabited
ExactNonClosingRealization P h⁺                        inhabited
canonical precedence and adjacency                     preserved
ExactConcreteRealization A h⁺                          inhabited for every supplied A
CircularRefinement P h⁺                                refuted
CircularSpecificationSatisfaction P h⁺                 refuted
```

The normative refutation is direct. The strict continuation turns the
trajectory obligation into `P.TotalLoop`, which is rejected by the constitutive
obstruction carried by the presentation. It therefore does not rely first on
rejection by the regime.

The construction nevertheless remains possible and faithfully interpretable.
Exiting the regime destroys neither the produced history, its occurrences, nor
the structural agreements already preserved. It locates a break in normative
status on the same constituted object.

Uniformity is provided by `oneStepUniformPerimetralRegimeExit`: the candidate is
fixed before the implementation is chosen, and an exact realization of that
same history is then constructed for every supplied
`ConcreteContinuationAlgebra P`. The diagnosed boundary therefore does not
depend on a particular concrete representation satisfying the interface.

## Relevance to alignment

The result formalizes several distinctions required by an alignment diagnostic:

```text
ability to continue a construction
  ≠ normative admission of that continuation

local faithfulness with correct precedence and adjacency
  ≠ satisfaction of a global trajectory obligation

exact concrete realization
  ≠ membership in the evaluated regime
```

A locally correct behavior or faithful implementation is therefore not, by
itself, a certificate of global alignment. The framework makes the following
obligations separately auditable:

1. the norm imposed on a history;
2. the operational regime intended to enforce it;
3. the faithfulness of its concrete realizations;
4. soundness and completeness of the agreement between norm and regime;
5. the first candidate that preserves realization while losing normative status.

Relative alignment thus becomes a formal relation between an independently
defined specification and a regime evaluated on the same constituted objects,
rather than an implicit identification of what can be produced with what should
be admitted.

## Structural out-of-distribution

The framework introduces **structural OOD relative to a regime** as a
conceptual extension of out-of-distribution reasoning. Statistical OOD concerns
departure from a data distribution. Structural OOD instead concerns a candidate
that remains generated by the relevant construction but is not admitted by an
explicit regime. It requires neither a probability distribution nor a training
set. Faithful realizability is not part of this documentary definition; it is
an additional property established for the circular witness below.

The circular instance provides a machine-checked witness:

```text
h⁺ : RootedGeneratedHistory P
∀ A : ConcreteContinuationAlgebra P,
  ExactConcreteRealization A h⁺
CircularRefinement P h⁺ → False
```

Thus `h⁺` is not outside the space of construction or concrete realization. It
is outside the operational regime while retaining the positive structural
witnesses already established. This makes structural OOD a diagnosis of a
change of status, rather than a synonym for malformed, unknown, or
unrealizable.

Structural OOD and relative misalignment are not identified. A regime exit is
the structural diagnosis; relative misalignment additionally involves an
independent norm and the proved adequacy of the regime to that norm. In the
circular instance, the same minimal candidate also carries the direct
refutation
`CircularSpecificationSatisfaction P h⁺ → False`, so it witnesses both
diagnoses.

The underlying constructions and refutations are verified in Lean. The term
**structural OOD** and its interpretation are presently a conceptual proposal,
not yet a generic Lean definition. See the full treatment in
[Structural foundations](docs/en/structural_foundations.md).

## Abstract kernel and normative interface

The architecture has two distinct levels of generality.

The first is fully polymorphic over the carrier and presupposes neither histories,
perimeters, nor circularity:

- `ExactRegimeClassification` exactly characterizes the carriers of a regime
  relative to a canonical carrier;
- `RegimeExit` combines a candidate, a positive witness of faithfulness, and a
  refutation of its membership in the regime;
- `UniformRegimeExit` fixes the candidate before implementations vary and
  requires its faithfulness in every supplied implementation.

The second level is parametric over the norm and the regime, but its carrier is
currently specialized to `RootedGeneratedHistory P` for
`P : CircularPresentation`:

- `NormativeAdequacy` separates the type of alignment specifications from the
  family of regimes being evaluated;
- `AdequateAlong` requires normative adequacy along every occurrence actually
  constituted in a history;
- `SpecRelativeHistoryExit` combines faithfulness, regime exit, and adequacy
  witnesses for a specification on the same candidate.

On the current history carrier, this interface supports other norms and regimes,
proofs of their adequacy, and boundary diagnostics that preserve the object while
locating exactly which property is lost. The more abstract `RegimeExit` kernel is
directly reusable on other carriers; extending the entire normative interface to
an arbitrary carrier would require an additional generalization.

## Conceptual foundations

The development follows four structural distinctions organized by an order of
dependency:

1. individuation is definitionally prior to identity;
2. totality is local and must not be conflated with globality;
3. succession is indexed by a total locality, without an external clock;
4. time and the global are derived from the trajectory of localities.

```text
presentation
→ locality and roles
→ formed occurrences and local realization
→ succession
→ history
→ precedence, global composition, and readings
```

These principles structure the demonstrated instance; they are not presented as
four independent universal theorems.

### Relational constitutive roles

An occurrence is individuated by its formation and by the structural relations
in which it participates before being projected to a reading, label, or value.
The method thereby preserves provenance, position, role, and participation in a
composition even when some readings coincide.

This fine-grained structure is preserved by concrete interpretations.
`exactlyInterpretHistory` constructs inverse correspondences between free and
concrete occurrences, together with agreement on sources, targets, and steps. A
change of representation therefore neither erases, merges, nor adds an
occurrence without a corresponding occurrence within the interface.

## Development architecture

- [`SegmentedResidualRole.lean`](SegmentedResidualRole.lean) proves the abstract
  residual-occurrence theorem: a faithfully segmented positive continuation has
  exactly one new occurrence, necessarily carrying the residual role;
- [`AbstractSegmentedTurning.lean`](AbstractSegmentedTurning.lean) defines exact
  regime classification, typed exits, and the abstract segmented-turning theorem;
- [`StrongPerimetralTurning.lean`](StrongPerimetralTurning.lean) constructs free
  histories, perimeter realization, the independent norm, the circular regime,
  concrete interpretations, and the complete alignment instance.

## Reproduction and audit

Prerequisite: `elan`, or an equivalent installation capable of reading
`lean-toolchain`.

```bash
lake build
```

This command compiles the three modules in the order
`SegmentedResidualRole → AbstractSegmentedTurning → StrongPerimetralTurning` and
runs their final `#print axioms` blocks.

From the repository root, verify the integrity of the nine scientific files in
the current package on Linux or macOS:

```bash
bash scripts/verify-manifest.sh
```

On Windows PowerShell:

```powershell
powershell -ExecutionPolicy Bypass -File scripts/verify-manifest.ps1
```

## Detailed documentation

- [Structural foundations — English](docs/en/structural_foundations.md)
- [Fondements structurels — français](docs/fr/fondements_structurels.md)
- [Method of relational constitutive roles — English](docs/en/relational_constitutive_roles_method.md)
- [Méthode des rôles constitutifs relationnels — français](docs/fr/methode_roles_constitutifs_relationnels.md)
- [Formal proof of relative alignment — English](docs/en/formal_relative_alignment_proof.md)
- [Preuve formelle d'alignement relatif — français](docs/fr/preuve_formelle_alignement_relatif.md)
- [Build and audit log](audit/AUDIT_BUILD.txt)
- [AI authorship and generation disclosure](AI_AUTHORSHIP.md)

## Provenance and scope

The `audit/AUDIT_BUILD.txt` log states that the initial versions of five scientific
files were copied from source commit
`31ba1516aaefc5e2ef29aff902fed6af2cd43176` in
`git@github.com:JohnDoe-collab-stack/meta.git`. Since that import, the two
original French documents have undergone local editorial stabilization and
their English translations have been added; a bilingual methodology document
was added locally. No Lean module has been modified. The nine current scientific
files match the hashes recorded in `MANIFEST.sha256`.

The source commit is not publicly accessible at the stated address, and the local
working copy does not contain its Git history. The manifest can therefore verify
the integrity of the current package, but cannot by itself establish its remote
provenance. For a reproducible external audit, these sources must be published in
the repository referenced by `CITATION.cff` under a resolvable commit or tag.

The result is a first complete instance of a formal kernel for relative
alignment. It establishes adequacy within the framework defined by
`CircularPresentation`; by itself, it does not formalize every possible norm or
system. The proof is constructive, and its audit must not depend on any axioms,
`Classical`, `propext`, or `Quot.sound`.

## License and citation

The code and documentation are distributed under the Apache-2.0 license.
Citation metadata is provided in `CITATION.cff`.
