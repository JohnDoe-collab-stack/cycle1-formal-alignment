# Representation boundary — local exactness and diagonal non-closure

[Français](../fr/frontiere_representationnelle.md) | **English**

Navigation: [structural synthesis](structural_foundations.md) ·
[relative alignment](relative_alignment.md) ·
[method](relational_constitutive_roles_method.md)

## Status

This document describes the autonomous representation-boundary branch
implemented in:

```text
RepresentationBoundary/DiagonalizationKernel.lean
RepresentationBoundary/CircularStatusRepresentation.lean
```

This branch is not a numbered successor stage of alignment. The
`DiagonalizationKernel` is independent of alignment theory and imports only
`Init`. `CircularStatusRepresentation` separately applies that kernel to
circular statuses already established in `StrongPerimetralTurning`.

Four levels of claim remain distinct:

1. **machine-checked result** — a declaration proved in Lean;
2. **derived consequence** — a direct mathematical reading of proved results;
3. **architectural interpretation** — a proposed use of the formal pattern;
4. **future Gödelian connection** — not established by this development.

## 1. Place in the architecture

Dynamic alignment and the representation boundary answer different questions.

```text
dynamic alignment
  → coherence between transitions and realizations
  → naturality
  → composition / pasting

representation boundary
  → exact representation of a determined status
  → evaluator diagonalization
  → non-representable predicate
  → failure of global representation closure
```

No diagonal theorem is required to prove alignment naturality, persistence, or
pasting. Conversely, `diagonalStatus_notRepresentable` uses no notion of
alignment.

The circular-status application only uses the already proved adequacy between
`CircularRefinement` and `CircularSpecificationSatisfaction` to transport exact
representation between propositionally equivalent predicates.

## 2. Dependency boundary

```text
RepresentationBoundary.DiagonalizationKernel
  └── imports only Init

StrongPerimetralTurning
  ───────────────────────────────┐
                                 ├─→ RepresentationBoundary.CircularStatusRepresentation
RepresentationBoundary.DiagonalizationKernel
  ───────────────────────────────┘

RepresentationBoundary
  └── aggregates both modules
```

The diagonal kernel contains no circular presentation, history, norm, regime,
or alignment definition.

## 3. Exact representation

The primitive relation is extensional representation:

```lean
def Represents
    (eval : Code → Code → Prop)
    (program : Code)
    (predicate : Code → Prop) : Prop :=
  ∀ input, eval program input ↔ predicate input
```

A program represents a predicate when one evaluator row agrees exactly with
that predicate on every input.

Internal representability is existential:

```lean
def InternallyRepresentable
    (eval : Code → Code → Prop)
    (predicate : Code → Prop) : Prop :=
  ∃ program, Represents eval program predicate
```

These definitions assume no syntax, arithmetic, computability, or proof theory.

## 4. Constructed diagonal status

The diagonal candidate is defined from the evaluator itself:

```lean
def diagonalStatus (eval : Code → Code → Prop) : Code → Prop :=
  fun code => ¬ eval code code
```

The central theorem is:

```lean
diagonalStatus_notRepresentable :
  ¬ InternallyRepresentable eval (diagonalStatus eval)
```

If `program` represented `diagonalStatus eval`, specializing its representation
to its own input would yield:

```text
eval program program ↔ ¬ eval program program.
```

The two directions then refute one another constructively. No external diagonal
axiom or excluded middle is required.

## 5. Global representation non-closure

The property:

```lean
GlobalRepresentationClosure eval
```

states that every predicate `Code → Prop` has an exact representing evaluator
row.

The theorem:

```lean
noGlobalRepresentationClosure :
  ¬ GlobalRepresentationClosure eval
```

follows by applying the proposed closure to `diagonalStatus eval`.

The word “representation” is deliberate: this is not a second form of
alignment and it does not claim that an operational construction cannot
continue.

## 6. Local fixed point

`diagonalFixedPoint_ofRepresentable` formalizes a Lawvere-style observation.
If the predicate

```text
input ↦ operator (eval input input)
```

is locally representable, then there exists a proposition `p` such that:

```text
p ↔ operator p.
```

This is a local premise. It does not assume the global representation closure
refuted above.

It is not by itself a Gödel incompleteness theorem.

## 7. Representation exit

`StatusRepresentationExit eval` stores:

```text
candidate : Code → Prop
outside   : ¬ InternallyRepresentable eval candidate
```

`diagonalStatusExit eval` canonically supplies such an exit using
`diagonalStatus eval`.

This is not an `AbstractSegmentedTurning.RegimeExit`:

```text
RegimeExit
  → exit from an operational regime on a carrier

StatusRepresentationExit
  → exit from an internal-representability regime on code predicates
```

No theorem identifies the two.

## 8. Application to circular statuses

`CircularStatusRepresentation` observes only whether a witness exists:

```lean
HasStatus Status carrier := Nonempty (Status carrier)
```

For a circular presentation `P`:

```text
CircularRegimeStatus P H
  := Nonempty (CircularRefinement P H)

CircularSpecificationStatus P H
  := Nonempty (CircularSpecificationSatisfaction P H)
```

`circularStatusAdequacy` proves:

```text
CircularRegimeStatus P H
  ↔
CircularSpecificationStatus P H
```

from the already proved witness maps. This does not merge the original
proof-relevant witness types.

## 9. Pullback to codes

A map

```lean
decode : Code → RootedGeneratedHistory P
```

pulls both statuses back to predicates on `Code`.
`codedCircularStatusAdequacy` preserves their pointwise equivalence.

The generic theorem `transportRepresentation` states that exact representation
transports along pointwise logical equivalence.

Thus exact representation of the regime status yields exact representation of
the equivalent normative status, and conversely.

## 10. Local exactness and diagonal boundary

The structure

```lean
ExactCircularStatusRepresentation P Code
```

contains:

```text
decode
eval
program
representsRegime
```

It asserts only exact representation of one determined circular status.

The theorem

```lean
localExactRepresentation_hasDiagonalExit
```

packages:

```text
exact representation of the selected regime status
+
exact representation of the equivalent normative status
+
non-representability of the evaluator's diagonal status
```

The theorem

```lean
localExactRepresentation_notGloballyClosed
```

directly derives failure of `GlobalRepresentationClosure`.

This is the main conceptual result of the branch:

> **local exact representation of determined statuses can coexist with a
> diagonal boundary to global representability.**

## 11. Separator model

`canonicalUnitCircularStatusRepresentation` constructs a concrete instance on
`Unit`.

It proves the interface is inhabited. It does not provide a non-degenerate code
space or a universal evaluator.

`canonicalUnitCircularStatusRepresentation_hasDiagonalExit` explicitly checks
that even this local exact representation retains a diagonal exit.

## 12. Relation to alignment

The relation to alignment should be stated negatively and precisely:

```text
alignment coherence
  does not imply
global representation closure

a diagonal representation boundary
  is not required
to prove alignment
```

The mediated-coherence theory currently developed on
`research/mediated-transition-coherence` strengthens this separation: alignment,
naturality, and pasting are proved without importing `RepresentationBoundary`.

The representation boundary can therefore remain as an autonomous result
without being assigned a foundational role in alignment theory.

## 13. Relation to Gödel

The verified kernel is an abstract semantic diagonal argument, close to
Cantor/Lawvere-style arguments.

It does not yet provide:

- a syntax of formulas;
- substitution or quotation;
- arithmetization of syntax;
- a provability predicate;
- a formal consistency or effectiveness hypothesis;
- a Gödel sentence;
- either incompleteness theorem.

A formal Gödelian instance would require a separate syntactic development.

## 14. Reproduction and audit

From the repository root:

```bash
lake clean
lake build
```

The libraries can be built separately:

```bash
lake build StructuralFoundations
lake build RepresentationBoundary
lake build AuditRegression
```

The Lean files under `RepresentationBoundary` end with explicit
`#print axioms` blocks covering their public declarations.

Source integrity is checked with:

```bash
bash scripts/verify-manifest.sh
```

or on Windows:

```powershell
pwsh -NoProfile -File scripts/verify-manifest.ps1
```

## Conclusion

`RepresentationBoundary` is an autonomous representation-limit module, not an
alignment stage. It formalizes coexistence of local exact representation with
the impossibility of global representation closure for an evaluator of type
`Code → Code → Prop`.

This naming preserves the diagonal result while removing a misleading narrative
dependency on alignment theory.

## Authorship

> **Conceptual-authorship and AI-generation disclosure.** The project owner
> declares that the project's essential ideas and research direction are their
> own. This document was written by models in OpenAI's ChatGPT model series
> under human direction. See the
> [full bilingual declaration](../../AI_AUTHORSHIP.md).
