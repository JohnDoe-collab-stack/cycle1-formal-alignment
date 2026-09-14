# Cycle 2 — Reflective alignment and diagonal non-closure

[Français](../fr/alignement_reflexif.md) | **English**

Navigation: [structural synthesis](structural_foundations.md) ·
[Cycle 1 — relative alignment](relative_alignment.md) ·
[method](relational_constitutive_roles_method.md)

## Status

This document describes the self-contained Cycle 2 extension implemented in
`Cycle2/DiagonalizationKernel.lean` and `Cycle2/ReflectiveAlignment.lean`.
Every Lean declaration named below is compiled with Lean 4.33.1 and covered by
the repository's final `#print axioms` audit.

Four levels of claim are kept separate:

1. **machine-checked result** — a declaration proved in Lean;
2. **derived consequence** — a direct mathematical reading of proved declarations;
3. **architectural interpretation** — a proposed use of the formal pattern;
4. **future Gödelian connection** — not established by this cycle.

## Place in the overall architecture

Cycle 2 is not an independent branch attached directly to the structural base.
It begins from the adequacy already established by the two Cycle 1 witness maps,
observes that adequacy at proposition level through `Nonempty`, and only then
transports it into the representation layer:

```text
Cycle 1 witness maps
  → exact relative adequacy
  → `Nonempty` status equivalence
  → pullback to codes
  → exact representation transport
  + evaluator diagonalization
  → determined exact representation with global non-closure
```

The operational continuation `oneStepAfterPerimeter` belongs to another branch
after Cycle 1 adequacy. It is not an input to the diagonal proof.

## 1. Purpose

Cycle 1 separates construction, faithful realization, operational admission,
and satisfaction of an independent norm. Cycle 2 asks a different question:
can one evaluator internally represent every proposition-valued status on its
own code space?

The answer is constructively negative. Given

```lean
eval : Code → Code → Prop
```

the development constructs a predicate from `eval` itself and proves that no
row of `eval` represents it exactly. This is a representation-level boundary,
not an operational history boundary.

## 2. Dependency boundary

```text
Cycle2.DiagonalizationKernel ── imports only Init ──┐
                                                    ├─→ Cycle2.ReflectiveAlignment
StrongPerimetralTurning ────────────────────────────┘             │
                                                                  ▼
                                                                Cycle2
```

`Cycle2.DiagonalizationKernel` contains no circular presentation, history,
norm, regime, or alignment definition. All contact with Cycle 1 is confined to
`Cycle2.ReflectiveAlignment`. Conversely, no Cycle 1 module imports Cycle 2.

## 3. Exact representation

The primitive relation is extensional representation:

```lean
def Represents
    (eval : Code → Code → Prop)
    (program : Code)
    (predicate : Code → Prop) : Prop :=
  ∀ input, eval program input ↔ predicate input
```

Thus a code represents a predicate when one row of the evaluator agrees with
that predicate at every input. Internal representability is existential:

```lean
def InternallyRepresentable
    (eval : Code → Code → Prop)
    (predicate : Code → Prop) : Prop :=
  ∃ program, Represents eval program predicate
```

No syntax, computability, arithmetic, proof system, or intended semantics is
assumed at this level.

## 4. Constructed diagonal status

The candidate is defined, not postulated:

```lean
def diagonalStatus (eval : Code → Code → Prop) : Code → Prop :=
  fun code => ¬ eval code code
```

The central theorem is:

```lean
diagonalStatus_notRepresentable :
  ¬ InternallyRepresentable eval (diagonalStatus eval)
```

Assume that a code `program` represents `diagonalStatus eval`. Specializing the
representation equivalence to `program` gives

```text
eval program program ↔ ¬ eval program program.
```

Each direction then refutes the other constructively. The proof uses neither
excluded middle nor an external diagonal axiom.

## 5. Global non-closure

Global reflective closure is the claim that every predicate on `Code` has an
exact representing row:

```lean
def GlobalReflectiveClosure (eval : Code → Code → Prop) : Prop :=
  ∀ predicate, InternallyRepresentable eval predicate
```

The theorem

```lean
noGlobalReflectiveClosure : ¬ GlobalReflectiveClosure eval
```

is derived by applying the proposed closure to `diagonalStatus eval` and then
invoking `diagonalStatus_notRepresentable`. The witness of failure is therefore
explicit and remains tied to the evaluator it escapes.

`diagonalFixedPoint` also packages the corresponding Lawvere-style observation:
global representation would give a fixed point for every operator
`Prop → Prop`. Taking negation explains why that global premise cannot hold.
The theorem does not add a consistency or incompleteness result; its premise is
precisely the closure already refuted above.

## 6. Representation-level exit

`StatusRepresentationExit eval` stores:

```text
candidate : Code → Prop
outside   : ¬ InternallyRepresentable eval candidate
```

`diagonalStatusExit eval` instantiates this structure with the constructed
diagonal predicate. This is the Cycle 2 representation-level analogue of an
exit certificate. It is deliberately not an `AbstractSegmentedTurning.RegimeExit`:
the two structures classify different kinds of objects under different regimes.

## 7. Proposition-level reading of Cycle 1

Cycle 1 statuses are proof-relevant families. Cycle 2 observes only whether a
witness exists:

```lean
HasStatus Status carrier := Nonempty (Status carrier)
```

For a circular presentation `P` and history `history`, it defines:

```text
CircularRegimeStatus        := Nonempty (CircularRefinement P history)
CircularSpecificationStatus := Nonempty
  (CircularSpecificationSatisfaction P history)
```

The theorem `circularStatusAdequacy` proves their equivalence by using the Cycle
1 soundness and completeness maps in opposite directions. `Nonempty` is only a
proposition-level observation; it neither replaces nor identifies the original
witness types.

## 8. Pullback to codes and transport

A decoding function

```lean
decode : Code → RootedGeneratedHistory P
```

pulls each history status back to a predicate on codes. The theorem
`codedCircularStatusAdequacy` proves pointwise equivalence of the pulled-back
regime and specification statuses.

`transportRepresentation` then establishes a general rule: exact
representation transports across pointwise logical equivalence. Consequently:

```text
representation of the circular regime status
  ↔ representation of the circular specification status.
```

This transport uses the already proved normative adequacy. It does not define
the norm from the regime and does not assume universal representability.

## 9. Exact representation of determined statuses with global non-closure

`ReflectiveCircularStatusView P Code` contains a decoder, an evaluator, one
program, and a proof that this program exactly represents the pulled-back
circular regime status. Adequacy supplies exact representation of the
specification status by the same program.

The theorem `exactCircularStatusRepresentation_hasDiagonalOutside` packages
three simultaneous facts:

```text
the selected regime status is represented exactly
the equivalent normative status is represented exactly
the evaluator's diagonal status is not internally representable
```

`exactCircularStatusRepresentation_notGloballyClosed` states the corresponding
failure of global reflective closure. Exact representation of these determined
statuses and normative adequacy therefore coexist with a precisely located
representational exterior.

The closed `Unit` model `canonicalUnitCircularStatusView` verifies that this
interface is inhabited: a particular circular status can be represented by a
constant evaluator without turning that evaluator into a universal one.
This is currently the only reflective status view constructed by the
repository. It establishes inhabitation of the interface, not the existence of
a non-degenerate code space or a non-constant evaluator.

## 10. Two exits that are not identified

Cycle 1 and Cycle 2 construct distinct boundaries:

| Level | Candidate | Regime | Certified loss |
|---|---|---|---|
| operational | `oneStepAfterPerimeter P` | `CircularRefinement P` | operational admission and normative satisfaction |
| representational | `diagonalStatus eval` | `InternallyRepresentable eval` | exact internal representation |

The first candidate is a history that remains constructible and, like every
rooted generated history in this development, admits an exact concrete
realization. The second is a predicate on codes constructed from an evaluator.
No theorem in the repository converts one exit into the other, and no such
conversion is assumed.

## 11. Relation to Gödel

The verified proof is an abstract semantic diagonal argument, closely related
to Cantor/Lawvere non-surjectivity. It captures the architectural fact that an
evaluator cannot extensionally enumerate every predicate on its own code space.

It does **not** yet provide:

- a syntax of formulas;
- substitution or quotation;
- an arithmetization of syntax;
- a provability predicate;
- a formal consistency or effectiveness hypothesis;
- a Gödel sentence;
- either incompleteness theorem.

A formal Gödelian instance would require these ingredients in a separate
syntactic development. The present result can serve as its abstract diagonal
kernel, but is not itself that instance.

## 12. Reproduction and audit

From the repository root:

```bash
lake clean
lake build
```

To build the two libraries separately:

```bash
lake build Cycle1Alignment
lake build Cycle2ReflectiveExtension
```

The Cycle 2 source files end with `#print axioms` for all 28 of their explicit
top-level declarations. The complete build runs 460 `#print axioms` commands
over 459 distinct declarations; one declaration is re-audited by the
`Cycle2.lean` aggregator. Every report states that the named declaration has no
axiom dependency. Source integrity is checked on Linux or macOS with:

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

## 13. Stabilized conclusion

Cycle 2 machine-checks a self-contained constructive kernel of reflective
non-closure.
It constructs the escaping status, proves its non-representability, transports
Cycle 1 normative adequacy through exact representation of determined statuses,
and demonstrates that this exactness does not collapse into global closure. Its formal
scope is intentionally narrower than Gödelian incompleteness and does not merge
the operational exit of Cycle 1 with the representational exit of Cycle 2.

## Authorship

> **Conceptual-authorship and AI-generation disclosure.** The project owner
> declares that the project's essential ideas and research direction are their
> own. This document was written from start to finish by models in OpenAI's
> ChatGPT model series, under human direction and through successive
> interactions. See the
> [full bilingual declaration](../../AI_AUTHORSHIP.md).
