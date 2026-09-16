# Verified architecture map

## Status

This document fixes the reference architecture map of the repository from the
validated state of branch `research/mediated-transition-coherence`, commit
`384f336aa0255776b982cc34c5c9fd6cde83d9fa`.

It explicitly distinguishes:

1. the **scientific lineage** leading to the project's circular instance;
2. the **Lean import DAG**, which contains several independent abstract roots;
3. the **junctions** where a generic theory is applied to the circular
   instance;
4. **validation**, **example**, and **regression** branches, which are not new
   stages of the theory.

If an older narrative diagram diverges from this document, this map controls
the architectural interpretation of the code. It does not yet prescribe file
renaming: it first fixes the scientific and technical relations that any
refactor must preserve.

## 1. Scientific lineage of circularity

The scientific trunk specific to circularity is:

```text
SegmentedResidualRole
        |
        v
AbstractSegmentedTurning
        |
        v
StrongPerimetralTurning
        |
        v
project instance: circularity / perimeter
```

### `SegmentedResidualRole`

`SegmentedResidualRole.lean` is the first abstract kernel in this lineage. It
imports only `Init` and isolates residual-role determination and uniqueness of
the new occurrence. It has no dependency on circular presentations,
differences, provenance, loops, junctions, or totalization.

The branch

```text
SegmentedResidualRole
        |
        +----> SegmentedResidualRoleStrictness
```

is a **strictness-validation** branch. It constructively shows that the weak
residual kernel can be inhabited while a richer internal interface cannot be
reconstructed. It is not a productive stage toward the circular instance.

### `AbstractSegmentedTurning`

`AbstractSegmentedTurning.lean` imports `SegmentedResidualRole` and builds the
abstract turning of a segmented totality: boundary generator, exact regime
classification, strict continuation, regime exit, and rejection of
totalization attempts.

The fundamental production theorem is `coreTurning`. Its signature consumes
the minimal residual boundary and an obstructed regime and contains no notion
of circularity.

### `StrongPerimetralTurning`

`StrongPerimetralTurning.lean` imports `AbstractSegmentedTurning` and
`ExactTypeTransport`. It is **the scientific instance of the project**, namely
the circular/perimetral instance.

This is where `CircularPresentation`, `PerimeterSpine`, `NonClosingPosition`,
generated histories, closure obstructions, circular refinements, the circular
specification, and concrete realizations appear.

The production path actually uses the abstract kernel:

```text
oneStepResidualDeterminationCore
        |
        v
oneStepCoreResidualOccurrence
        |
        v
oneStepCoreSegmentedBoundary
        |
        v
perimetralCoreCoupledRegime
        |
        v
perimetralCoreObstructedRegime
        |
        v
oneStepCoreTurning
        |
        v
AbstractSegmentedTurning.coreTurning
        |
        v
abstractTurningOfCircularPresentation
```

Thus

```text
abstract residual -> abstract turning -> circular instance
```

is both a scientific reading and a proof path actually used by production code.

## 2. The technical DAG is not one linear chain

The preceding lineage must not be confused with the whole import graph. Three
other abstract kernels are independent of circularity.

### `ExactTypeTransport`

`ExactTypeTransport.lean` defines constructive exact transports by two maps and
their two round-trip laws. It is independent of constitution, realization,
admission, specification, and readout.

It is used directly by `StrongPerimetralTurning` and is also the root of the
generic alignment theory:

```text
ExactTypeTransport
        |
        v
Alignment.Constitutive
        |
        v
Alignment.FinitePersistence
        |
        v
Alignment.ReadoutPersistence
```

`Alignment.Constitutive` states that it isolates a content-independent
structure extracted from the canonical one-step persistence proof. We must
therefore distinguish:

- the **scientific extraction lineage**: the alignment interface was extracted
  from a canonical construction;
- the **current Lean dependency**: the abstract module no longer depends on the
  circular instance.

`Alignment.FinitePersistence` adds finite depth, extensions, and transports
through a constitutive index. `Alignment.ReadoutPersistence` attaches readouts
only after constitution and realization.

### `MediatedTransitionCoherence`

`MediatedTransitionCoherence.lean` imports only `Init`. It formalizes an
independent constructive kernel for mediator-level commutation, sequential
realization, and pasting of adjacent squares.

Its current application to finite alignment is:

```text
MediatedTransitionCoherence
             +
Alignment.FinitePersistence
             |
             v
Alignment/MediatedTransitionCoherence.lean
             |
             v
Alignment/MediatedTransitionPasting.lean
```

These two modules are generic over
`FiniteConstitutiveAlignment`. They do not depend on `CircularPresentation` or
on the circular instance of `StrongPerimetralTurning`.

Their current location is therefore a historical filesystem fact, not a
scientific dependency on a “circular instance”.

### `RepresentationBoundary.DiagonalizationKernel`

`RepresentationBoundary/DiagonalizationKernel.lean` imports only `Init`. It
independently defines internal representability, diagonal status, failure of
global representation closure, and diagonal representation exit.

This kernel is not a consequence of alignment.

### Namespace and specialization

Several generic structures (`ExactTypeTransport`, `Alignment/*`,
`MediatedTransitionCoherence`) currently live under the Lean namespace
`StrongPerimetralTurning`. Namespace membership **is not enough** to classify
them as circular specializations. Their specialization level must be determined
from their imports and signatures.

## 3. Junction of alignment with the circular instance

The canonical one-step junction is currently contained in
`StrongPerimetralTurning/ConstitutivePersistence.lean`.

Its imports are exactly:

```lean
import StrongPerimetralTurning
import Alignment.Constitutive
```

and its mathematical namespace is:

```text
StrongPerimetralTurning.ConstitutivePersistence
```

Its role is to take the continuation actually built by the circular instance
and expose it through the abstract `ExactOneStepConstitutiveAlignment`
interface.

The junction does not invent a second fresh identity.
`canonicalAlignment_fresh_eq_residualFreeOccurrence` proves that the canonical
alignment's `fresh` identity is exactly the circular instance's free residual
occurrence.
`canonicalAlignmentRealization_fresh_eq_residualConcreteOccurrence` proves the
same agreement in every supplied concrete realization.

The correct junction is therefore:

```text
StrongPerimetralTurning ---------+
                                 |
                                 v
                    ConstitutivePersistence
                                 ^
                                 |
Alignment.Constitutive ----------+
```

## 4. Finite persistence of the circular instance

`StrongPerimetralTurning/IteratedConstitutivePersistence.lean` imports
`Alignment.ReadoutPersistence` and `StrongPerimetralTurning.ConstitutivePersistence`.

It actually constructs the finite histories of the instance:

```text
iteratedHistory 0
  = perimeterDeployment

iteratedHistory (n + 1)
  = appendGenerated previous (generate previous.endpoint)
```

and then exposes them as `FiniteConstitutiveAlignment` objects and exact
realizations. This layer proves identity persistence, transport between
realizations, naturality, and persistence of the operational residual
occurrence.

Its architectural role is:

```text
ConstitutivePersistence + Alignment.ReadoutPersistence
                         |
                         v
           IteratedConstitutivePersistence
```

The correct reading is “finite persistence of the circular instance”, not “a
second constitution of circularity”.

## 5. Representation branch

The circular application of the representation boundary is
`RepresentationBoundary/CircularStatusRepresentation.lean`.

Its imports are exactly:

```lean
import StrongPerimetralTurning
import RepresentationBoundary.DiagonalizationKernel
```

It propositionally observes statuses already established in the instance:

```text
CircularRegimeStatus
  = Nonempty (CircularRefinement ...)

CircularSpecificationStatus
  = Nonempty (CircularSpecificationSatisfaction ...)
```

and derives their adequacy from `circularRefinement_soundSpecification` and
`circularSpecification_complete`.

The junction is therefore direct:

```text
StrongPerimetralTurning --------------------+
                                            |
                                            v
                         CircularStatusRepresentation
                                            ^
                                            |
DiagonalizationKernel ----------------------+
```

There is no dependency from this branch to `ConstitutivePersistence`,
`IteratedConstitutivePersistence`, or `Alignment/*`.

Conversely, dynamic alignment and persistence do not depend on
`RepresentationBoundary`.

Operational exit and representation exit therefore remain distinct
diagnostics.

## 6. Facade, examples, and regressions

`StructuralEntrypoint.lean` currently imports
`StrongPerimetralTurning.IteratedConstitutivePersistence`. It is a human-scale facade over the
instance-persistence branch and does not import `RepresentationBoundary`.

`Examples/*` supplies downstream concrete realizations and readouts. These are
not abstract kernels.

`Tests/*` contains regressions and separators. They may independently rederive
production properties but are not dependencies of production modules.

## 7. Canonical map

The canonical view should be read in blocks, without imposing a total
chronology:

```text
SCIENTIFIC LINEAGE OF CIRCULARITY

SegmentedResidualRole
   |\
   | +--> SegmentedResidualRoleStrictness   [validation]
   |
   v
AbstractSegmentedTurning
   |
   v
StrongPerimetralTurning                     [instance = circularity]


GENERIC ALIGNMENT INFRASTRUCTURE

ExactTypeTransport
   |
   v
Alignment.Constitutive
   |
   v
Alignment.FinitePersistence
   |
   v
Alignment.ReadoutPersistence


JUNCTION WITH THE CIRCULAR INSTANCE

StrongPerimetralTurning + Alignment.Constitutive
   |
   v
ConstitutivePersistence

ConstitutivePersistence + Alignment.ReadoutPersistence
   |
   v
IteratedConstitutivePersistence


GENERIC MEDIATED COHERENCE

MediatedTransitionCoherence + Alignment.FinitePersistence
   |
   v
finite mediated coherence
   |
   v
mediated pasting


REPRESENTATION BOUNDARY

DiagonalizationKernel + StrongPerimetralTurning
   |
   v
CircularStatusRepresentation


FACADE

IteratedConstitutivePersistence
   |
   v
StructuralEntrypoint
```

## 8. Frozen architectural invariants

Any future path or naming refactor must preserve the following invariants:

- `SegmentedResidualRole` abstractly precedes segmented turning;
- `SegmentedResidualRoleStrictness` remains a validation branch, not a
  productive stage;
- `AbstractSegmentedTurning` remains independent of circularity;
- `StrongPerimetralTurning` is the project's circular/perimetral instance;
- the residual occurrence consumed by turning and the canonical alignment's
  fresh identity remain connected by explicit agreement theorems;
- `ExactTypeTransport` remains shared generic infrastructure;
- `Alignment/*` remains generic and must not retroactively constitute the
  residual occurrence;
- readouts remain downstream of constitution and realization;
- `MediatedTransitionCoherence` remains an independent generic kernel;
- applying mediated coherence to `FiniteConstitutiveAlignment` must not be
  interpreted as circularity-specific;
- `DiagonalizationKernel` remains autonomous;
- `CircularStatusRepresentation` joins directly to statuses from
  `StrongPerimetralTurning` and to the diagonal kernel;
- no dependency may make `RepresentationBoundary` a necessary stage of dynamic
  alignment;
- no dependency may make alignment a prerequisite for the residual turning of
  the circular instance.

## 9. Classification after the architectural refactor

The historical numbered classification has been dissolved without changing the
mathematical content of the theorems. Modules are now placed under their actual
scientific owner:

- `StrongPerimetralTurning/ConstitutivePersistence.lean` and
  `StrongPerimetralTurning/IteratedConstitutivePersistence.lean` develop the
  circular instance;
- `Alignment/MediatedTransitionCoherence.lean` and
  `Alignment/MediatedTransitionPasting.lean` specialize the generic mediated
  coherence kernel to `FiniteConstitutiveAlignment`.

Iteration declarations now use the `iterated` prefix rather than a phase
number. The primary Lean target uses the package's architectural name,
`StructuralFoundations`, while `RepresentationBoundary` remains a separate
target. This organization makes the verified DAG visible in repository paths
without introducing a new scientific hierarchy.
