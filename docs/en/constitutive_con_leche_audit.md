# Constitutive audit of a verification chain with ConLeche

**English** | [Français](../fr/audit_constitutif_con_leche.md)

## 1. Result

This development separates two complementary guarantees:

1. ConLeche checks the object actually presented to its verified fold;
2. constitutive analysis makes explicit how that object was formed from a
   source occurrence.

The central distinction is:

```text
acceptance of the presented object
≠
faithfulness of its formation from the source
```

The module
[`ConstitutiveAlignment/VerificationTransport.lean`](../../ConstitutiveAlignment/VerificationTransport.lean)
formalizes this distinction constructively. It depends on neither ConLeche nor
its set-theoretic model.

## 2. Scope of the external theorem

ConLeche's main theorem is relative to a model of its `SetTheory` interface.
When `checkDecls` in `verified` mode accepts a declaration list and produces an
environment, that environment contains no constant whose type is `False`.

The result concerns the list received by the verified fold. The frontend lies
before that boundary: it parses the NDJSON stream, adds a prelude, handles
certain dependencies and inductive blocks, and may rewrite projection
functions. The declarations it produces are checked, but full semantic
equivalence between the initial stream and all these transformations is not the
main theorem.

The constitutive test names the resulting internal alignment exactly:

```text
R(ds, env) = checkDecls .verified ds = .ok env
S(ds, env) = env contains no constant whose type is False
```

`no_proof_of_False` establishes `R → S`. In the inspected code, the chain is
`acceptance → FullyChecked → Nonempty EnvModelM → exclusion of False`. The
local module reconstructs this shape as `SemanticChecker.Soundness`, exposes
its factorization `R → Certificate → S`, and uses separators to show that this
soundness yields neither completeness `S → R` nor provenance faithfulness.

A separate recompilation against the pinned commit additionally establishes
that the last arrow factors through the projection
`EnvModelM → {base2, type_reads, mem_type}`. The other eleven top-level
`EnvModelM` fields are therefore not read directly by the `no False` capstone;
they may still be required to construct that projection upstream. Within
`base2`, this arrow reads the `acval` valuation and the `basis_pinnedL` pin. Its
set-theoretic endpoint consumes only an empty object and the impossibility of
membership in it. `ConstructiveEmptyFoundation.derivedEmpty` positively
reconstructs that witness from regularity and an inhabited transitive
universe, without classical choice. The complete `checkDecls → FullyChecked →
slice → no False` chain recompiles against ConLeche; at this stage its upstream
construction still passes through the full `EnvModelM`.

The direct-construction test then followed the induction actually used by
`installRun_model`. Its first semantic step calls `declStep_preserves` for each
of the six declaration forms. That operation does not carry the terminal slice
as its invariant: it consumes and reconstructs the full carrier, notably
because checking a new value may exercise the `const`, definition, iota,
projection, literal, capability, and reduction clauses assembled by
`TierInputsAt.ofSem`. The current lemmas therefore do not yield a direct
`FullyChecked → slice` construction that bypasses the full model. The established
result is more precise: the slice suffices for the terminal inference, while its
inductive closure under every accepted declaration remains a separate
obligation.

The local kernel now distinguishes a constructive realization from its
propositional shadow. `WitnessCandidate` carries an initial witness and extracts
the terminal guarantee; `ShadowCarrier` retains only existence through
`Nonempty`. `WeaklyStable` asks only for existence of a successor, whereas
`HistoricalStable` constructs a determined successor related to the old
witness by a compatibility relation. The theorems `shadowExtract` and
`historicalStable_implies_weaklyStable` establish the two valid forgetful
steps. Finally, a `Separator` refutes either local transition reconstruction or
any historical stability whose compatibility would provide the separated
obligation. The kernel asserts no converse, canonical closure, or minimality.

Weakening the concrete separator now sharpens this boundary. A sufficient
local envelope factors the three value branches `defn`, `thm`, and `opaque`
through three facts: well-denotation of the value, membership in the inferred
type, and semantic agreement between the inferred and declared types. In the
first countermodel, the first two facts are positively constructed and the
third is refuted. The transition- and old-witness-indexed obligation `Q0` is
therefore reduced to this historical agreement alone for that transition. It
is carried in `Type` through `PLift`, since ConLeche's execution certificates
live in `Prop`. For the concrete transition, `B0W + Step + Q0` produces both
`CheckedValueLocalRows`, while the separator refutes exactly `Q0`.

The strict generic test then stopped at the first requested branch, `defn`. A
second concrete `B0W` witness assigns a stored alias an interpretation in
`U₀`, while the checker unfolds the same alias operationally as a function
type. A stored function is terminally well typed in the weakened slice, and a
new definition applying it is accompanied by an actual constructive
`DeclDefnRun`. Nevertheless, the application cannot be `WellDenoted`: at
level zero its alleged function must be `pt`, and at a positive level its graph
would have to equal `unitSet`; both alternatives are constructively refuted.
The theorem `b0WDefnStepDoesNotProduceValueWellDenoted` therefore establishes
the concrete separation

```text
B0W + accepted DefnStep
  ↛ valueWellDenoted.
```

The local analysis then descends one layer without opening `WellDenoted`. The
theorem `ValueFrontRun.appSubtermReads` shows that when the annotated output of
an actual `ValueFrontRun` is an application, its head and argument have
successful `denoteMeta` readings for every level valuation `ψ`. The proof
consumes only `slice.base2`, the `ValueFrontRun`, and the equality identifying
its output as an application. It consumes neither `ConstantValRun`,
`type_reads`, `mem_type`, nor the eta witness. This is not a purely syntactic
result, however: `acceptedReads_of` uses the `base2` model and the successful
inference already contained in `ValueFrontRun`. The reading layer therefore
creates no new separator.

The next test does, however, stop immediately at the first semantic row.
`ApplicationHeadWellDenoted` preserves the established quantifier order: for
each `ψ`, the same `headA` and `argA` readings must serve for every `ρ`. The
theorem `appReadsDoNotDetermineHeadWellDenoted` constructs a `B0W` witness, an
actual `ValueFrontRun` with applicative output, and both readings for every
`ψ`, then refutes every assignment of `WellDenoted` to that same head for all
`ρ`. The countermodel places the already established semantically incoherent
application in the body of an operationally accepted lambda and uses that
lambda as the head of an outer application. The head reading is therefore
determined, but its well-denotation does not follow:

```text
B0W + ValueFrontRun + head/argument readings
  ↛ ∀ ρ, WellDenoted ρ headA.
```

Opening the exact `WellDenoted_lam` equation localizes the break one layer
further. Its first clause, well-denotation of the `Sort 0` domain, is
constructed without the walk witness or any additional semantic memory. The
second clause requires the body to remain well-denoted under every extension
of `ρ` by a member of the domain. `outerHeadBodyHereditaryFails` already
refutes it by choosing the empty set, which belongs to the interpretation of
`Sort 0`, and reusing the inner-application separator. The third clause, which
quantifies a semantic fibre, is not opened. The first internal residue is thus
hereditary well-denotation of the body, not well-denotation of the domain.

Opening this hereditary clause in turn stops at the first residue of the inner
application. `argReadExact` fixes its reading as the expected annotated
product. `innerApplicationHeadWellDenoted` and
`innerApplicationArgumentWellDenoted` then discharge the two recursive
clauses of `WellDenoted_app`: both the constant head and the argument are
well-denoted. `InnerApplicationFrame` subsequently keeps the same `v`, domain
`A`, and fibre `B` shared by the three remaining semantic clauses. Internal
weakening nevertheless shows that the first clause alone already yields the
contradiction: for every `v`, `A`, and `B`,
`innerApplicationHeadInPiRFails` refutes membership of `punit`'s `unitSet`
reading in `piR v A B`. At level zero this would identify `unitSet` with `pt`;
at a positive level it would make `unitSet` a graph although its member `pt`
is not a pair. `argumentInA` and `zeroCondition` are therefore not consumed by
this separator. Their reconstructibility is not analyzed.

The actual positive proof of the `headInPiR` clause is then factorized without
detaching its intermediate objects. The
`headInPiR_of_membership_and_reduction` lemma consumes a membership row `M`
from the head reading to an inferred-type reading, a reduction equality `R`
between that same inferred type and the reduced `forall`, and the exact reading
of that `forall` as the corresponding `piR`. In the countermodel,
`innerHeadMembershipInInferredType` positively constructs `M`: `punit` reads
as `unitSet`, which belongs to `univ 0`, the reading of the inferred `Sort 0`
type. `aliasWhnfAndRead` keeps together the concrete `WhnfRun` and the reading
of the body it produces: the reduced `forall` is not selected independently.
By contrast, `inferredTypeReductionAgreementFails` refutes `R`:
identifying `univ 0` with this functional reading would produce precisely the
already refuted `headInPiR` membership. Thus, in this countermodel, the first
resisting dependency of this factorization is `R`, not `M`.

This result makes `R` neither a minimal condition nor a universal necessity,
and it does not yet identify a historical memory. It only localizes the break
in this concrete positive proof while retaining the same inferred type and the
same reduced `forall` across both premises.

Opening the positive proof of `R` then descends into the δ branch of
`whnfLoop_claim`. This branch uses `Delta`, which the general architecture
constructs from `AcvalDefnInst`. The weakening nevertheless imports neither
`WhnfClaim` nor `AcvalDefnInst` as a new primitive. It isolates their exact
local consequence, `AliasDeltaReadingCoherence`: for this reduction, the
reading of the constant before unfolding must equal the reading of the body
that is actually unfolded.

`aliasDeltaReading_of_Delta` shows that `Delta` produces this local relation,
and `aliasDeltaReading_of_acvalDefnInst` records the sufficient chain from the
general field. Conversely at the level required here,
`inferredTypeReductionAgreement_of_aliasDeltaReading` shows that this reading
equality alone reconstructs `R`; it retains the annotations fixed by
`aliasInferredTypeRead`, `aliasWhnfAndRead`, and `aliasBodyRead`.

The separator then reaches this relation itself.
`aliasDeltaReadingCoherenceFails` refutes it, and
`b0WAndWhnfDoNotDetermineAliasDeltaReading` packages a `B0W` witness, the
concrete `whnf`, and this refutation. Finally, `oldSlice_hasNoAcvalDefnInst`
shows that the countermodel cannot satisfy the general field, precisely because
its alias instance would imply the refuted local relation. The result still
establishes neither that the whole of `AcvalDefnInst` is necessary, nor that
this local relation is minimal in a general class, nor that it must be persisted
in a future `B1`.

A further weakening shows that even the complete semantic equality `R` is not
consumed by the final step. `AliasDeltaHeadMembershipTransport` is indexed by
the `old.slice` realization, by `ψ`, and by `ρ`; it transports only the already
available membership of this exact head reading from its type reading before δ
to the reduced-type reading.
`aliasDeltaHeadMembershipTransport_of_reductionAgreement` establishes `R →`
transport, so reading coherence also produces this transport. Then
`innerHeadInPiR_of_aliasDeltaHeadMembershipTransport` combines only that
transport with `M` to obtain the exact `headInPiR` clause.

The weakening does not repair the countermodel:
`aliasDeltaHeadMembershipTransportFails` already refutes the oriented
transport, while `b0WAndWhnfDoNotDetermineHeadMembershipTransport` retains in
one statement the `old.slice` witness, the concrete `whnf`, and this refutation
for every `ψ` and `ρ`. However,
`aliasDeltaHeadMembershipTransport_iff_innerHeadInPiR` establishes a decisive
limit of the weakening: for this fully fixed occurrence, `M` is already
available and the transport target is exactly `headInPiR`; the transport is
therefore equivalent to the conclusion itself. It is not yet a strict
intermediate capacity. Equality `R` remains a sufficient envelope, but no
converse between transport and equality has been proved. Weakening this local
transport further would merely restate the target here.

The weakening therefore changes level. `UniformMembershipPreservation`
quantifies over every set valuation `ρ` and every object `x`: every membership
in the reading before transformation must be transported to the reading after
transformation. The relation thus covers a whole family of membership
judgements uniformly instead of renaming one occurrence's conclusion.

`uniformMembershipPreservation_of_semanticEquality` shows that uniform
semantic equality implies this relation. For the current alias,
`aliasDeltaReading_implies_uniformMembershipPreservation` performs that step,
then `innerHeadInPiR_of_uniformMembershipPreservation` recovers the particular
conclusion from `M`.

This time the weakening is strict and non-vacuous. A second concrete δ
unfolding concerns `GrowingType`, whose stored body is `Sort 1`, while the
weakened realization reads the constant as `Sort 0`.
`growingTypeDeltaUnfold` and `growingTypeDeltaReads` fix that same unfolding
and its two exact readings.
`growingTypeDelta_uniformMembershipPreservation` proves transport of every
membership by cumulativity from `univ 0` to `univ 1`, and
`growingTypeDelta_hasPreservedMembership` exhibits `empty` as a membership
that is actually preserved. Nevertheless,
`growingTypeDelta_semanticEqualityFails` refutes equality: it would turn
`univ 0 ∈ univ 1` into the impossible self-membership `univ 0 ∈ univ 0`.
Thus, within the studied class of membership judgements:

```text
uniform semantic equality
        ↓
uniform preservation of membership
        ↓
the required particular membership

but

uniform preservation of membership
        ↛ uniform semantic equality
```

The connection to the original countermodel is then direct while retaining
every index. `aliasUniformMembershipPreservationFails` applies the uniform
relation to the same `ψ`, the same `ρ`, and membership row `M`, then reaches
the same refuted `headInPiR`. The theorem
`b0WAndWhnfDoNotDetermineUniformMembershipPreservation` gathers one `B0W`
witness, the concrete `whnf` of the same alias, the exact reading of its result
for every `ψ`, and the refutation of uniform preservation between the old and
reduced readings. It therefore establishes:

```text
B0W + concrete unfolding of the alias
        ↛ uniform preservation of membership
```

The transversal audit weakens this capacity once more. The real consumers
need transport only for valuations `ρ` satisfying the annotated context `Δa`.
`GuardedMembershipPreservation` states exactly that guard, while
`WhnfMembershipClaim` retains well-denotedness of the reduct and replaces the
equality supplied by `WhnfClaim` with this transport alone. Three
reconstructions compile through the weakened interface: canonical `SortSemAt`,
IO `SortSemAtIO`, and the structurally distinct `StructEtaIrrel` row. The
capacity is therefore neither tailored to one occurrence nor merely duplicated
between two checker lanes.

The same countermodel already refutes it in the empty context:
`b0WAndWhnfDoNotDetermineGuardedMembershipPreservation` retains one `B0W`
witness, the same concrete unfolding, and its exact reading, then shows that
even this guarded relation is not reconstructible. Equality remains sufficient
to produce it. The same `GrowingType` witness now directly and non-vacuously
establishes `GuardedMembershipPreservation ↛ equality` in the empty context,
without erasing the previously established separation for
`UniformMembershipPreservation`.

The inverted analysis of the δ producer yields a first exact chain, without
yet treating it as an interface common to other reductions:
`AcvalDefnInst` constructs `Delta`; `Delta` forces identity of the annotation
read before and after the concrete unfolding; that identity produces guarded
preservation. This identifies the upstream datum actually used by the δ
producer, but proves neither its minimality nor persistence in `B1`.

`unfoldDefinition_exposesExactSpine` now fixes the operational class transported
by `delta_core`. A successful unfolding exposes a constant head, its stored
`defnInfo`, agreement of level arities, and a target exactly equal to the
instantiated body with `source.getAppArgs` reapplied. The spine is therefore an
arbitrary finite syntactic list preserved in the same order.
`denoteMeta_mkAppN_swap` requires neither typing, `Sat`, nor `WellDenoted` at
this layer; successful reading of the complete term forces the required
argument readings. `ψ` and depth remain fixed, while `ρ` does not yet occur.

This exact context class now generates a formal intermediate relation.
`ReadableApplicativeMembershipSimulation` is indexed by `acval`, the
environment, `ψ`, and depth. It admits an annotated spine only when
`DenoteMetaSpine` proves that it is the actual reading of one common syntactic
spine. Every membership observed after that spine on `before` must remain valid
after the same spine, in the same order, on `after`, uniformly in `ρ`. Adding
one argument explicitly requires its reading equation. The relation contains
no `Sat`, typing, or `WellDenoted` premise.

`ApplicativeMembershipSimulation` is the stronger envelope quantifying over
all lists of `AnnotTerm`; it restricts to the exact interface for every reading
context. The proofs therefore establish:

```text
uniform semantic equality of the heads
        ↓
ApplicativeMembershipSimulation
        ↓ restriction to actual readings
ReadableApplicativeMembershipSimulation
        │ stable under one actually read argument
        │ stable under every common DenoteMetaSpine
        ↓
GuardedMembershipPreservation
```

This is not a renaming of the final relation. The annotated witness
`.const .punit [] → .sort 1` satisfies applicative simulation for every spine:
at the empty context, `pt` gives an actually transported membership from
`unitSet` to `univ 1`; after the first application, the source becomes `empty`,
which propagates through every later application. Yet `unitSet ≠ univ 1`,
because `empty` belongs to the target but not the source. The witness satisfies
the universal envelope and, by restriction, the readable-spine interface for
every producer context.
`readableApplicativeMembershipSimulation_strictlyWeakerThanEquality` therefore
packages the direct, non-vacuous non-converse at the exact interface level.

Finally, `aliasReadableApplicativeMembershipSimulationFails` and
`b0WAndWhnfDoNotDetermineReadableApplicativeMembershipSimulation` connect this
exact interface to the existing countermodel: its empty-spine projection,
which is always readable, would yield the already refuted guarded preservation.
Thus the relation is sufficient for the consumers, strictly weaker than
equality, and not reconstructible from `B0W` on this concrete unfolding.

The search for a local generator yields an exact characterization rather than
a new level of strength. `ReadableApplicativeGenerator` requires only two laws
of a relation on annotated readings: transport membership in the current
context, and remain closed when the same actually read argument is applied on
both sides. `LocallyGeneratedReadableSimulation` merely asserts the existence
of such a relation containing the head/body pair. The proofs establish

```text
LocallyGeneratedReadableSimulation
        ↔
ReadableApplicativeMembershipSimulation
```

The theorem `locallyGeneratedReadableSimulation_iff` fixes this equivalence.
The local-to-global direction is an induction over `DenoteMetaSpine`; the
converse takes the already obtained readable simulation as the relation, since
it is closed under one additional reading. The `.const .punit [] → .sort 1`
witness also separates this local presentation from semantic equality in
`locallyGeneratedReadableSimulation_strictlyWeakerThanEquality`, while
`aliasLocallyGeneratedReadableSimulationFails` refutes its existence from
`B0W` on the same δ.

This result therefore separates the **local generator** from its **contextual
closure**, but does not claim different logical strengths for them: at this
level of generality they are equivalent.

The producer audit then isolates a particular relation that mentions neither a
spine nor the completed simulation. `SemanticApplicativeSeed V before after`
preserves exactly two local determinations:

```text
before ⊆ after

∀ argument,
  app before argument = app after argument
```

`DeltaHeadBodySeed` requires this package between the interpretations of the
two annotated readings, uniformly in `ρ`. Semantic identity produces it, but
the exported conclusion is weaker. `deltaHeadBodySeed_of_delta` shows that
ConLeche's real `Delta` constructs this seed for the concrete readings before
and after unfolding; `deltaHeadBodySeed_of_acvalDefnInst` connects the upstream
producer currently in use.

This relation is locally closed under application. Inclusion supplies the
generator's observation law; after one argument, pointwise equality makes the
two results identical and therefore supplies both the new observation and
closure under the next argument. Thus:

```text
semantic identity
        ↓
DeltaHeadBodySeed
        ↓
ReadableApplicativeMembershipSimulation
        ↓
guarded consumers
```

Both levels are formally separated. At semantic-value level,
`unitSet ⊆ upair pt empty` is non-vacuous, both values return `empty` after
every application, yet they are unequal:
`semanticApplicativeSeed_strictlyWeakerThanEquality` therefore separates the
seed from identity without emptying its first clause. At annotated-reading
level, `deltaHeadBodySeed_strictlyWeakerThanEquality` also gives the
non-converse. Conversely,
`readableApplicativeSimulation_strictlyWeakerThanDeltaHeadBodySeed` constructs
a readable simulation that does not satisfy the seed. This last separator,
however, starts from a head interpreted by `empty`, so its simulation is
vacuous; it establishes the formal non-converse, not yet a non-vacuous strict
separation at that level.

Finally, `aliasDeltaHeadBodySeedFails` and
`b0WAndWhnfDoNotDetermineDeltaHeadBodySeed` show that the same `B0W` witness and
the same alias δ cannot reconstruct this producer relation: it would generate
the already refuted readable simulation.

The audit next tests the restriction suggested by readable arguments.
`ReadableDeltaSeed` preserves inclusion at the head but requires equality
after application only for an `argumentReading` produced by an attested
`denoteMeta` call in the fixed producer context. The theorems
`DeltaHeadBodySeed.toReadableSeed`, `readableDeltaSeed_generator`, and
`ReadableDeltaSeed.toReadableSimulation` establish:

```text
DeltaHeadBodySeed
        ↓
ReadableDeltaSeed
        ↓
ReadableApplicativeMembershipSimulation
```

The last converse fails formally in
`readableSimulation_doesNotDetermineReadableDeltaSeed`, although its separator
is still membership-vacuous. More importantly, the first arrow cannot yet be
claimed strict in the relevant δ case.
`ReadableDeltaSeed.toDeltaHeadBodySeed_of_valuationIndependent` shows that at
depth zero the readable seed reconstructs the universal seed whenever both
readings are independent of `ρ`. The reason is constructive: a `fvar` is read
as `.bvar 0`, whose value under `ρ` can then be chosen as any semantic
argument. Raw success of `denoteMeta` therefore does not define a semantically
restricted argument class for closed heads.

The producer is nevertheless genuinely factorized. The new
`AcvalDefnReadableSeed` interface carries only the readable relation between a
stored constant's reading and its instantiated body's reading. The theorem
`readableDeltaSeed_of_acvalDefnReadableSeed` opens the real
`unfoldDefinition`, recovers the same syntactic spine and the same argument
readings, and propagates that relation to the complete readings. Its proof
uses neither `Delta` nor equality of the complete annotations. The existing
`AcvalDefnInst` invariant constructs this interface in
`acvalDefnReadableSeed_of_acvalDefnInst`; the composed bridge
`readableDeltaSeed_of_acvalDefnInst_withoutDelta` therefore bypasses the
`Delta` theorem, although the current implementation of `AcvalDefnInst` still
supplies exact identity at the head/body boundary.

Finally, `aliasReadableDeltaSeedFails`,
`b0WAndWhnfDoNotDetermineReadableDeltaSeed`, and
`oldSlice_hasNoAcvalDefnReadableSeed` show respectively that the readable
relation, its reconstruction from `B0W + δ`, and the weakened producer contract
are all impossible on the same countermodel.

The next test does not introduce another variant of “readable.” It indexes the
capacity by the δ occurrence itself. In `DeltaSpineAdmission`, the
`DenoteMetaSpine` reading fixes the ordered `source.getAppArgs` list, while
`WScoped` and `CtxOk` are certified for each argument in that same list. The theorem
`deltaSpineAdmission_of_sourceRead` reconstructs exactly this package from the
source term's reading, scope, and context. The last two conditions certify the
operational admissibility of the occurrence; they are not artificially turned
into semantic premises.

`SemanticDeltaSpineSeed` then asks only for what this finite spine consumes. On
an empty spine it preserves head inclusion. On a nonempty spine it additionally
requires equality after the first semantic argument actually present. The
remaining applications are identical on both sides and propagate that equality
by congruence. `SemanticApplicativeSeed.toDeltaSpineSeed` directly formalizes
the restriction of the universal seed to any finite semantic spine; the
annotated bridges `DeltaHeadBodySeed.toAdmissibleDeltaSeed` and
`ReadableDeltaSeed.toAdmissibleDeltaSeed` perform the same projection on the
attested occurrence. `AdmissibleDeltaSeed` requires this package for every
valuation `ρ`, on the occurrence's exact readings, and
`AdmissibleDeltaSeed.toGuardedMembershipPreservation` recovers guarded
preservation on the complete δ term.

This restriction now yields a strict and non-vacuous reduction at semantic
level. In `semanticDeltaSpineSeed_strictlyWeakerThanUniversalSeed`, the tested
spine is empty: `unitSet` and `upair pt (kpair empty pt)` genuinely share the
member `pt`, so the required inclusion is not vacuous, while their applications
to `empty` differ. The occurrence seed holds and the universal
`SemanticApplicativeSeed` is refuted. This separator concerns an occurrence
with no argument; it does not yet separate both notions on every nonempty
spine.

The producer bridge is direct as well.
`admissibleDeltaSeed_of_acvalDefnReadableSeed` opens the real
`unfoldDefinition`, recovers both head readings and the same argument list,
constructs their `DeltaSpineAdmission`, then produces the occurrence seed from
`AcvalDefnReadableSeed`. It does not use equality of the complete readings.
Finally, `aliasDeltaSpineAdmission`, `aliasAdmissibleDeltaSeedFails`, and
`b0WAndWhnfDoNotDetermineAdmissibleDeltaSeed` show that on the concrete
empty-spine alias δ, `B0W` cannot reconstruct even this restricted interface:
its sole head-inclusion clause is already false.

The additional weakening therefore comes from the constitutive admissibility
of an **actually present use**—its finite spine and position—rather than merely
from an argument having a reading. Scope and context honestly fix that
occurrence; by themselves they do not produce the semantic transport.

The β audit was then developed independently from the frozen δ reference at
commit `d296630`, without importing a δ-specific audit interface.
`OperationalOccurrence` retains the exact β disjunct of `whnf_app_inv`: the
lambda head, instantiated-body run, and authorization accepted by the checker.
`SemanticConsequence` retains only redex/reduct equality and well-denotation of
the reduct.

The zero-kind branch factors through one guarded semantic capability:

```text
kind = 0 → interpretation(argument) ∈ interpretation(domain).
```

The fired-gate branch constructs it by making `kind = 0` impossible. In the
certificate branch, `InferClaimIOS` establishes membership in the inferred
argument type; `DefEqClaim` is then weakened successively to uniform membership
transport and to membership of the concrete argument in the concrete domain.
That last row is also the only result of this equality used by the full and IO
application-inference proofs. The same weakened line therefore feeds three
real consumers, while β itself consumes only its guarded form.

Lean directly separates four strengths:

```text
semantic equality
        ↓ strictly
uniform membership transport
        ↓ strictly
membership of the occurrence's argument in its domain
        ↓ strictly when the lambda kind is retained
the exact zero-kind β obligation
```

On a genuinely accepted zero-kind β occurrence, the existing `B0W`
countermodel constructs inferred-type membership but refutes semantic
agreement, uniform transport, concrete domain membership, and hence the exact
guarded β obligation. The first resistant dependency is consequently the
semantic transport from the inferred type accepted by the checker to the
lambda's stored domain, not inference of the argument itself.

This stabilizes the β analysis independently: the reusable producer-side
capability is uniform membership transport, while concrete domain membership
and its kind guard are the strictly weaker projections consumed downstream.
It proves neither global minimality, persistence in a future invariant,
reachability of the countermodel from the empty environment, nor a minimal
common factor with δ. The standalone β file recompiles against the
pinned ConLeche commit, contains no `sorry`, explicit `axiom`, `Classical`, or
`native_decide`, and has SHA-256
`709169dc75e510985a1501f2366b70f777ae88adf714ab84aaf7670f4bbcb9bf`.
Its axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`,
inherited from the pinned ConLeche development.

Only after both analyses were stabilized, a separate comparison imported their
complete module interfaces without changing either source. The theorem
`betaTransport_iff_deltaGuarded` proves that β's independently defined uniform
transport and δ's guarded membership preservation are definitionally the same
predicate when their context and endpoints coincide. Moreover, the established
δ occurrence seed projects to this predicate, while the predicate plus the
independently produced source membership yields β's concrete argument/domain
row. The shared structure is therefore the guarded transport rule, not either
producer's operational details or either consumer's particular judgement.

The comparison now also gives a direct, non-vacuous converse failure at the
level of these two predicates. `strictnessDeltaSource_unfolds` fixes a genuine
one-argument δ source with its unchanged spine. On the same admitted spine,
`strictnessCommonCapacity` transports the real member `ptTag`, while
`strictnessDeltaOccurrenceSeed_fails` refutes the occurrence seed: its head
observation would place `ptTag` inside a graph-regime lambda. Hence
`commonCapacity_doesNotReconstruct_deltaOccurrenceSeed` proves, in the
unrestricted class of matching indices,

```text
GuardedMembershipPreservation
        ↛
AdmissibleDeltaSeed.
```

This makes the δ occurrence-seed interface strictly stronger than the common
transport predicate in that class; on the β side, the common predicate is
exactly the independently isolated intermediate transport. The separator is
deliberately precise about its boundary: its operational source and nonempty
spine are genuine, but its two semantic head readings are chosen independently
of `AcvalDefnInst`.

The producer-restricted test is now closed in the opposite direction.
`acvalDefnInst_constructs_commonAndOccurrenceSeed` proves that, for every real
δ unfolding equipped with its actual source and target readings, scope, and
context certificate, `AcvalDefnInst` constructs a matching occurrence seed and
therefore its common guarded projection. Consequently,
`acvalDefnInst_excludes_commonWithoutOccurrenceSeed` rules out a real
producer-generated case in which the common transport holds while every
matching occurrence seed fails. This does **not** prove that the common
predicate alone reconstructs the seed. It proves something more specific to
ConLeche's current producer: the producer assumptions already reconstruct the
stronger interface without consuming the common predicate.

The logical ordering and the producer-relative ordering must therefore remain
distinct:

```text
unrestricted predicates:
AdmissibleDeltaSeed > GuardedMembershipPreservation

actual AcvalDefnInst outputs:
AcvalDefnInst → AdmissibleDeltaSeed → GuardedMembershipPreservation
```

No minimality in a class `K`, persistence claim, or reachability result from
the initial environment has been proved. The comparison file contains no
forbidden construct, has SHA-256
`e28b68ac45439ce8e377e16d16dc5ad2de0e0ac4c82b0d613ea0c78394df97fb`,
and its axiom audit again reports only the three dependencies inherited from
ConLeche.

The ι audit was then started independently of the δ and β interfaces, without
anticipating a common capability. `OperationalOccurrence` retains the exact
occurrence exposed by `iotaRec_inv`, after which `FiredRuleSelection` keeps
only the stored recursor, the rule actually selected, and the fact that it
fires. `recRuleLaw_of_selection` separately marks the entry of `RecRules`,
while `SemanticConsequence` and `ContinuationCertificate` distinguish the
result's semantic law from the guarantees needed to continue computation.

The first `.plain` test constructs an explicit environment with a genuine
`B0W` witness. A stored recursor has an operationally admissible rule whose RHS
is `PUnit PUnit.unit`. `badPlainRun` proves that `iotaRecFueled` really selects
and executes this rule in `verified` mode. Independently,
`badContinuationCertificate` proves that the reduct is well scoped, closed,
leaf bounded, and compatible with the empty context. Continuation is therefore
not the missing component.

The semantic law cannot be reconstructed. `badRhsReading` fixes the RHS's
exact reading. `badRhsHeadWellDenoted` and `badRhsArgumentWellDenoted` prove
that both constituents are individually well denoted. Yet
`badRhsHeadNotInPi` refutes, for every `v`, `A`, and `B`, membership of the
`PUnit` reading in `piR v A B`: at level zero an inhabitant would have to be
`pt`, while at a positive level it would have to be a graph, which `unitSet`
cannot be. `badRhsApplicationFrameFails` consequently refutes the shared
relational package required by `WellDenoted_app` without consuming either the
argument-domain membership or the level-zero condition.

Together, `badPlainRhsWellDenotedFails`, `badRecRulesFails`, and
`badPlainOperationalSemanticSeparator` establish:

```text
B0W + plain-rule selection + real iota execution + continuation
        ↛
well-denotation of the selected RHS.
```

The first internal cut is relational: individual validity of the constituents
does not determine their semantic composability. This separator does not show
that the other `WellDenoted_app` clauses are generally unnecessary, does not
yet analyze `.nested`, and does not claim that its environment is reachable
from the initial environment. The two ι files recompile against the pinned
ConLeche commit and respectively have SHA-256
`dd4b0f4dd7853eb637d19b350d0375f288f6607d399a0ab9901d8c3e40f24449`
and
`4d91808724ed2b25b030032fe8d0795a04d51c2a5d4ae02efc7c9a5c48a5ddbe`.
They contain no `sorry`, explicit `axiom`, `Classical`, or `native_decide`;
their audits report only `propext`, `Classical.choice`, and `Quot.sound`,
inherited from ConLeche.

These results do not yet cover every family of semantic judgements,
characterize a minimal relation, or justify persistence in `B1`. They prove
neither that `AcvalDefnInst` can be replaced inside ConLeche without changing
the upstream invariant, nor that the admissible seed is minimal, nor that the
countermodel is reachable from the empty environment.

In accordance with the stopping rule, neither the `WellDenoted` row for the
outer application's argument nor its propositional existential carrying the
shared frame has been tested. The old
witness remains arbitrary within the `B0W` class; reachability from the empty
environment is not claimed.

Thus `Q0` is not the sole additional obligation of a uniform factorization from
arbitrary `B0W` witnesses. In accordance with the stopping rule, `thm` and
`opaque` were not tested, no historical capacity `H` was proposed, and no
`B1` was introduced. The second old state is an admissible `B0W` witness; this
test does not claim that it is reachable from the empty environment through a
ConLeche run. `Pdenote` now exposes the failed row as a transition obligation,
and `pdenoteSeparator` packages the same concrete data as
`Nonempty (Separator B0W Pdenote)`. The propositional shadow is necessary
because the checker run and its fuel are obtained propositionally; it adds no
new scientific claim. The standalone adapter reproduces the relevant generic
interface without making either repository depend on the other. The external
file recompiles against the pinned commit, contains no `sorry`, explicit
`axiom`, or `native_decide`, and has SHA-256
`2709bd20f263cb6981860b690b944a1b32fb74d04089929ab9c9197360b7546c`.

Pinned references for this case study:

- [main theorem](https://github.com/leanprover/con-leche/blob/86cd20a65660d757cedc81561a44579099b565d0/ConLeche/MainTheorem.lean);
- [projection rewrite](https://github.com/leanprover/con-leche/blob/86cd20a65660d757cedc81561a44579099b565d0/ConLeche/Frontend/ProjRec.lean);
- [frontend application point](https://github.com/leanprover/con-leche/blob/86cd20a65660d757cedc81561a44579099b565d0/ConLeche/Frontend/ExportC.lean);
- [set-theory assumption](https://github.com/leanprover/con-leche/blob/86cd20a65660d757cedc81561a44579099b565d0/OVERVIEW.md#7-the-set-theory-assumption);
- [theorem boundaries](https://github.com/leanprover/con-leche/blob/86cd20a65660d757cedc81561a44579099b565d0/OVERVIEW.md#9-what-the-theorem-does-not-cover).

## 3. Formation chain

`VerificationPipeline` distinguishes four carriers and three transformations:

```text
Source
  │ exportStep
  ▼
Exported
  │ parseStep
  ▼
Parsed
  │ prepareStep
  ▼
Presented
```

`Accepted : Presented → Type` remains external to the pipeline. Defining the
three functions therefore creates no faithfulness witness.

`VerificationFidelity` separately introduces:

```text
FaithfulExport
FaithfulParse
FaithfulPrepare
```

`FaithfulRun` gathers the three witnesses at the occurrences actually computed.
`FaithfulComp` composes them through a dependent sum that retains intermediate
occurrences. `ConstitutivelyAccepted` then requires two fields that cannot be
reduced to one another: a `FaithfulRun` and terminal acceptance.

## 4. Acceptance/origin separator

`collapsedPipeline` sends the two distinct occurrences of
`Separators.twoStepHistory` to one terminal `Unit` value. That value is accepted
in the abstract terminal model.

A faithful occurrence realization would, however, require an `InjectiveMap`
into `Unit`. The existing theorem
`Separators.noFaithfulTerminalOnlyRealization` refutes it. The new theorem
`acceptedPresentation_doesNotDetermineOrigin` directly reuses this separator:
terminal acceptance does not reconstruct upstream occurrence identity.

## 5. Sufficient factorization for transporting `no False`

For a counterexample family `Counterexample : Occurrence → Type`, the module
defines:

```text
NoCounterexample Counterexample
```

Two obligations suffice for abstract negative transport:

1. `SourceCoverage` provides a presented occurrence for every relevant source
   occurrence;
2. `PreservesCounterexample` turns every source counterexample into the
   corresponding presented counterexample.

The theorem `transportNoCounterexample` then constructs:

```text
no presented counterexample
  → no source counterexample
```

The two components are tested independently:

- `coverage_isNecessary` uses an inhabited source and an empty presented
  carrier;
- `counterexamplePreservation_isNecessary` retains total coverage but makes
  counterexample transport impossible.

This is minimality relative to this property and this explicit finite family of
obligations, not absolute minimality over every possible representation.

## 6. Projection-rewrite case

At the studied commit, the ConLeche frontend recognizes certain functions whose
body is a primitive projection and replaces that body with a recursor
application. At the record level subsequently pushed, the name, stream
position, relevant prior context, and declared type remain unchanged; the body
is replaced.

`ConLecheProjectionCase` locally reconstructs this shape:

- `LocatedDeclaration` individuates a declaration and its context;
- `rewriteProjection` changes only `body`;
- `ProjectionRewriteWitness` explicitly retains name, position, prefix, and
  type, and witnesses the new body form;
- `projectionNoFalseTransport` transports absence of a `False`-typed
  declaration.

This reconstruction is a local model of the documented transformation's
observable contract. It is neither a copy of the frontend nor a theorem about
all of its code.

The minimization adds a further distinction.
`metadataErasureNoFalseTransport` shows that, for the abstract `no False`
property alone, name, position, prefix, and body can be forgotten together when
declared type and coverage are preserved. Those data may nevertheless remain
necessary to establish concrete faithfulness of the real implementation.

Conversely, `substitutedType_hasNoFaithfulRewrite` mutates the declared type and
refutes the rich rewrite witness even when the abstract terminal model still
accepts the object. Declared type is therefore not forgettable for the transport
under study.

## 7. Reproducible external audit

The script [`scripts/run_con_leche_audit.py`](../../scripts/run_con_leche_audit.py)
fixes the exported roots:

```text
StrongPerimetralTurning Cycle2 ConstitutiveAlignment
```

In confirmatory mode it checks the commit and clean tree, builds the repository,
verifies the manifest, regenerates the export, hashes it before and after
checking, and runs exactly:

```text
con-leche --verified --jobs=1 FILE.ndjson
```

Only exit code `0` and the exact line `accepted N declarations (--verified)`
close the run. External clones, builds, exports, and logs remain outside the
repository.

Windows example:

```powershell
py -3 scripts/run_con_leche_audit.py `
  --lean4export C:\external\lean4export\.lake\build\bin\lean4export.exe `
  --lean4export-source C:\external\lean4export `
  --lean4export-commit COMMIT_40_HEX `
  --con-leche C:\external\con-leche\.lake\build\bin\con-leche.exe `
  --con-leche-source C:\external\con-leche `
  --con-leche-commit COMMIT_40_HEX `
  --output-dir C:\external\audit-output `
  --confirmatory `
  --expected-head REPOSITORY_COMMIT_40_HEX
```

## 8. Exploratory compatibility run

An initial run closed the practical compatibility question for the development
that preceded this module. Its status remains `exploratory` because it did not
target a commit containing the present work.

```text
repository commit: 794b8185abba13eb4ab91f77a7c87fd1cd2d6ae0
repository Lean: v4.33.1, 819816b2e0a3bf405af45ae5c7af2491d8f5bee6
lean4export: 411dce7db58a3afc60ecab2d211acd1042b593dc
ConLeche: 86cd20a65660d757cedc81561a44579099b565d0
mode: --verified --jobs=1
export size: 375004155 bytes
SHA-256 before and after: 7622cc2e2b40f2f3341381f3d0f79e8d94599348e73637410a01a690cdfcc74d
verdict: accepted 63916 declarations
exit code: 0
```

This run shows that ConLeche built with Lean `v4.33.0` accepts this export
produced with Lean `v4.33.1`. It does not replace the confirmatory run that must
target the final scientific commit of this work.

After adding the reduced kernel and its separators, a second exploratory run
on the working tree accepted `64359` declarations. The export contained
`376371840` bytes; its SHA-256 remained
`61c4e260bf3740b068c5c57cb53f3da672c1b43e86e11ebcc80d59958ef9d052`
before and after checking. The external report has SHA-256
`655c9dbfcc587138c196549f9c4f5e25cb0745b22d286f8a11be4f35b68caf90`.
Its status remains exploratory because the work has not yet been committed.

## 9. Exact scope

The Lean layer constructively proves:

- separation of formation, faithfulness, and acceptance;
- separation of soundness, completeness, and provenance in the `R → S`
  contract;
- sufficiency of the terminal `{base2, type_reads, mem_type}` projection of the
  actual `EnvModelM`;
- a positive construction of the empty witness consumed by the capstone;
- descent of terminal extraction to the propositional shadow;
- passage from historical stability to weak stability;
- separator-based refutation of local reconstruction and of historical
  stabilities strong enough to provide it;
- localization, in the external ConLeche separator, of the failure to semantic
  agreement between the inferred and declared types alone;
- sufficiency of that `Q0` agreement to reconstruct both local rows for the
  concrete transition, with the other two facts constructed separately;
- a second separator showing that an arbitrary `B0W` witness plus an accepted
  `defn` transition does not reconstruct `valueWellDenoted`;
- its packaging as a transition-indexed `Pdenote` and a propositionally
  inhabited generic `Separator`;
- reconstruction of the head and argument readings of an applicative output
  from `base2` and `ValueFrontRun` alone, without consuming the terminal
  slice's other components, eta, or `ConstantValRun`;
- a third separator showing that these readings, the same `ValueFrontRun`, and
  a `B0W` witness do not determine `WellDenoted` for the annotated head;
- its internal localization: the lambda domain, the constant head of its
  applicative body, and the annotated argument are well-denoted, while the
  shared frame's `headInPiR` clause alone is already constructively impossible;
- the positive factorization of `headInPiR` through a membership row `M`, a
  reduction agreement `R` over the same inferred type, and the exact reading of
  the same reduced `forall`; in the countermodel, `M` is constructed and `R`
  is refuted;
- the local factorization of `R` in the δ branch through equality of the
  readings before and after the concrete unfolding; `Delta` and
  `AcvalDefnInst` suffice to produce it, while a `B0W` witness and the accepted
  `whnf` do not determine it in the countermodel;
- weakening `R` to oriented transport of the exact head membership; for this
  occurrence, where `M` is already constructed, that transport is equivalent
  to `headInPiR` and is therefore not yet a strict intermediate;
- a genuinely strict reduction from uniform semantic equality to uniform
  preservation of every membership judgement: equality implies this
  transport, the transport recovers the particular `headInPiR`, and a second
  concrete δ unfolding satisfies the transport non-vacuously while refuting
  equality;
- on the alias countermodel, non-reconstructibility of this uniform capacity
  from one and the same `B0W` witness, concrete `whnf`, and exact reading of its
  result;
- transversal weakening to `Sat`-guarded preservation, which replaces equality
  in the real `SortSemAt`, `SortSemAtIO`, and `StructEtaIrrel` consumers and
  remains non-reconstructible from `B0W` on the same unfolding in the empty
  context;
- the direct non-vacuous converse failure between this guarded preservation and
  equality, followed by the δ producer chain
  `AcvalDefnInst → Delta → reading identity → guarded preservation`;
- formal extraction of `delta_core`'s spine class: every finite
  `source.getAppArgs` list, unchanged and reapplied in the same order to the
  instantiated body, with no semantic premise at this layer;
- the local/global characterization of simulation on these readable spines: a
  relation that transports membership immediately and remains closed under
  every actually read argument generates exactly the readable simulation; this
  presentation is strictly weaker than equality but equivalent to its own
  contextual closure, and remains unreconstructible from `B0W` on the δ
  separator;
- producer-side extraction of `DeltaHeadBodySeed`, consisting only of head
  inclusion and agreement after one semantic application: the real δ constructs
  it, it generates readable simulation, a non-vacuous separator distinguishes
  it from identity at semantic level, another non-converse formally separates
  it from readable simulation, and the alias countermodel prevents its
  reconstruction from `B0W`;
- the controlled `ReadableDeltaSeed` test: its head/body relation suffices and
  propagates through the exact spine from a producer contract weaker than
  `Delta`, but raw `denoteMeta` success does not yet restrict semantic arguments
  for closed readings; a depth-zero `fvar` then recovers the universality of
  `DeltaHeadBodySeed`, while the same alias refutes both the readable seed and
  its producer contract from `B0W`;
- the subsequent restriction to the actually admitted δ occurrence:
  `DeltaSpineAdmission` binds reading, scope, and `CtxOk` to the exact positions
  of `source.getAppArgs`, while `SemanticDeltaSpineSeed` retains only head
  inclusion and, for a nonempty spine, agreement after its first actual
  argument; this seed suffices for guarded preservation of the complete term,
  a non-vacuous empty-spine separator distinguishes it from the universal seed,
  the weakened producer constructs it directly, and the same alias still
  prevents its reconstruction from `B0W`;
- an independent β factorization from the exact accepted occurrence to its
  semantic consequence, through the guarded zero-kind domain-membership
  obligation produced by the gate/certificate split;
- strict weakenings from inferred/domain semantic equality to uniform
  membership transport, then to concrete argument/domain membership, and
  finally to the kind-guarded obligation consumed by β; the unguarded row is
  also the exact equality-dependent result used by full and IO application
  inference;
- a genuine accepted zero-kind β separator on which inferred-type membership
  holds but every later relation in that chain is refuted from `B0W`;
- a post-hoc formal comparison proving that the independently extracted β
  transport and δ guarded preservation coincide definitionally at matching
  indices, that the δ occurrence seed projects to this shared relation, and
  that the shared relation plus source membership supplies the β occurrence
  judgement;
- a direct non-vacuous separator on one fixed nonempty admitted δ spine: the
  shared guarded transport preserves `ptTag`, while the occurrence seed is
  impossible; this proves the predicate-level non-converse, while the separator
  itself does not apply to semantic heads generated by `AcvalDefnInst`;
- closure of that producer-restricted question in the opposite direction:
  actual δ unfolding data plus `AcvalDefnInst` always construct a matching
  occurrence seed and its common projection, excluding a common-without-seed
  separator in this producer class without asserting that the common predicate
  alone reconstructs the seed;
- an independent ι factorization separating the operational occurrence, stored
  rule selection, semantic law supplied by `RecRules`, and continuation
  certificate;
- a `.plain` separator over a real `iotaRecFueled` execution: the `B0W` witness
  and every continuation guarantee are constructed, both RHS constituents are
  well denoted, but the head reading inhabits no `piR`; this refutes the shared
  application frame, RHS well-denotation, and the corresponding `RecRules`
  law;
- composition without erasing intermediate occurrences;
- an origin separator reusing the Cycle 1 kernel;
- sufficiency of coverage and counterexample preservation;
- their independent negative separators;
- faithfulness of the local rewrite model;
- admissible erasure of non-type metadata for `no False`;
- rejection of a declared-type substitution.

It does not prove full faithfulness of `lean4export`, the parser, or the ConLeche
frontend. The external run remains a reproducible observation. ConLeche's
guarantee remains relative to its set-theoretic model assumption. It does not
yet construct the terminal slice directly from `FullyChecked`: the available
induction passes through the full carrier. The second separator refutes a
uniform implication from arbitrary `B0W` witnesses, and the third does the same
at the annotated-head row; neither establishes that its old state is
checker-reachable from the empty environment. Finally,
ConLeche acceptance does not
replace this repository's `#print axioms` audits, which separately establish
that our principal theorems depend on no axioms.

## Design

> **Intellectual-design and AI-generation disclosure.** The project lead
> states that the essential ideas and research direction are their own. This
> document was written from A to Z by models in OpenAI's ChatGPT series, under
> human direction and through successive interactions. See the
> [full bilingual disclosure](../../AI_AUTHORSHIP.md).
