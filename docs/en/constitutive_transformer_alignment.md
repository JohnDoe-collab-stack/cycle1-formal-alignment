# Constitutive neural architecture for relative alignment

*Causal memory, succession, and transformer realization*

**English** | [Français](../fr/alignement_constitutif_transformers.md)

Navigation: [structural synthesis](structural_foundations.md) ·
[relative alignment](relative_alignment.md) ·
[reflective alignment](reflective_alignment.md) ·
[relational constitutive roles](relational_constitutive_roles_method.md)

## 1. Thesis

A constitutive neural architecture does not receive already individuated
objects and subsequently attach memory, control, and evaluation to them. It
constructs occurrences whose identity depends on their formation, relational
roles, and participation in a history. Numerical supports realize these
occurrences; they do not define them by themselves.

The architectural hypothesis is:

> **A neural machine can preserve identity, reason through succession, and
> localize a normative break if it faithfully transports the relations that
> constitute its occurrences, separates regime from norm, and makes every
> effectuation depend on a certificate indexed by the exact action.**

The transformer is one possible realization of the neural plane. It is neither
the principle of individuation, nor the norm, nor the admission regime.
Persistent memory, long-horizon reasoning, and the diagnosis of relative
hallucinations are applications of one architecture of constitution,
preservation, and exit.

This thesis is not grounded in an empirical promise. The repository already
provides its structural base. The machine-specific contracts and finite
instances are constructed in Lean; the finite numerical observation and every
trained-network generalization remain separately identified.

## 2. Starting formal results

Cycle 1 verifies in Lean a chain in which construction, realization, regime,
and norm remain distinct:

```text
presentation
→ dependently typed history
→ occurrences individuated by formation
→ exact roles and agreements
→ faithful realization
→ operational regime
→ autonomous norm
→ exact adequacy on the same histories
→ minimal positive continuation
→ localized exit from regime and norm
```

The main anchors are:

| Function | Lean identifiers |
| --- | --- |
| exact realization and residual role | `ExactInternalRealization`, `FaithfulExtension` |
| abstract regime exit | `RegimeExit`, `UniformRegimeExit` |
| history generated from a root | `RootedGeneratedHistory` |
| regime–norm adequacy | `NormativeAdequacy`, `AdequateAlong` |
| circular regime | `CircularRefinement` |
| autonomous circular norm | `CircularSpecificationSatisfaction` |
| soundness | `circularRefinement_soundSpecification` |
| completeness | `circularSpecification_complete` |
| minimal continuation | `oneStepAfterPerimeter` |
| norm-relative exit | `oneStepSpecRelativeHistoryExit` |

`CircularRefinement P H` and `CircularSpecificationSatisfaction P H` are
witness types. The repository constructs a transformation in each direction.
At the propositional level, their inhabitance is therefore equivalent:

```text
Nonempty (CircularRefinement P H)
↔
Nonempty (CircularSpecificationSatisfaction P H)
```

This adequacy does not prevent construction from continuing.
`oneStepAfterPerimeter` is positively formed, has a faithful realization, and
leaves both the regime and the norm on the same continuation.

Cycle 2 then lifts adequacy to represented statuses:

```text
exact representation of determined statuses
+ a diagonal status outside the representation regime
→ no global reflective closure
```

The corresponding identifiers are `Represents`, `InternallyRepresentable`,
`PullbackStatus`, `transportRepresentation`,
`diagonalStatus_notRepresentable`, and `noGlobalReflectiveClosure`.

## 3. Architectural consequence of non-closure

Non-closure removes nothing from the exactness already constructed. It forbids
turning exact representation of determined statuses into a claim that every
status of the machine has one total internal representation.

The target architecture is therefore dynamic, relative, and locally
determined:

```text
a determined regime
↔ an autonomous norm on the same objects
→ exactness within that scope
+ the possibility of an outside status
→ succession or explicit exit, never postulated global closure
```

The machine does not certify itself globally. It transports witnesses within a
declared scope, exactly represents some statuses, and preserves a positive exit
when an operational, normative, or representational boundary is reached.

This consequence motivates the architecture below but does not replace its
contracts. Every transport, admission, effectuation, and succession must still
be constructed.

## 4. Abstract constitutive machine

The fundamental machine is independent of any neural implementation:

```lean
State : Type
Step  : State → State → Type
```

A history is a proof-relevant composition of steps. An occurrence is indexed by
the history that formed it and can retain its formation step, source and target
states, structural position, constitutive dependencies, provenance, and open
obligations.

The same reading may therefore correspond to two different occurrences when
their formations differ. Conversely, two material supports realize the same
occurrence only when a faithful correspondence is constructed.

A role is not a label such as `fact`, `memory`, or `error`. It is a relational
requirement on which participation in the construction depends. An agreement
states that a determined occurrence realizes that role:

```lean
Agreement
  (history : History)
  (role : Role)
  (occurrence : History.Occurrence history) : Type
```

An exact realization supplies an injective map from required roles to realized
occurrences and an agreement for every role. It does not require every future
occurrence to have a role in the current family. That asymmetry permits
continuation without erasing established local exactness.

`ConstitutiveMachine` reuses Cycle 1 histories and occurrences directly.
`circularMachine` is an adapter over the existing circular construction, and
`circularMachineAdequacy` transports its soundness and completeness without
redefining either regime or norm.

## 5. Four planes and five distinctions

The architecture separates four planes:

```text
constitutive plane       formation, occurrences, roles, histories
formal-normative plane   regime, norm, adequacy, proofs
operational plane        actions, effects, memory, consumed traces
neural plane             activations, parameters, predictions, proposals
```

The planes communicate through explicit realizations and certificates. They
are not identified.

For a history `H` and candidate `x`, five families remain distinct:

```text
C(H, x)   internal construction of x
F(H, x)   faithful realization of x
R(H, x)   admission of x by the regime
S(H, x)   satisfaction of the autonomous norm
E(H, x)   governed effectuation of the action carried by x
```

Relative alignment is adequacy between `R` and `S` on the same objects. It is
not a score, a preference, or a comparison of terminal outputs. Effectuation is
different again: it determines what the system may do after admission.

The structuring separations are:

```text
construction          ≠ realization
realization           ≠ admission
admission             ≠ normative satisfaction
norm                  ≠ adequacy of the regime
proposal              ≠ incorporation
learning              ≠ constitutive succession
trace composition     ≠ causal dependence
one-step causality    ≠ multicycle autonomy
operational exit      ≠ representational exit
```

## 6. Memory relative to relevant futures

Persistent memory is neither complete storage of a history nor later access to
similar text. It preserves exactly those differences required by declared
future behaviours.

```lean
Question : Type
Answer : Question → Type
behaviour : State → (q : Question) → Answer q
```

Two states are future-equivalent when every declared question receives the same
answer. `MemorySound` says that equal memory implies this equivalence.
`MemoryComplete` says that future-equivalent states share a memory value.
`ExactCausalMemory` keeps both directions separate and then packages them.

Consequently:

- equal memory licenses contraction only for the declared future family;
- one declared future distinction prevents fusion by a sound memory;
- retaining the whole state can be sound without being complete relative to a
  coarser future;
- changing the question family can invalidate a formerly exact contraction.

`AutonomousMemoryUpdate` requires the memory update to commute with the actual
state transition. The next memory value is computed from the previous memory;
it is not supplied as a correct external fixture.

## 7. Normative admission and effectuation

An action is a value before it is an effect. `ConstitutiveAction` records its
nature, target, parameters, declared constitutive context, scope, and requested
effector.

`NormativeExecutor` keeps three indexed families distinct:

```text
Admission context action
Norm context action
Certificate context action
```

The certificate is indexed by the exact action and context. A certified
effectuation yields an admission witness and, through soundness, a normative
witness:

```text
effectuation → admission → norm
```

Without a certificate, no value of `CertifiedEffectuation` can be built. The
finite separators show that another target, an expired context, or a modified
action cannot reuse the valid certificate. A deliberately unmediated bypass is
represented separately to demonstrate why diagnosis alone cannot prevent an
effect.

`FormationFailure`, `OperationalExit`, and `NormativeFailure` are also distinct
types. Under explicit adequacy, operational and normative exits can be
transported in either direction without identifying the underlying notions.

## 8. One-step constitutive learning causality

Placing learning, prediction, and proposal in the same log establishes no
causal dependence. The required contract is:

```text
parent predictive state
→ effective learning
→ learned predictive state
→ changed learned prediction
→ prediction consumed as a constitutive input
→ changed constitutive proposal
→ exact succession
```

Two controlled trajectories share the problem, constitutive state, proposal
producer, randomness, budget, and authorized view. Their only initial variation
is the parent or learned predictive state.

`OneStepLearningCausality` then requires distinct predictions, exact
consumption of each prediction, distinct proposals, a fixed parent rejection
reason, and a constructed learned succession. A constant-proposal separator
shows that changed predictions alone do not establish influence on the
proposal.

`FreshProbeCausality.lean` closes the acquisition side of this intervention.
It separates the training corpus from the evaluation probe, binds both by one
unique commitment, constructs a refutation that the probe belongs to the
training corpus, and runs parent and learned states on the same authorized
probe view. The learned state produced by that training procedure is exactly
the fixed weight state used by the finite-depth transformer dynamics. This is
a constructive finite instance, not an assumption that arbitrary trained
weights satisfy the contract.

This one-step result is a necessary condition of the target machine. By itself,
it is not a proof of multicycle autonomy.

## 9. Constitutive succession and long horizon

Three transitions are formalized separately:

```text
parametric learning        parameters → parameters
constitutive incorporation state → extended state
normative succession       regime → successor regime
```

`ConstitutiveSuccession` explicitly witnesses the agreement between
independently defined incorporation and normative succession.
`UniformTransition` defines one operator for every depth, while `iterateState`
and `iterateHistory` recursively consume the state actually produced by the
previous step.

Declared obligations are preserved under finite composition.
`PartialTransition` represents either a constructed next step or a positive
refutation that the next step can be formed; stopping is therefore explicit and
inspectable.

`ReferenceModel.lean` closes these obligations in one integrated finite
instance. The same candidates and states connect proof-relevant histories,
independently defined regime and norm, faithful realization, exact memory,
governed action, formation failure, the controlled parent–learned pair,
operational and normative exit, and reflective non-closure. Its learned
candidate is exactly the admitted and effectuated candidate; its parent
candidate is exactly the faithful continuation rejected by the regime, the
norm, and governed effectuation. The model also constructs two cycles with the
same operator and proves that the second consumes the first output after the
first memory update has reconfigured its input.

The relevant horizon is structural rather than token-count based. A long token
sequence may break early at the structural level, while a compressed sequence
may remain faithful if the required relations are transported.

`TransformerDynamics.lean` instantiates the same discipline on the finite
hard-attention core. One uniform operator runs with the same learned weights,
incorporates the produced proposal as the next relation, and runs again on that
produced view. A dedicated ablation keeps tokens, cache, memory, budget, core,
and weights fixed while omitting only this incorporation; both the second
prediction and the second proposal then change. This establishes finite
two-cycle autonomy in the declared model.

`GovernedDynamics.lean` then generalizes this dynamic to every finite depth
`n : Nat` without introducing a cycle catalogue. `viewAt n` is produced by the
same operator; `reachableTransformerAt n` carries its forming history; and
`proposalIsNextConsumedRelation n` establishes that the proposal at rank `n`
is exactly the relation consumed at rank `n + 1`. `GovernedInvariant` aggregates
at every reached state trajectory fidelity, exactness and retention of the
declared memory, regime–norm adequacy, the candidate's normative status,
retention of its elaboration, and confinement of any governed effect. Its
one-step law is composed by `preservesAlongIteration`, constructing the
invariant for every finite horizon. Ablating the active relation changes the
prediction, the proposal, and therefore the next produced state at every depth
of this instance, while bounded stopping remains an explicit constructive
result.

## 10. Neural realization

The neural plane receives an authorized view. Proofs, future verdicts, exact
targets, and audit outputs are not fields of that view.

The realization chain is:

```text
latent state
→ discrete proposal
→ total elaboration
→ accepted candidate or first localized error
```

Elaboration never repairs a proposal. Invalid candidates remain representable
and auditable.

`FullTrajectoryRealization` links every constitutive occurrence to an actually
consumed operational occurrence through an injective map. Terminal equality or
vector similarity is insufficient.

`NeuralCausalTrace` records the learned state, produced prediction, exact
consumed prediction, proposal, and elaboration as primary causal data. The
trace is sealed before `DeferredAudit`; the audit returns a report without
modifying the primary trace.

## 11. Transformer realization

`TransformerCore` instantiates the neural plane with explicit tokens,
activations, cache, addressable memory, constitutive relation, weights,
prediction, proposal, and total elaboration. Its logits do not define identity,
norm, or admission.

The finite one-step instance proves:

- effective learning changes the prediction;
- the produced prediction is the one consumed by proposal construction;
- the proposal changes under the controlled parent–learned intervention;
- the parent proposal is rejected for a fixed reason;
- the learned proposal is accepted and has an exact succession witness;
- changing an active constitutive relation changes the future prediction;
- removing that relation from the control computation makes the intervention
  inert;
- coherently renaming a memory address and its store preserves the prediction;
- the learned proposal becomes the exact relation consumed by a second run of
  the same core, and ablating that relation changes the continuation;
- the Boolean relation forms the query of a two-key hard-attention head whose
  address renaming is proved equivariant;
- the rejected proposal decodes to the reference-model operational exit, while
  the learned proposal decodes to its admitted, normative, governed action;
- the rejected proposal remains present in the elaboration trace.

This closes the stated one-step obligations on a finite constructive
hard-attention realization. The one-step module alone is not a multicycle
result, but its composition in `TransformerDynamics.lean` and then
`GovernedDynamics.lean` constructs, respectively, two causally linked cycles
and governed dynamics at every finite depth. It is not a trained transformer, a
formalization of floating-point softmax-attention tensors, or an infinite-horizon
result.

## 12. Memory, normative break, and relative hallucination

Memory is established within a scope when states fused by memory are
indistinguishable under every declared question. Compression without that
certificate remains an implementation hypothesis.

The finite transformer memory is exact for both hard-attention queries and is
preserved by relation incorporation. Its summary retains the two values needed
by those futures while excluding the technical focus address.

A relative hallucination may be defined as a constructed and faithfully
realized candidate whose autonomous norm is refuted. The definition is relative
to the explicitly selected norm. It does not turn every regime exit or every
linguistic error into a hallucination.

The finite relative-hallucination witness contains one and the same candidate,
its constructed history, faithful injective realization, preserved rejected
proposal, and refutation of the autonomous norm. The candidate is exactly the
operational and normative exit, and its corresponding governed action cannot
be effectuated. Internal construction is preserved; only certified external
effect is confined.

The target witness retains on the same candidate:

```text
positive formation
+ faithful realization
+ preserved prior structure
+ refuted first normative obligation
+ impossibility of the corresponding governed effect
```

The machine thereby localizes the break without denying that construction
continued. The rejected continuation remains available to audit, while
certificate-governed effectuation is confined.

## 13. Formal program

The new modules follow their dependency order:

| Module | Main obligation | Current status |
| --- | --- | --- |
| `Machine.lean` | constitutive interface connected to Cycle 1 histories | proved |
| `CausalMemory.lean` | exactness relative to declared futures and update law | proved, with finite separators |
| `NormativeExecution.lean` | action, certificate, and governed effectuation | proved, with separate unmediated path |
| `NormativeFailure.lean` | non-neural, distinct failure diagnostics | proved |
| `Succession.lean` | uniform iteration, normative connection, explicit stop | proved generically and finitely |
| `LearningCausality.lean` | learning causes the next proposal at one step | contract and finite instance proved |
| `ReflectiveMachine.lean` | machine instance of exact representation and non-closure | proved |
| `ReferenceModel.lean` | one integrated finite certificate from histories and adequacy to causal succession, governed action, linked cycles, and reflective exit | proved |
| `NeuralRealization.lean` | neural fidelity contract and deferred audit | defined and proved on a finite instance |
| `TransformerRealization.lean` | transformer contract, hard attention, proposed-relation consumption, and parent–learned intervention | finite one-step gate proved; multicycle developed in `TransformerDynamics.lean` |
| `TransformerDynamics.lean` | exact attention memory, uniform two-cycle feedback, intercycle ablation, relative normative break, and confinement | proved on the finite hard-attention instance |
| `FreshProbeCausality.lean` | committed training/probe split, constructive freshness, and exact use of the acquired weights | proved on the finite hard-attention instance |
| `GovernedDynamics.lean` | proof-relevant reachability, governed invariant, admissible evolution, and arbitrary-finite-depth transformer dynamics | constructively proved for every `n : Nat` |
| `ExecutableRefinement.lean` | canonical discrete boundary, exact refinement, linked traces, and negative separators | constructively proved for every `n : Nat` |
| `TypedProgramDomain.lean` | total intrinsically typed language, finite rank-free frontier, regime, norm, and adequacy | constructively proved on the finite instance |
| `EndogenousTypedSuccession.lean` | one operator over two transitions, actual successor-corpus consumption, two counterfactuals, generated probe, and exact refinement | constructively proved on the finite instance |
| `experiment/protocol_v1.py` | numerical softmax-attention prototype, disjoint training/probe split, immutable traces, controls, and deferred audit | confirmatory run passed on three precommitted seeds after source freeze |
| `experiment/verify_refinement_v1.py` | read-only frozen-hash, probe-identity, trace, boundary, and negative-mutation verification | 3 runs and 24 traces accepted; 8 mutations rejected |
| `experiment/typed_program/` | separate executable typed self-extension witness, cumulative ledger, and exact worker requests | smoke test and 12 negative mutations passed; confirmatory run awaits the freeze commit |

The `ConstitutiveAlignment.lean` facade imports the leaves of this graph. Cycle
1 and Cycle 2 files remain the formal authority; the new modules construct
bridges and do not redefine their results.

Every new Lean file is constructive, contains no `axiom`, `sorry`, `Classical`,
`propext`, or `Quot.sound`, and ends in one `AXIOM_AUDIT` block.

## 14. Implementation order and gates

The closure order is:

```text
abstract machine
→ memory and effectuation
→ succession and generic causal contract
→ reflective layer
→ finite reference model
→ abstract neural realization
→ one-step transformer instance
→ two-cycle transformer dynamics
→ governed invariant at every finite depth
→ admissible evolution and adequacy transport
→ refinement of the executable discrete boundary
→ reproducible experimental protocol
→ typed self-extension through two passes of the same operator
→ dynamic generated-probe protocol and cumulative ledger
```

The numerical protocol requires separate fixed smoke and confirmatory probes,
both disjoint from the training set and from each other by identifier and
authorized view. A smoke run does not execute the confirmatory probe. The
protocol also checks absence of
forbidden targets from the neural view; identity between produced and consumed
prediction; proposal change under the parent–learned intervention on that same
probe; consumption of the true successor state; intercycle ablation;
preservation of invalid candidates; immutable traces and causally silent audit;
and controls, seeds, and criteria fixed before its confirmatory run.

A failed gate remains a localized result. It may not be bypassed through a
silent protocol change or an implicit weakening of the claim.

## 15. Exact status

The repository currently proves:

- the dependently typed structural kernel;
- abstract and concrete operational exit;
- exact adequacy between the circular regime and its autonomous norm;
- a minimal faithfully realizable continuation that leaves both;
- exact representation of determined statuses together with a nonrepresentable
  diagonal status and global reflective non-closure;
- future-relative exact memory, non-fusion, and an autonomous finite update;
- impossibility of governed effectuation without an exact certificate and the
  chain `effectuation → admission → norm`;
- typed separation of formation failure, regime exit, and normative failure;
- uniform iteration, obligation preservation, explicit stopping, and an
  explicit connection between incorporation and normative succession;
- one-step causality from learning through consumed prediction and changed
  proposal to parent rejection and learned succession;
- a fixed fresh-probe acquisition witness whose training corpus and probe are
  constructively disjoint, whose commitment prevents probe substitution, and
  whose acquired weights are exactly those used by the finite-depth dynamics;
- one integrated finite reference model with same-reading/different-formation
  occurrences, exact memory, independent regime and norm, faithful parent and
  learned branches, governed action, distinct exits, linked cycles, and a
  represented status with the diagonal outside;
- a four-plane neural interface, non-repairing elaboration, trajectory
  fidelity, and causally silent deferred audit;
- a transformer realization interface and finite hard-attention one-step
  instance whose learned proposal is consumed as the next relation, with active
  relation, inert control, address-renaming invariance, and an exact bridge to
  the reference-model exit, norm, and governed action;
- finite two-cycle transformer dynamics under one uniform operator and fixed
  learned weights, with exact proposal-to-relation feedback, exact attention
  memory, a dedicated intercycle ablation, and confined relative normative
  failure;
- transformer dynamics constructed for every finite depth `n : Nat`, where
  every state carries its forming history and every proposal becomes exactly
  the relation consumed by the next cycle;
- a governed invariant preserved at every such reachable state, combining
  without identifying them fidelity, memory, adequacy, normative status,
  elaboration retention, and effect confinement;
- an admissible-evolution contract separating parametric learning,
  incorporation, memory update, adequacy transport, and injective action and
  certificate transport;
- a discrete executable boundary exactly refining the formal trace at every
  finite depth, with constructive rejection of a rewritten candidate, a forged
  effect, and a missing intercycle link; certificate and effectuation statuses
  are indexed by the exact candidate-derived action and constitutive context.
- a finite intrinsically typed language with total semantics, a rank-free
  frontier, and two transitions through the same `typedStep`, where the second
  consumes exactly the corpus produced by the first;
- divergence of the second obligation when first incorporation is removed, and
  disappearance of the second proposal when `T₁` is preserved but prior
  weights are restored;
- a formal generated-probe protocol from a sealed descriptor and reserved seed,
  together with exact refinement rejecting a rewritten proposal and a target
  corpus missing its first incorporation.

Separately from these theorems, the canonical numerical protocol was frozen in
commit `a4b9a44` before its confirmatory probe was executed. Its training set,
smoke probe, and confirmatory probe are pairwise disjoint. On all three
precommitted seeds, learning changes the proposal on `confirmatory-0`; the first
proposal is consumed as the second relation; intercycle ablation changes the
second proposal; and deferred audit preserves the sealed traces. The read-only
verifier accepts all 24 traces and rejects eight negative mutations. Lean does
not parse the JSON result: formal `TraceRefinement` and executable acceptance
remain distinct controls.

The separate `experiment/typed_program/` executable protocol has passed its
smoke test and twelve negative mutations. It has no confirmatory result yet:
that run is technically blocked until the new sources are frozen by a clean
commit.

The repository does not yet prove:

- a production-scale trained transformer realization or an actually infinite
  trajectory;
- faithful realization by a trained network and its actual tensors;
- an empirical result about linguistic hallucinations.

These remain ordered obligations, not anticipated conclusions. The boundary
between Lean theorems, contracts, implementations, and observations remains
explicit.

## Design

> **Intellectual-design and AI-generation disclosure.** The project lead
> states that the essential ideas and the research direction of this project
> are their own. This document was written from A to Z by models in OpenAI's
> ChatGPT series, under human direction and through successive interactions.
> See the [full bilingual disclosure](../../AI_AUTHORSHIP.md).
