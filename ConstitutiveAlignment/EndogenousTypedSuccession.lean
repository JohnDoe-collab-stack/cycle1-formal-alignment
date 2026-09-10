import ConstitutiveAlignment.TypedProgramDomain
import ConstitutiveAlignment.FreshProbeCausality

set_option linter.checkUnivs false

/-!
# Endogenous typed-program succession

One transformer operator learns one additional unit of compositional capacity,
proposes the current corpus frontier, incorporates the certified abstraction,
and returns the exact corpus consumed by the next invocation.  The frontier has
no cycle ordinal input.  A generated-probe certificate binds the held-out probe
to a sealed competence descriptor and a precommitted seed.
-/

namespace ConstitutiveAlignment
namespace EndogenousTypedSuccession

open TypedProgram

def frontierFormation? (corpus : ProgramCorpus) : Option Formation :=
  (programFrontierCandidate corpus).map
    CertifiedProgramAbstraction.formation

def hasCapacity (capacity : Nat) (formation : Formation) : Bool :=
  decide (formation.depth ≤ capacity)

def proposalFor (capacity : Nat) (corpus : ProgramCorpus) :
    Option CertifiedProgramAbstraction :=
  match programFrontierCandidate corpus with
  | none => none
  | some candidate =>
      if hasCapacity capacity candidate.formation then some candidate else none

inductive CapacityLearningEvidence : Nat → Nat → Type
  | increment (capacity : Nat) :
      CapacityLearningEvidence capacity (Nat.succ capacity)

inductive ProgramProposalError : Type
  | insufficientCapacity

def programCore : TransformerCore where
  Token := Unit
  Activation := Unit
  Cache := Unit
  MemoryReference := Unit
  Relation := ProgramCorpus
  Weights := Nat
  LearningEvidence := CapacityLearningEvidence
  learn := Nat.succ
  learningEvidence := CapacityLearningEvidence.increment
  Prediction := Option CertifiedProgramAbstraction
  Proposal := Option CertifiedProgramAbstraction
  Candidate := CertifiedProgramAbstraction
  Error := LocalizedError ProgramProposalError
  activate := fun _tokens => ()
  predict := fun capacity _activation view =>
    proposalFor capacity view.relation
  propose := fun _view prediction => prediction
  elaborate
    | none => .rejected ⟨0, .insufficientCapacity⟩
    | some candidate => .accepted candidate

def viewFor (corpus : ProgramCorpus) :
    TransformerAuthorizedView Unit Unit Unit ProgramCorpus :=
  { tokens := [()]
    cache := ()
    memory := ()
    relation := corpus
    budget := 3 }

structure TypedStage where
  corpus : ProgramCorpus
  capacity : Nat

def initialStage : TypedStage :=
  ⟨initialCorpus, 1⟩

def firstStage : TypedStage :=
  ⟨firstSuccessorCorpus, 2⟩

def secondStage : TypedStage :=
  ⟨secondSuccessorCorpus, 3⟩

def typedStep (stage : TypedStage) : Option TypedStage :=
  let learnedCapacity := programCore.learn stage.capacity
  let proposal := proposalFor learnedCapacity stage.corpus
  match proposal with
  | none => none
  | some proposed =>
      some ⟨stage.corpus.incorporate proposed, learnedCapacity⟩

inductive TypedStep : TypedStage → TypedStage → Type
  | exact {source target : TypedStage} :
      typedStep source = some target → TypedStep source target

def firstStep_reconstructsCorpus : TypedStep initialStage firstStage :=
  .exact rfl

def secondStep_consumesFirstSuccessor : TypedStep firstStage secondStage :=
  .exact rfl

def firstHistory :
    StrongPerimetralTurning.History TypedStep initialStage firstStage :=
  .extend .root firstStep_reconstructsCorpus

def secondHistory :
    StrongPerimetralTurning.History TypedStep initialStage secondStage :=
  .extend firstHistory secondStep_consumesFirstSuccessor

def withoutFirstIncorporation : TypedStage :=
  ⟨initialCorpus, firstStage.capacity⟩

theorem incorporationAblation_keepsPriorFrontier :
    frontierFormation? withoutFirstIncorporation.corpus =
      some doubleNegateAbstraction.formation :=
  firstFrontier_isDoubleNegate

theorem firstIncorporation_changesSecondObligation :
    frontierFormation? withoutFirstIncorporation.corpus =
      frontierFormation? firstStage.corpus → False :=
  firstIncorporation_changesNextFrontier

theorem firstIncorporation_changesFrontierSemantics :
    doubleNegateAbstraction.evaluate false =
      tripleNegateAbstraction.evaluate false → False := by
  intro equality
  nomatch equality

def firstParentTrace :=
  programCore.run initialStage.capacity (viewFor initialStage.corpus)

def firstLearnedTrace :=
  programCore.run (programCore.learn initialStage.capacity)
    (viewFor initialStage.corpus)

def secondParentTrace :=
  programCore.run firstStage.capacity (viewFor firstStage.corpus)

def secondLearnedTrace :=
  programCore.run (programCore.learn firstStage.capacity)
    (viewFor firstStage.corpus)

theorem firstParent_hasNoProposal :
    firstParentTrace.causal.proposal = none :=
  rfl

theorem firstLearned_proposesFirstFrontier :
    firstLearnedTrace.causal.proposal.map
      CertifiedProgramAbstraction.formation =
      some doubleNegateAbstraction.formation :=
  rfl

theorem secondParent_hasNoProposal :
    secondParentTrace.causal.proposal = none :=
  rfl

theorem secondLearned_proposesSecondFrontier :
    secondLearnedTrace.causal.proposal.map
      CertifiedProgramAbstraction.formation =
      some tripleNegateAbstraction.formation :=
  rfl

theorem restoredPriorCapacity_changesSecondProposal :
    secondParentTrace.causal.proposal =
      secondLearnedTrace.causal.proposal → False := by
  intro equality
  nomatch equality

/-! ## Probe generated from a sealed descriptor -/

structure CompetenceDescriptor where
  sourceCorpus : ProgramCorpus
  obligation : Formation

structure SealedDescriptor where
  descriptor : CompetenceDescriptor
  marker : Unit

inductive ReservedSeed : Type
  | secondStage

structure DynamicProbe where
  corpus : ProgramCorpus
  obligation : Formation

def generateProbe
    (sealed : SealedDescriptor)
    (_seed : ReservedSeed) : DynamicProbe :=
  { corpus := sealed.descriptor.sourceCorpus
    obligation := sealed.descriptor.obligation }

def secondDescriptor : SealedDescriptor :=
  { descriptor :=
      { sourceCorpus := firstSuccessorCorpus
        obligation := tripleNegateAbstraction.formation }
    marker := () }

def generatedSecondProbe : DynamicProbe :=
  generateProbe secondDescriptor .secondStage

def probeSignature (probe : DynamicProbe) : Formation :=
  probe.obligation

def trainingCorpus : List Formation :=
  [doubleNegateAbstraction.formation]

def priorProbeLedger : List Formation :=
  [doubleNegateAbstraction.formation]

def probeInTraining
    (corpus : List Formation)
    (probe : DynamicProbe) : Prop :=
  List.Mem probe.obligation corpus

inductive ProgramTrainingEvidence :
    List Formation → Nat → Nat → Type
  | empty (capacity : Nat) : ProgramTrainingEvidence [] capacity capacity
  | nonempty (head : Formation) (remaining : List Formation) (capacity : Nat) :
      ProgramTrainingEvidence (head :: remaining) capacity (Nat.succ capacity)

def trainCapacity : List Formation → Nat → Nat
  | [], capacity => capacity
  | _head :: _remaining, capacity => Nat.succ capacity

def trainingProcedure : TransformerTrainingProcedure programCore where
  Corpus := List Formation
  Probe := DynamicProbe
  InCorpus := probeInTraining
  train := trainCapacity
  TrainingEvidence := ProgramTrainingEvidence
  trainingEvidence
    | [], capacity => .empty capacity
    | head :: remaining, capacity => .nonempty head remaining capacity
  view := fun probe => viewFor probe.corpus

inductive ProbeCommitment : Type
  | canonical

inductive ProbeBinding :
    ProbeCommitment → List Formation → DynamicProbe → Type
  | canonical :
      ProbeBinding .canonical trainingCorpus generatedSecondProbe

theorem generatedSecondProbe_isFresh :
    probeInTraining trainingCorpus generatedSecondProbe → False := by
  intro membership
  nomatch membership

theorem generatedSecondProbe_absentFromPriorLedger :
    List.Mem (probeSignature generatedSecondProbe) priorProbeLedger → False := by
  intro membership
  nomatch membership

def fixedGeneratedProtocol : FixedFreshProbeProtocol trainingProcedure where
  corpus := trainingCorpus
  probe := generatedSecondProbe
  Commitment := ProbeCommitment
  commitment := .canonical
  Binds := ProbeBinding
  bound := .canonical
  bindingUnique := by
    intro otherCorpus otherProbe binding
    cases binding
    exact ⟨rfl, rfl⟩
  fresh := generatedSecondProbe_isFresh

structure GeneratedFreshProbeProtocol where
  sealed : SealedDescriptor
  seed : ReservedSeed
  generated : DynamicProbe
  generatedExact : generated = generateProbe sealed seed
  generationUnique : (other : DynamicProbe) →
    other = generateProbe sealed seed → other = generated
  fixed : FixedFreshProbeProtocol trainingProcedure
  trainingExact : fixed.corpus = trainingCorpus
  probeExact : fixed.probe = generated
  priorLedger : List Formation
  absentFromPriorLedger :
    List.Mem (probeSignature generated) priorLedger → False

def generatedProtocol : GeneratedFreshProbeProtocol :=
  { sealed := secondDescriptor
    seed := .secondStage
    generated := generatedSecondProbe
    generatedExact := rfl
    generationUnique := by
      intro other equality
      exact equality
    fixed := fixedGeneratedProtocol
    trainingExact := rfl
    probeExact := rfl
    priorLedger := priorProbeLedger
    absentFromPriorLedger := generatedSecondProbe_absentFromPriorLedger }

theorem generatedProbe_isBoundToSealedDescriptor :
    generatedProtocol.fixed.probe =
      generateProbe generatedProtocol.sealed generatedProtocol.seed := by
  rw [generatedProtocol.probeExact, generatedProtocol.generatedExact]

theorem acquiredCapacity_isSecondLearnedCapacity :
    fixedGeneratedProtocol.learnedState firstStage.capacity =
      programCore.learn firstStage.capacity :=
  rfl

def secondIntervention : NeuralIntervention programCore.toNeuralSystem
    firstStage.capacity
    (fixedGeneratedProtocol.learnedState firstStage.capacity)
    fixedGeneratedProtocol.authorizedView :=
  { parentTrace := secondParentTrace.causal
    learnedTrace := secondLearnedTrace.causal
    predictionChanges := by
      intro equality
      nomatch equality
    proposalChanges := restoredPriorCapacity_changesSecondProposal }

inductive ProgramRejectReason : Type
  | insufficientCapacity

inductive ProgramRejected :
    ProgramCorpus → Option CertifiedProgramAbstraction → ProgramRejectReason → Type
  | secondParent :
      ProgramRejected firstSuccessorCorpus none .insufficientCapacity

def programSuccessor
    (corpus : ProgramCorpus)
    (proposal : Option CertifiedProgramAbstraction) : ProgramCorpus :=
  match proposal with
  | none => corpus
  | some proposed => corpus.incorporate proposed

inductive ProgramSucceeds :
    ProgramCorpus → Option CertifiedProgramAbstraction → ProgramCorpus → Type
  | secondLearned :
      ProgramSucceeds firstSuccessorCorpus
        (programCore.run (programCore.learn firstStage.capacity)
          (viewFor firstStage.corpus)).causal.proposal secondSuccessorCorpus

def programSuccession : TransformerSuccession programCore where
  RejectReason := ProgramRejectReason
  Rejected := ProgramRejected
  successor := programSuccessor
  Succeeds := ProgramSucceeds

def strictGeneratedCausality : StrictFreshProbeCausality
    trainingProcedure fixedGeneratedProtocol programSuccession
    firstStage.capacity :=
  { learning := .nonempty doubleNegateAbstraction.formation []
      firstStage.capacity
    intervention := secondIntervention
    parentRejectReason := .insufficientCapacity
    parentRejected := .secondParent
    learnedSucceeds := .secondLearned }

theorem secondProposal_usesAcquiredCapacity :
    strictGeneratedCausality.intervention.learnedTrace.proposal =
      secondLearnedTrace.causal.proposal :=
  rfl

/-! ## Address-renaming separator -/

def renamedFirstSuccessorCorpus : ProgramCorpus :=
  firstSuccessorCorpus.renameAddresses (fun address => address + 10)

theorem renaming_preservesNextFrontier :
    frontierFormation? renamedFirstSuccessorCorpus =
      frontierFormation? firstSuccessorCorpus :=
  rfl

/-! ## Exact typed executable boundary -/

structure TypedExecutableTrace where
  sourceFormations : List Formation
  incomingCapacity : Nat
  acquiredCapacity : Nat
  predicted : Option Formation
  consumed : Option Formation
  proposal : Option Formation
  proposedInterface : Option (ProgramType × ProgramType)
  certifiedFormation : Option Formation
  targetFormations : Option (List Formation)
  regimeAdmitted : Bool
  normSatisfied : Bool
  certificateIssued : Bool
  governedEffect : Bool

def typedCanonicalTrace (stage : TypedStage) : TypedExecutableTrace :=
  let acquired := programCore.learn stage.capacity
  let formal := programCore.run acquired (viewFor stage.corpus)
  let target := typedStep stage
  { sourceFormations := stage.corpus.formations
    incomingCapacity := stage.capacity
    acquiredCapacity := acquired
    predicted := formal.causal.predicted.map
      CertifiedProgramAbstraction.formation
    consumed := formal.causal.consumedPrediction.map
      CertifiedProgramAbstraction.formation
    proposal := formal.causal.proposal.map
      CertifiedProgramAbstraction.formation
    proposedInterface := formal.causal.proposal.map
      (fun abstraction => (abstraction.source, abstraction.target))
    certifiedFormation := formal.causal.proposal.map
      CertifiedProgramAbstraction.formation
    targetFormations := target.map (fun next => next.corpus.formations)
    regimeAdmitted := target.isSome
    normSatisfied := target.isSome
    certificateIssued := target.isSome
    governedEffect := target.isSome }

structure TypedTraceRefinement
    (stage : TypedStage)
    (trace : TypedExecutableTrace) : Prop where
  exact : trace = typedCanonicalTrace stage

theorem typedCanonicalRefinement (stage : TypedStage) :
    TypedTraceRefinement stage (typedCanonicalTrace stage) :=
  ⟨rfl⟩

theorem TypedTraceRefinement.predictionConsumedExactly
    {stage : TypedStage}
    {trace : TypedExecutableTrace}
    (refinement : TypedTraceRefinement stage trace) :
    trace.consumed = trace.predicted := by
  rw [refinement.exact]
  exact congrArg (Option.map CertifiedProgramAbstraction.formation)
    ((programCore.run (programCore.learn stage.capacity)
      (viewFor stage.corpus)).causal.consumedExact)

theorem TypedTraceRefinement.effectRequiresCertificate
    {stage : TypedStage}
    {trace : TypedExecutableTrace}
    (refinement : TypedTraceRefinement stage trace) :
    trace.governedEffect = trace.certificateIssued := by
  rw [refinement.exact]
  rfl

theorem TypedTraceRefinement.regimeAgreesWithNorm
    {stage : TypedStage}
    {trace : TypedExecutableTrace}
    (refinement : TypedTraceRefinement stage trace) :
    trace.regimeAdmitted = trace.normSatisfied := by
  rw [refinement.exact]
  rfl

def forgedEffectWithoutCertificate : TypedExecutableTrace :=
  { typedCanonicalTrace firstStage with
    certificateIssued := false
    governedEffect := true }

theorem forgedEffectWithoutCertificate_hasNoRefinement :
    TypedTraceRefinement firstStage forgedEffectWithoutCertificate → False := by
  intro refinement
  have certificateEquality :=
    congrArg TypedExecutableTrace.certificateIssued refinement.exact
  nomatch certificateEquality

def rewrittenSecondTrace : TypedExecutableTrace :=
  { typedCanonicalTrace firstStage with
    proposal := some (.identity .bit) }

theorem rewrittenSecondTrace_hasNoRefinement :
    TypedTraceRefinement firstStage rewrittenSecondTrace → False := by
  intro refinement
  have proposalEquality :=
    congrArg TypedExecutableTrace.proposal refinement.exact
  nomatch proposalEquality

def missingFirstCorpusTrace : TypedExecutableTrace :=
  { typedCanonicalTrace firstStage with
    targetFormations := some initialCorpus.formations }

theorem missingFirstCorpusTrace_hasNoRefinement :
    TypedTraceRefinement firstStage missingFirstCorpusTrace → False := by
  intro refinement
  have targetEquality :=
    congrArg TypedExecutableTrace.targetFormations refinement.exact
  nomatch targetEquality

structure CompactTypedSelfExtension where
  firstTransition : TypedStep initialStage firstStage
  secondTransition : TypedStep firstStage secondStage
  formedHistory : StrongPerimetralTurning.History
    TypedStep initialStage secondStage
  frontierChanged :
    frontierFormation? withoutFirstIncorporation.corpus =
      frontierFormation? firstStage.corpus → False
  frontierSemanticsChanged :
    doubleNegateAbstraction.evaluate false =
      tripleNegateAbstraction.evaluate false → False
  learningChangedSecondProposal :
    secondParentTrace.causal.proposal =
      secondLearnedTrace.causal.proposal → False
  generatedProbe : GeneratedFreshProbeProtocol
  generatedProbeExact : generatedProbe.fixed.probe =
    generateProbe generatedProbe.sealed generatedProbe.seed
  strictCausality : StrictFreshProbeCausality
    trainingProcedure fixedGeneratedProtocol programSuccession
      firstStage.capacity
  renamingInvariant :
    frontierFormation? renamedFirstSuccessorCorpus =
      frontierFormation? firstSuccessorCorpus
  firstRefines : TypedTraceRefinement initialStage
    (typedCanonicalTrace initialStage)
  secondRefines : TypedTraceRefinement firstStage
    (typedCanonicalTrace firstStage)
  rewrittenRejected :
    TypedTraceRefinement firstStage rewrittenSecondTrace → False
  missingCorpusRejected :
    TypedTraceRefinement firstStage missingFirstCorpusTrace → False
  forgedEffectRejected :
    TypedTraceRefinement firstStage forgedEffectWithoutCertificate → False

def compactTypedSelfExtension : CompactTypedSelfExtension :=
  { firstTransition := firstStep_reconstructsCorpus
    secondTransition := secondStep_consumesFirstSuccessor
    formedHistory := secondHistory
    frontierChanged := firstIncorporation_changesSecondObligation
    frontierSemanticsChanged := firstIncorporation_changesFrontierSemantics
    learningChangedSecondProposal := restoredPriorCapacity_changesSecondProposal
    generatedProbe := generatedProtocol
    generatedProbeExact := generatedProbe_isBoundToSealedDescriptor
    strictCausality := strictGeneratedCausality
    renamingInvariant := renaming_preservesNextFrontier
    firstRefines := typedCanonicalRefinement initialStage
    secondRefines := typedCanonicalRefinement firstStage
    rewrittenRejected := rewrittenSecondTrace_hasNoRefinement
    missingCorpusRejected := missingFirstCorpusTrace_hasNoRefinement
    forgedEffectRejected := forgedEffectWithoutCertificate_hasNoRefinement }

end EndogenousTypedSuccession
end ConstitutiveAlignment

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveAlignment.EndogenousTypedSuccession.frontierFormation?
#print axioms ConstitutiveAlignment.EndogenousTypedSuccession.programCore
#print axioms ConstitutiveAlignment.EndogenousTypedSuccession.typedStep
#print axioms ConstitutiveAlignment.EndogenousTypedSuccession.firstStep_reconstructsCorpus
#print axioms ConstitutiveAlignment.EndogenousTypedSuccession.secondStep_consumesFirstSuccessor
#print axioms ConstitutiveAlignment.EndogenousTypedSuccession.firstIncorporation_changesSecondObligation
#print axioms ConstitutiveAlignment.EndogenousTypedSuccession.firstIncorporation_changesFrontierSemantics
#print axioms ConstitutiveAlignment.EndogenousTypedSuccession.restoredPriorCapacity_changesSecondProposal
#print axioms ConstitutiveAlignment.EndogenousTypedSuccession.generatedSecondProbe_isFresh
#print axioms ConstitutiveAlignment.EndogenousTypedSuccession.generatedSecondProbe_absentFromPriorLedger
#print axioms ConstitutiveAlignment.EndogenousTypedSuccession.generatedProbe_isBoundToSealedDescriptor
#print axioms ConstitutiveAlignment.EndogenousTypedSuccession.acquiredCapacity_isSecondLearnedCapacity
#print axioms ConstitutiveAlignment.EndogenousTypedSuccession.strictGeneratedCausality
#print axioms ConstitutiveAlignment.EndogenousTypedSuccession.renaming_preservesNextFrontier
#print axioms ConstitutiveAlignment.EndogenousTypedSuccession.TypedTraceRefinement.predictionConsumedExactly
#print axioms ConstitutiveAlignment.EndogenousTypedSuccession.TypedTraceRefinement.effectRequiresCertificate
#print axioms ConstitutiveAlignment.EndogenousTypedSuccession.TypedTraceRefinement.regimeAgreesWithNorm
#print axioms ConstitutiveAlignment.EndogenousTypedSuccession.forgedEffectWithoutCertificate_hasNoRefinement
#print axioms ConstitutiveAlignment.EndogenousTypedSuccession.rewrittenSecondTrace_hasNoRefinement
#print axioms ConstitutiveAlignment.EndogenousTypedSuccession.missingFirstCorpusTrace_hasNoRefinement
#print axioms ConstitutiveAlignment.EndogenousTypedSuccession.compactTypedSelfExtension
/- AXIOM_AUDIT_END -/
