import ConstitutiveAlignment.Machine

set_option linter.checkUnivs false

/-!
# Constitutive transport into an external verifier

This module separates a source-to-presentation formation chain from the
terminal acceptance relation of a verifier.  It also isolates the two minimal
obligations needed to transport a negative guarantee such as `no False`:
coverage of every relevant source occurrence and preservation of
counterexamples.

The ConLeche projection case below is a local record-level model of the
documented frontend rewrite: the declaration header is retained while a
primitive-projection body is replaced by a recursor-projection body.  It is not
an import of ConLeche and makes no theorem about that external implementation.
-/

namespace ConstitutiveAlignment

universe uSource uExported uParsed uPresented
universe uExportFaithful uParseFaithful uPrepareFaithful uAccepted

/-! ## A typed formation chain -/

structure VerificationPipeline where
  Source : Type uSource
  Exported : Type uExported
  Parsed : Type uParsed
  Presented : Type uPresented
  exportStep : Source → Exported
  parseStep : Exported → Parsed
  prepareStep : Parsed → Presented

namespace VerificationPipeline

def run (pipeline : VerificationPipeline) :
    pipeline.Source → pipeline.Presented :=
  fun source => pipeline.prepareStep
    (pipeline.parseStep (pipeline.exportStep source))

def exported
    (pipeline : VerificationPipeline)
    (source : pipeline.Source) : pipeline.Exported :=
  pipeline.exportStep source

def parsed
    (pipeline : VerificationPipeline)
    (source : pipeline.Source) : pipeline.Parsed :=
  pipeline.parseStep (pipeline.exportStep source)

end VerificationPipeline

/- Fidelity is a separate specification.  Merely defining the three executable
   maps therefore creates no fidelity witness. -/
structure VerificationFidelity
    (pipeline : VerificationPipeline) where
  FaithfulExport : pipeline.Source → pipeline.Exported → Type uExportFaithful
  FaithfulParse : pipeline.Exported → pipeline.Parsed → Type uParseFaithful
  FaithfulPrepare : pipeline.Parsed → pipeline.Presented → Type uPrepareFaithful

def FaithfulComp
    {First : Type _}
    {Middle : Type _}
    {Last : Type _}
    (first : First → Middle → Type _)
    (second : Middle → Last → Type _)
    (source : First)
    (target : Last) : Type _ :=
  Sigma fun middle : Middle => first source middle × second middle target

/- A faithful run retains witnesses at every computed intermediate occurrence.
   The intermediates can be recovered definitionally from `source`. -/
structure FaithfulRun
    (pipeline : VerificationPipeline)
    (fidelity : VerificationFidelity pipeline)
    (source : pipeline.Source) where
  exportWitness : fidelity.FaithfulExport source (pipeline.exportStep source)
  parseWitness : fidelity.FaithfulParse
    (pipeline.exportStep source)
    (pipeline.parseStep (pipeline.exportStep source))
  prepareWitness : fidelity.FaithfulPrepare
    (pipeline.parseStep (pipeline.exportStep source))
    (pipeline.run source)

namespace FaithfulRun

def sourceToPresented
    {pipeline : VerificationPipeline}
    {fidelity : VerificationFidelity pipeline}
    {source : pipeline.Source}
    (run : FaithfulRun pipeline fidelity source) :
    FaithfulComp fidelity.FaithfulExport
      (FaithfulComp fidelity.FaithfulParse fidelity.FaithfulPrepare)
      source (pipeline.run source) :=
  ⟨pipeline.exportStep source, run.exportWitness,
    ⟨pipeline.parseStep (pipeline.exportStep source),
      run.parseWitness, run.prepareWitness⟩⟩

end FaithfulRun

/- Acceptance does not generate fidelity: both witnesses must be supplied. -/
structure ConstitutivelyAccepted
    (pipeline : VerificationPipeline)
    (fidelity : VerificationFidelity pipeline)
    (Accepted : pipeline.Presented → Type uAccepted)
    (source : pipeline.Source) where
  faithful : FaithfulRun pipeline fidelity source
  accepted : Accepted (pipeline.run source)

/-! ## Transport of negative guarantees -/

universe uSourceOccurrence uPresentedOccurrence
universe uSourceCounterexample uPresentedCounterexample

def NoCounterexample
    {Occurrence : Type _}
    (Counterexample : Occurrence → Type _) : Prop :=
  (occurrence : Occurrence) → Counterexample occurrence → False

/- Coverage is deliberately separate from preservation.  A total map witnesses
   that no relevant source occurrence is silently omitted. -/
structure SourceCoverage
    (SourceOccurrence : Type uSourceOccurrence)
    (PresentedOccurrence : Type uPresentedOccurrence) where
  present : SourceOccurrence → PresentedOccurrence

structure PreservesCounterexample
    {SourceOccurrence : Type uSourceOccurrence}
    {PresentedOccurrence : Type uPresentedOccurrence}
    (coverage : SourceCoverage SourceOccurrence PresentedOccurrence)
    (SourceCounterexample : SourceOccurrence → Type uSourceCounterexample)
    (PresentedCounterexample :
      PresentedOccurrence → Type uPresentedCounterexample) where
  preserve : {source : SourceOccurrence} →
    SourceCounterexample source →
      PresentedCounterexample (coverage.present source)

theorem transportNoCounterexample
    {SourceOccurrence : Type uSourceOccurrence}
    {PresentedOccurrence : Type uPresentedOccurrence}
    {SourceCounterexample : SourceOccurrence → Type uSourceCounterexample}
    {PresentedCounterexample :
      PresentedOccurrence → Type uPresentedCounterexample}
    (coverage : SourceCoverage SourceOccurrence PresentedOccurrence)
    (preserves : PreservesCounterexample coverage
      SourceCounterexample PresentedCounterexample)
    (nonePresented : NoCounterexample PresentedCounterexample) :
    NoCounterexample SourceCounterexample :=
  fun source counterexample =>
    nonePresented (coverage.present source) (preserves.preserve counterexample)

/-! ## Internal alignment of a semantic checker -/

universe uInput uEnvironment uFailure uSemantic uCertificate

/- This is the exact abstract shape of the ConLeche result: an operational
   computation returns an environment, while an independently stated semantic
   family classifies that environment. -/
structure SemanticChecker (Input : Type uInput) where
  Environment : Type uEnvironment
  Failure : Type uFailure
  check : Input → Except Failure Environment
  SemanticSafe : Environment → Type uSemantic

namespace SemanticChecker

abbrev Candidate
    {Input : Type uInput}
    (checker : SemanticChecker Input) : Type _ :=
  Input × checker.Environment

def Regime
    {Input : Type uInput}
    (checker : SemanticChecker Input)
    (candidate : checker.Candidate) : Type :=
  PLift (checker.check candidate.1 = .ok candidate.2)

def Norm
    {Input : Type uInput}
    (checker : SemanticChecker Input)
    (candidate : checker.Candidate) : Type _ :=
  checker.SemanticSafe candidate.2

abbrev Soundness
    {Input : Type uInput}
    (checker : SemanticChecker Input) : Type _ :=
  (candidate : checker.Candidate) →
    checker.Regime candidate → checker.Norm candidate

abbrev Completeness
    {Input : Type uInput}
    (checker : SemanticChecker Input) : Type _ :=
  (candidate : checker.Candidate) →
    checker.Norm candidate → checker.Regime candidate

structure Adequacy
    {Input : Type uInput}
    (checker : SemanticChecker Input) where
  sound : checker.Soundness
  complete : checker.Completeness

/- A factorization exposes the intermediate certificate used by a soundness
   proof instead of hiding the constitution of `Regime → Norm`.  In the
   inspected ConLeche proof, acceptance first yields a `FullyChecked` object,
   then a nonempty `EnvModelM`; that model excludes a `False`-typed constant. -/
structure SoundnessFactorization
    {Input : Type uInput}
    (checker : SemanticChecker Input) where
  Certificate : checker.Candidate → Type uCertificate
  certify : (candidate : checker.Candidate) →
    checker.Regime candidate → Certificate candidate
  interpret : (candidate : checker.Candidate) →
    Certificate candidate → checker.Norm candidate

def SoundnessFactorization.sound
    {Input : Type uInput}
    {checker : SemanticChecker Input}
    (factorization : SoundnessFactorization checker) : checker.Soundness :=
  fun candidate accepted =>
    factorization.interpret candidate
      (factorization.certify candidate accepted)

end SemanticChecker

/- The full source-to-semantics certificate keeps provenance and operational
   acceptance distinct.  Semantic safety is derived only through soundness. -/
structure ConstitutivelySoundRun
    (pipeline : VerificationPipeline)
    (fidelity : VerificationFidelity pipeline)
    (checker : SemanticChecker pipeline.Presented)
    (source : pipeline.Source) where
  faithful : FaithfulRun pipeline fidelity source
  environment : checker.Environment
  accepted : checker.Regime (pipeline.run source, environment)

def ConstitutivelySoundRun.semantic
    {pipeline : VerificationPipeline}
    {fidelity : VerificationFidelity pipeline}
    {checker : SemanticChecker pipeline.Presented}
    {source : pipeline.Source}
    (run : ConstitutivelySoundRun pipeline fidelity checker source)
    (sound : checker.Soundness) : checker.SemanticSafe run.environment :=
  sound (pipeline.run source, run.environment) run.accepted

/-! ## Consumed slice of the `no False` capstone -/

universe uDeclaration uReading uValue uMembership uFalseTyped

/- This interface is the local dependency slice read from the terminal
   ConLeche argument.  `type_reads` and the constant-reading equations supply
   `typeReading`; `mem_type` supplies `inhabitsStoredType`; the pinned `False`
   leaf supplies `falseTypeReadsEmpty`; and `not_mem_empty` supplies the final
   eliminator.  No other field of `EnvModelM` occurs in this capstone. -/
structure NoFalseSemanticSlice where
  Declaration : Type uDeclaration
  Reading : Type uReading
  Value : Type uValue
  Membership : Value → Value → Type uMembership
  FalseTyped : Declaration → Type uFalseTyped
  typeReading : Declaration → Reading
  valueOf : Declaration → Value
  interpret : Reading → Value
  empty : Value
  inhabitsStoredType : (declaration : Declaration) →
    Membership (valueOf declaration) (interpret (typeReading declaration))
  falseTypeReadsEmpty : {declaration : Declaration} →
    FalseTyped declaration →
      PLift (interpret (typeReading declaration) = empty)
  emptyHasNoMembers : (value : Value) → Membership value empty → False

theorem NoFalseSemanticSlice.excludesFalse
    (slice : NoFalseSemanticSlice) :
    NoCounterexample slice.FalseTyped := by
  intro declaration falseTyped
  have inhabits := slice.inhabitsStoredType declaration
  rw [(slice.falseTypeReadsEmpty falseTyped).down] at inhabits
  exact slice.emptyHasNoMembers (slice.valueOf declaration) inhabits

/- ConLeche derives its empty set from regularity applied to an inhabited
   transitive universe and then selects the witness classically.  The
   constitutive content can instead retain the witness positively. -/
universe uFoundation uFoundationMembership

structure ConstructiveEmptyFoundation where
  Value : Type uFoundation
  Membership : Value → Value → Type uFoundationMembership
  innerUniverse : Value
  outerUniverse : Value
  innerInOuter : Membership innerUniverse outerUniverse
  outerTransitive : {middle member : Value} →
    Membership middle outerUniverse →
      Membership member middle → Membership member outerUniverse
  minimalMember :
    (container : Value) →
    (Sigma fun witness : Value => Membership witness container) →
      Sigma fun minimal : Value =>
        Membership minimal container ×
          PLift ((candidate : Value) →
            Membership candidate minimal →
            Membership candidate container → False)

def ConstructiveEmptyFoundation.derivedEmpty
    (foundation : ConstructiveEmptyFoundation) :
    Sigma fun empty : foundation.Value =>
      PLift ((value : foundation.Value) →
        foundation.Membership value empty → False) := by
  obtain ⟨empty, emptyInOuter, minimal⟩ :=
    foundation.minimalMember foundation.outerUniverse
      ⟨foundation.innerUniverse, foundation.innerInOuter⟩
  exact ⟨empty, ⟨fun value valueInEmpty =>
    minimal.down value valueInEmpty
      (foundation.outerTransitive emptyInOuter valueInEmpty)⟩⟩

/-! ## Witnessed transport and propositional shadows

This kernel separates three claims that must not be conflated:

* a witness at one state is sufficient for a terminal proposition;
* after an admissible step, some successor witness exists;
* a determined successor witness is historically compatible with the old one.

Only the first claim descends automatically through `Nonempty`.  Historical
compatibility remains a relation between concrete witnesses.  No converse from
weak stability to historical stability, no canonical closure, and no
minimality claim is introduced here. -/

universe uState uStep uCarrier uObligation

structure WitnessCandidate
    (State : Type uState)
    (initial : State)
    (Terminal : State → Prop) where
  Carrier : State → Type uCarrier
  initialWitness : Carrier initial
  extract : {state : State} → Carrier state → Terminal state

def ShadowCarrier
    {State : Type uState}
    {initial : State}
    {Terminal : State → Prop}
    (candidate : WitnessCandidate State initial Terminal)
    (state : State) : Prop :=
  Nonempty (candidate.Carrier state)

def WeaklyStable
    {State : Type uState}
    {initial : State}
    {Terminal : State → Prop}
    (candidate : WitnessCandidate State initial Terminal)
    (Step : State → State → Type uStep) : Prop :=
  ∀ {before after : State},
    ShadowCarrier candidate before →
      Step before after → ShadowCarrier candidate after

def HistoricalStable
    {State : Type uState}
    {initial : State}
    {Terminal : State → Prop}
    (candidate : WitnessCandidate State initial Terminal)
    (Step : State → State → Type uStep)
    (Compatible : (before after : State) →
      Step before after →
      candidate.Carrier before →
      candidate.Carrier after → Prop) : Type _ :=
  (before after : State) →
    (step : Step before after) →
    (old : candidate.Carrier before) →
      {new : candidate.Carrier after //
        Compatible before after step old new}

def TransitionObligation
    {State : Type uState}
    {initial : State}
    {Terminal : State → Prop}
    (candidate : WitnessCandidate State initial Terminal)
    (Step : State → State → Type uStep) : Type _ :=
  (before after : State) →
    Step before after →
    candidate.Carrier before → Type uObligation

def LocallyReconstructs
    {State : Type uState}
    {initial : State}
    {Terminal : State → Prop}
    (candidate : WitnessCandidate State initial Terminal)
    (Step : State → State → Type uStep)
    (obligation : TransitionObligation candidate Step) : Type _ :=
  (before after : State) →
    (step : Step before after) →
    (old : candidate.Carrier before) →
      obligation before after step old

structure Separator
    {State : Type uState}
    {initial : State}
    {Terminal : State → Prop}
    (candidate : WitnessCandidate State initial Terminal)
    (Step : State → State → Type uStep)
    (obligation : TransitionObligation candidate Step) where
  before : State
  after : State
  carrier : candidate.Carrier before
  step : Step before after
  refute : obligation before after step carrier → False

theorem shadowExtract
    {State : Type uState}
    {initial : State}
    {Terminal : State → Prop}
    (candidate : WitnessCandidate State initial Terminal)
    {state : State}
    (shadow : ShadowCarrier candidate state) :
    Terminal state := by
  exact Nonempty.elim shadow (fun witness => candidate.extract witness)

theorem historicalStable_implies_weaklyStable
    {State : Type uState}
    {initial : State}
    {Terminal : State → Prop}
    (candidate : WitnessCandidate State initial Terminal)
    (Step : State → State → Type uStep)
    (Compatible : (before after : State) →
      Step before after →
      candidate.Carrier before →
      candidate.Carrier after → Prop)
    (historical : HistoricalStable candidate Step Compatible) :
    WeaklyStable candidate Step := by
  intro before after oldShadow step
  exact Nonempty.elim oldShadow (fun old =>
    let successor := historical before after step old
    ⟨successor.1⟩)

theorem separator_refutes_localReconstruction
    {State : Type uState}
    {initial : State}
    {Terminal : State → Prop}
    (candidate : WitnessCandidate State initial Terminal)
    (Step : State → State → Type uStep)
    (obligation : TransitionObligation candidate Step)
    (separator : Separator candidate Step obligation) :
    LocallyReconstructs candidate Step obligation → False := by
  intro reconstructs
  exact separator.refute
    (reconstructs separator.before separator.after separator.step
      separator.carrier)

theorem separator_refutes_historicalStability
    {State : Type uState}
    {initial : State}
    {Terminal : State → Prop}
    (candidate : WitnessCandidate State initial Terminal)
    (Step : State → State → Type uStep)
    (obligation : TransitionObligation candidate Step)
    (Compatible : (before after : State) →
      Step before after →
      candidate.Carrier before →
      candidate.Carrier after → Prop)
    (separator : Separator candidate Step obligation)
    (compatibleProvides :
      (before after : State) →
      (step : Step before after) →
      (old : candidate.Carrier before) →
      (new : candidate.Carrier after) →
        Compatible before after step old new →
          obligation before after step old) :
    HistoricalStable candidate Step Compatible → False := by
  intro historical
  obtain ⟨new, compatible⟩ :=
    historical separator.before separator.after separator.step
      separator.carrier
  exact separator.refute
    (compatibleProvides separator.before separator.after separator.step
      separator.carrier new compatible)

/-! ## Constructive separators -/

namespace VerificationSeparators

open StrongPerimetralTurning

abbrev SourceRole : Type :=
  History.Occurrence Separators.twoStepHistory

def collapsedPipeline : VerificationPipeline where
  Source := SourceRole
  Exported := Unit
  Parsed := Unit
  Presented := Unit
  exportStep := fun _source => ()
  parseStep := fun _exported => ()
  prepareStep := fun _parsed => ()

def AcceptedPresentation (_presented : Unit) : Type := Unit

def acceptedPresentation
    (source : collapsedPipeline.Source) :
    AcceptedPresentation (collapsedPipeline.run source) :=
  ()

/- This is a specialized global fidelity obligation for preservation of
   occurrence identity at the first transformation. -/
structure FaithfulOccurrenceExport
    (pipeline : VerificationPipeline) where
  realization : InjectiveMap pipeline.Source pipeline.Exported
  realizesExport : realization.toFun = pipeline.exportStep

theorem collapsedPipeline_hasNoFaithfulOccurrenceExport :
    FaithfulOccurrenceExport collapsedPipeline → False := by
  intro faithful
  exact Separators.noFaithfulTerminalOnlyRealization faithful.realization

theorem acceptedPresentation_doesNotDetermineOrigin
    (source : collapsedPipeline.Source) :
    AcceptedPresentation (collapsedPipeline.run source) →
      FaithfulOccurrenceExport collapsedPipeline → False :=
  fun _accepted faithful => collapsedPipeline_hasNoFaithfulOccurrenceExport faithful

/- Coverage cannot be omitted: an inhabited source cannot be covered by an
   empty presented carrier. -/
def UnitCounterexample (_source : Unit) : Type := Unit

def EmptyCounterexample
    (_presented : Separators.EmptyWitness) : Type :=
  Separators.EmptyWitness

theorem noEmptyCounterexample : NoCounterexample EmptyCounterexample :=
  fun presented => nomatch presented

theorem coverage_isNecessary :
    SourceCoverage Unit Separators.EmptyWitness → False :=
  fun coverage => nomatch coverage.present ()

/- Preservation cannot be omitted even when coverage exists. -/
def unitCoverage : SourceCoverage Unit Unit :=
  { present := fun source => source }

def NoUnitCounterexample (_presented : Unit) : Type :=
  Separators.EmptyWitness

theorem noUnitCounterexample : NoCounterexample NoUnitCounterexample :=
  fun _presented counterexample => nomatch counterexample

theorem counterexamplePreservation_isNecessary :
    PreservesCounterexample unitCoverage
      UnitCounterexample NoUnitCounterexample → False :=
  fun preserves => nomatch preserves.preserve (source := ()) ()

/- The terminal no-False argument consumes three independent relations after
   the type reading has been obtained: inhabitation, the False-to-empty
   reading, and emptiness. -/
namespace NoFalseSlice

def absentMembership (_value _container : Unit) : Type :=
  Separators.EmptyWitness

def unitFalseTyped (_declaration : Unit) : Type := Unit

def unitFalseReadsEmpty :
    {declaration : Unit} → unitFalseTyped declaration →
      PLift ((() : Unit) = ()) :=
  fun _falseTyped => ⟨rfl⟩

theorem absentMembership_empty :
    (value : Unit) → absentMembership value () → False :=
  fun _value membership => nomatch membership

theorem inhabitation_isNecessary :
    ((declaration : Unit) → absentMembership () ()) → False :=
  fun inhabits => nomatch inhabits ()

inductive TwoValues : Type
  | inhabited
  | empty

def selectiveMembership (_value : TwoValues) : TwoValues → Type
  | .inhabited => Unit
  | .empty => Separators.EmptyWitness

def storedValueInhabitsReading :
    selectiveMembership .inhabited .inhabited :=
  ()

theorem selectiveEmptyHasNoMembers :
    (value : TwoValues) → selectiveMembership value .empty → False :=
  fun _value membership => nomatch membership

theorem falseTypeReading_isNecessary :
    PLift (TwoValues.inhabited = TwoValues.empty) → False :=
  fun reading => nomatch reading.down

def indiscriminateMembership (_value _container : Unit) : Type := Unit

def indiscriminateInhabitation :
    indiscriminateMembership () () :=
  ()

theorem emptyExclusion_isNecessary :
    ((value : Unit) → indiscriminateMembership value () → False) → False :=
  fun emptyExclusion => emptyExclusion () ()

theorem totalMembership_hasNoEmptyWitness :
    (Sigma fun empty : Unit =>
      PLift ((value : Unit) →
        indiscriminateMembership value empty → False)) → False :=
  fun emptyWitness => emptyWitness.2.down () ()

end NoFalseSlice

/- The three arrows of the ConLeche case study are independent. -/
namespace InternalAlignment

def unsoundChecker : SemanticChecker Unit where
  Environment := Unit
  Failure := Unit
  check := fun _input => .ok ()
  SemanticSafe := fun _environment => Separators.EmptyWitness

def unsoundAccepted :
    unsoundChecker.Regime ((), ()) :=
  ⟨rfl⟩

theorem acceptance_withoutSoundness_hasNoSemantics :
    unsoundChecker.Norm ((), ()) → False :=
  fun semantic => nomatch semantic

theorem unsoundChecker_hasNoSoundness :
    unsoundChecker.Soundness → False :=
  fun sound => acceptance_withoutSoundness_hasNoSemantics
    (sound ((), ()) unsoundAccepted)

inductive SelectiveInput : Type
  | admitted
  | omitted

def selectiveChecker : SemanticChecker SelectiveInput where
  Environment := Unit
  Failure := Unit
  check
    | .admitted => .ok ()
    | .omitted => .error ()
  SemanticSafe := fun _environment => Unit

def selectiveSoundness : selectiveChecker.Soundness := by
  intro candidate _accepted
  exact ()

theorem selectiveChecker_hasNoCompleteness :
    selectiveChecker.Completeness → False := by
  intro complete
  have accepted := complete (.omitted, ()) ()
  nomatch accepted.down

def acceptingChecker : SemanticChecker Unit where
  Environment := Unit
  Failure := Unit
  check := fun _input => .ok ()
  SemanticSafe := fun _environment => Unit

def acceptingSoundness : acceptingChecker.Soundness :=
  fun _candidate _accepted => ()

def collapsedAccepted
    (source : collapsedPipeline.Source) :
    acceptingChecker.Regime (collapsedPipeline.run source, ()) :=
  ⟨rfl⟩

def collapsedSemantic
    (source : collapsedPipeline.Source) :
    acceptingChecker.Norm (collapsedPipeline.run source, ()) :=
  acceptingSoundness _ (collapsedAccepted source)

theorem soundAcceptanceAndSemantics_doNotDetermineOrigin
    (source : collapsedPipeline.Source) :
    acceptingChecker.Soundness →
      acceptingChecker.Regime (collapsedPipeline.run source, ()) →
      acceptingChecker.Norm (collapsedPipeline.run source, ()) →
      FaithfulOccurrenceExport collapsedPipeline → False :=
  fun _sound _accepted _semantic faithful =>
    collapsedPipeline_hasNoFaithfulOccurrenceExport faithful

end InternalAlignment

end VerificationSeparators

/-! ## Local model of the ConLeche projection rewrite -/

namespace ConLecheProjectionCase

inductive DeclaredType : Type
  | falseType
  | other (code : Nat)
  deriving DecidableEq

inductive DeclarationBody : Type
  | primitiveProjection (owner field subject : Nat)
  | recursorProjection (owner field subject : Nat)
  | other (code : Nat)
  deriving DecidableEq

structure LocatedDeclaration where
  name : Nat
  position : Nat
  sourcePrefix : List Nat
  declaredType : DeclaredType
  body : DeclarationBody
  deriving DecidableEq

def rewriteBody : DeclarationBody → DeclarationBody
  | .primitiveProjection owner field subject =>
      .recursorProjection owner field subject
  | .recursorProjection owner field subject =>
      .recursorProjection owner field subject
  | .other code => .other code

def rewriteProjection (source : LocatedDeclaration) : LocatedDeclaration :=
  { name := source.name
    position := source.position
    sourcePrefix := source.sourcePrefix
    declaredType := source.declaredType
    body := rewriteBody source.body }

/- The rich witness describes the record-level preservation visible in the
   documented rewrite: only the body is replaced. -/
structure ProjectionRewriteWitness
    (source target : LocatedDeclaration) where
  nameExact : PLift (target.name = source.name)
  positionExact : PLift (target.position = source.position)
  prefixExact : PLift (target.sourcePrefix = source.sourcePrefix)
  declaredTypeExact : PLift (target.declaredType = source.declaredType)
  bodyExact : PLift (target.body = rewriteBody source.body)

def projectionRewriteWitness (source : LocatedDeclaration) :
    ProjectionRewriteWitness source (rewriteProjection source) where
  nameExact := ⟨rfl⟩
  positionExact := ⟨rfl⟩
  prefixExact := ⟨rfl⟩
  declaredTypeExact := ⟨rfl⟩
  bodyExact := ⟨rfl⟩

def HasFalseType (declaration : LocatedDeclaration) : Type :=
  PLift (declaration.declaredType = .falseType)

def ProjectionRewriteWitness.preservesFalse
    {source target : LocatedDeclaration}
    (witness : ProjectionRewriteWitness source target)
    (sourceFalse : HasFalseType source) : HasFalseType target := by
  rcases sourceFalse with ⟨sourceFalse⟩
  exact ⟨witness.declaredTypeExact.down.trans sourceFalse⟩

def projectionCoverage :
    SourceCoverage LocatedDeclaration LocatedDeclaration :=
  { present := rewriteProjection }

def projectionPreservesFalse :
    PreservesCounterexample projectionCoverage HasFalseType HasFalseType :=
  { preserve := fun {source} sourceFalse =>
      (projectionRewriteWitness source).preservesFalse sourceFalse }

theorem projectionNoFalseTransport
    (nonePresented : NoCounterexample HasFalseType) :
    NoCounterexample HasFalseType :=
  transportNoCounterexample projectionCoverage
    projectionPreservesFalse nonePresented

/- For the abstract `no False` transport, name, position, prefix and body can be
   forgotten together.  Only the declared-type counterexample is retained. -/
def eraseNonTypeMetadata
    (source : LocatedDeclaration) : LocatedDeclaration :=
  { name := 0
    position := 0
    sourcePrefix := []
    declaredType := source.declaredType
    body := .other 0 }

def metadataErasureCoverage :
    SourceCoverage LocatedDeclaration LocatedDeclaration :=
  { present := eraseNonTypeMetadata }

def metadataErasurePreservesFalse :
    PreservesCounterexample metadataErasureCoverage HasFalseType HasFalseType :=
  { preserve := fun sourceFalse => sourceFalse }

theorem metadataErasureNoFalseTransport
    (nonePresented : NoCounterexample HasFalseType) :
    NoCounterexample HasFalseType :=
  transportNoCounterexample metadataErasureCoverage
    metadataErasurePreservesFalse nonePresented

def sourceFalseProjection : LocatedDeclaration :=
  { name := 7
    position := 11
    sourcePrefix := [2, 3, 5]
    declaredType := .falseType
    body := .primitiveProjection 13 0 17 }

def substitutedTypeDeclaration : LocatedDeclaration :=
  { name := (rewriteProjection sourceFalseProjection).name
    position := (rewriteProjection sourceFalseProjection).position
    sourcePrefix := (rewriteProjection sourceFalseProjection).sourcePrefix
    declaredType := .other 19
    body := (rewriteProjection sourceFalseProjection).body }

def AbstractlyAccepted (_declaration : LocatedDeclaration) : Type := Unit

def substitutedTypeAccepted :
    AbstractlyAccepted substitutedTypeDeclaration :=
  ()

theorem substitutedType_hasNoFaithfulRewrite :
    ProjectionRewriteWitness sourceFalseProjection
      substitutedTypeDeclaration → False := by
  intro witness
  nomatch witness.declaredTypeExact.down

theorem acceptedSubstitution_hasNoFaithfulRewrite :
    AbstractlyAccepted substitutedTypeDeclaration →
      ProjectionRewriteWitness sourceFalseProjection
        substitutedTypeDeclaration → False :=
  fun _accepted witness => substitutedType_hasNoFaithfulRewrite witness

end ConLecheProjectionCase

end ConstitutiveAlignment

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveAlignment.FaithfulComp
#print axioms ConstitutiveAlignment.FaithfulRun.sourceToPresented
#print axioms ConstitutiveAlignment.ConstitutivelyAccepted
#print axioms ConstitutiveAlignment.transportNoCounterexample
#print axioms ConstitutiveAlignment.SemanticChecker.SoundnessFactorization.sound
#print axioms ConstitutiveAlignment.ConstitutivelySoundRun.semantic
#print axioms ConstitutiveAlignment.NoFalseSemanticSlice.excludesFalse
#print axioms ConstitutiveAlignment.ConstructiveEmptyFoundation.derivedEmpty
#print axioms ConstitutiveAlignment.WitnessCandidate
#print axioms ConstitutiveAlignment.ShadowCarrier
#print axioms ConstitutiveAlignment.WeaklyStable
#print axioms ConstitutiveAlignment.HistoricalStable
#print axioms ConstitutiveAlignment.TransitionObligation
#print axioms ConstitutiveAlignment.LocallyReconstructs
#print axioms ConstitutiveAlignment.Separator
#print axioms ConstitutiveAlignment.shadowExtract
#print axioms ConstitutiveAlignment.historicalStable_implies_weaklyStable
#print axioms ConstitutiveAlignment.separator_refutes_localReconstruction
#print axioms ConstitutiveAlignment.separator_refutes_historicalStability
#print axioms ConstitutiveAlignment.VerificationSeparators.collapsedPipeline_hasNoFaithfulOccurrenceExport
#print axioms ConstitutiveAlignment.VerificationSeparators.acceptedPresentation_doesNotDetermineOrigin
#print axioms ConstitutiveAlignment.VerificationSeparators.coverage_isNecessary
#print axioms ConstitutiveAlignment.VerificationSeparators.counterexamplePreservation_isNecessary
#print axioms ConstitutiveAlignment.VerificationSeparators.NoFalseSlice.inhabitation_isNecessary
#print axioms ConstitutiveAlignment.VerificationSeparators.NoFalseSlice.falseTypeReading_isNecessary
#print axioms ConstitutiveAlignment.VerificationSeparators.NoFalseSlice.emptyExclusion_isNecessary
#print axioms ConstitutiveAlignment.VerificationSeparators.NoFalseSlice.totalMembership_hasNoEmptyWitness
#print axioms ConstitutiveAlignment.VerificationSeparators.InternalAlignment.unsoundChecker_hasNoSoundness
#print axioms ConstitutiveAlignment.VerificationSeparators.InternalAlignment.selectiveSoundness
#print axioms ConstitutiveAlignment.VerificationSeparators.InternalAlignment.selectiveChecker_hasNoCompleteness
#print axioms ConstitutiveAlignment.VerificationSeparators.InternalAlignment.soundAcceptanceAndSemantics_doNotDetermineOrigin
#print axioms ConstitutiveAlignment.ConLecheProjectionCase.projectionRewriteWitness
#print axioms ConstitutiveAlignment.ConLecheProjectionCase.rewriteProjection
#print axioms ConstitutiveAlignment.ConLecheProjectionCase.rewriteBody
#print axioms ConstitutiveAlignment.ConLecheProjectionCase.ProjectionRewriteWitness
#print axioms ConstitutiveAlignment.ConLecheProjectionCase.DeclaredType
#print axioms ConstitutiveAlignment.ConLecheProjectionCase.DeclarationBody
#print axioms ConstitutiveAlignment.ConLecheProjectionCase.LocatedDeclaration
#print axioms ConstitutiveAlignment.ConLecheProjectionCase.ProjectionRewriteWitness.preservesFalse
#print axioms ConstitutiveAlignment.ConLecheProjectionCase.projectionNoFalseTransport
#print axioms ConstitutiveAlignment.ConLecheProjectionCase.metadataErasureNoFalseTransport
#print axioms ConstitutiveAlignment.ConLecheProjectionCase.substitutedType_hasNoFaithfulRewrite
#print axioms ConstitutiveAlignment.ConLecheProjectionCase.acceptedSubstitution_hasNoFaithfulRewrite
/- AXIOM_AUDIT_END -/
