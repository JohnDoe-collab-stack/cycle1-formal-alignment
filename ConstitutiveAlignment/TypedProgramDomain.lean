import ConstitutiveAlignment.Machine

set_option linter.checkUnivs false

/-!
# Finite typed-program domain

This module defines the compact, total program domain used by the endogenous
succession witness.  Programs are intrinsically typed; their constitutive
formation is retained separately from their extensional behavior.  A corpus is
a positive list of certified abstractions, and its frontier is computed by a
single exhaustive search for the first missing typed composition.
-/

namespace ConstitutiveAlignment
namespace TypedProgram

inductive ProgramType : Type
  | bit
  | pair
  deriving DecidableEq, Repr

def Carrier : ProgramType → Type
  | .bit => Bool
  | .pair => Bool × Bool

inductive Program : ProgramType → ProgramType → Type
  | identity (type : ProgramType) : Program type type
  | negate : Program .bit .bit
  | duplicate : Program .bit .pair
  | first : Program .pair .bit
  | compose {source middle target : ProgramType} :
      Program source middle → Program middle target → Program source target

def Program.evaluate {source target : ProgramType}
    (program : Program source target) : Carrier source → Carrier target :=
  match program with
  | .identity _type => fun value => value
  | .negate => fun value => Bool.not value
  | .duplicate => fun value => (value, value)
  | .first => fun value => value.1
  | .compose firstProgram secondProgram => fun value =>
      secondProgram.evaluate (firstProgram.evaluate value)

inductive Formation : Type
  | identity (type : ProgramType)
  | negate
  | duplicate
  | first
  | compose (first second : Formation)
  deriving DecidableEq, Repr

def Formation.matches (left right : Formation) : Bool :=
  decide (left = right)

def Formation.depth : Formation → Nat
  | .identity _type => 1
  | .negate => 1
  | .duplicate => 1
  | .first => 1
  | .compose leftFormation rightFormation =>
      Nat.max (Formation.depth leftFormation)
        (Formation.depth rightFormation) + 1

def Program.formation {source target : ProgramType}
    (program : Program source target) : Formation :=
  match program with
  | .identity type => .identity type
  | .negate => .negate
  | .duplicate => .duplicate
  | .first => .first
  | .compose firstProgram secondProgram =>
      .compose firstProgram.formation secondProgram.formation

structure CertifiedProgramAbstraction where
  address : Nat
  source : ProgramType
  target : ProgramType
  program : Program source target

def CertifiedProgramAbstraction.formation
    (abstraction : CertifiedProgramAbstraction) : Formation :=
  abstraction.program.formation

def CertifiedProgramAbstraction.evaluate
    (abstraction : CertifiedProgramAbstraction) :
    Carrier abstraction.source → Carrier abstraction.target :=
  abstraction.program.evaluate

def CertifiedProgramAbstraction.renameAddress
    (rename : Nat → Nat)
    (abstraction : CertifiedProgramAbstraction) : CertifiedProgramAbstraction :=
  { abstraction with address := rename abstraction.address }

theorem CertifiedProgramAbstraction.formation_renameAddress
    (rename : Nat → Nat)
    (abstraction : CertifiedProgramAbstraction) :
    (abstraction.renameAddress rename).formation = abstraction.formation :=
  rfl

structure ProgramCorpus where
  first : CertifiedProgramAbstraction
  remaining : List CertifiedProgramAbstraction

def ProgramCorpus.abstractions (corpus : ProgramCorpus) :
    List CertifiedProgramAbstraction :=
  corpus.first :: corpus.remaining

def ProgramCorpus.formations (corpus : ProgramCorpus) : List Formation :=
  corpus.abstractions.map CertifiedProgramAbstraction.formation

def ProgramCorpus.containsFormation
    (corpus : ProgramCorpus)
    (formation : Formation) : Bool :=
  corpus.formations.any (fun present => present.matches formation)

def ProgramCorpus.incorporate
    (corpus : ProgramCorpus)
    (abstraction : CertifiedProgramAbstraction) : ProgramCorpus :=
  ⟨corpus.first, corpus.remaining ++ [abstraction]⟩

def ProgramCorpus.renameAddresses
    (rename : Nat → Nat)
    (corpus : ProgramCorpus) : ProgramCorpus :=
  ⟨corpus.first.renameAddress rename,
    corpus.remaining.map
      (CertifiedProgramAbstraction.renameAddress rename)⟩

def composeCertified :
    CertifiedProgramAbstraction → CertifiedProgramAbstraction →
      Option CertifiedProgramAbstraction
  | ⟨firstAddress, firstSource, firstTarget, firstProgram⟩,
      ⟨secondAddress, secondSource, secondTarget, secondProgram⟩ =>
      if equality : firstTarget = secondSource then
        match equality with
        | rfl =>
            some
              { address := firstAddress + secondAddress + 1
                source := firstSource
                target := secondTarget
                program := .compose firstProgram secondProgram }
      else
        none

def compositionsWith
    (first : CertifiedProgramAbstraction) :
    List CertifiedProgramAbstraction → List CertifiedProgramAbstraction
  | [] => []
  | second :: remaining =>
      match composeCertified first second with
      | some composition => composition :: compositionsWith first remaining
      | none => compositionsWith first remaining

def compositionCandidates
    (corpus : ProgramCorpus) : List CertifiedProgramAbstraction :=
  corpus.abstractions.flatMap
    (fun first => compositionsWith first corpus.abstractions)

inductive FrontierSearch
    (corpus : ProgramCorpus) :
    List CertifiedProgramAbstraction → Type
  | missing
      {candidates : List CertifiedProgramAbstraction}
      (candidate : CertifiedProgramAbstraction)
      (present : List.Mem candidate candidates)
      (fresh : corpus.containsFormation candidate.formation = false) :
      FrontierSearch corpus candidates
  | saturated
      {candidates : List CertifiedProgramAbstraction}
      (allPresent : (candidate : CertifiedProgramAbstraction) →
        List.Mem candidate candidates →
          corpus.containsFormation candidate.formation = true) :
      FrontierSearch corpus candidates

def searchFrontier
    (corpus : ProgramCorpus) :
    (candidates : List CertifiedProgramAbstraction) →
      FrontierSearch corpus candidates
  | [] => .saturated (by
      intro candidate membership
      nomatch membership)
  | candidate :: remaining =>
      match equality : corpus.containsFormation candidate.formation with
      | false => .missing candidate (.head remaining) equality
      | true =>
          match searchFrontier corpus remaining with
          | .missing missing membership fresh =>
              .missing missing (.tail candidate membership) fresh
          | .saturated allPresent =>
              .saturated (by
                intro present membership
                cases membership with
                | head => exact equality
                | tail _membershipHead membershipTail =>
                    exact allPresent present membershipTail)

def programFrontier (corpus : ProgramCorpus) :
    FrontierSearch corpus (compositionCandidates corpus) :=
  searchFrontier corpus (compositionCandidates corpus)

def FrontierSearch.candidate?
    {corpus : ProgramCorpus}
    {candidates : List CertifiedProgramAbstraction} :
    FrontierSearch corpus candidates → Option CertifiedProgramAbstraction
  | .missing candidate _present _fresh => some candidate
  | .saturated _allPresent => none

def programFrontierCandidate
    (corpus : ProgramCorpus) : Option CertifiedProgramAbstraction :=
  (programFrontier corpus).candidate?

inductive ProgramRegime :
    List CertifiedProgramAbstraction → Formation → Type
  | here {head remaining} :
      ProgramRegime (head :: remaining) head.formation
  | later {head remaining formation} :
      ProgramRegime remaining formation →
        ProgramRegime (head :: remaining) formation

/- The norm is an independently declared witness family.  It validates the
   same certified formation without reusing a `ProgramRegime` witness. -/
inductive ProgramNorm :
    List CertifiedProgramAbstraction → Formation → Type
  | certified {head remaining} :
      ProgramNorm (head :: remaining) head.formation
  | inherited {head remaining formation} :
      ProgramNorm remaining formation →
        ProgramNorm (head :: remaining) formation

structure ProgramSemanticWitness (formation : Formation) where
  source : ProgramType
  target : ProgramType
  program : Program source target
  formationExact : program.formation = formation
  semantics : Carrier source → Carrier target
  semanticsExact : semantics = program.evaluate

def ProgramNorm.semanticWitness
    {corpus : List CertifiedProgramAbstraction}
    {formation : Formation}
    (normative : ProgramNorm corpus formation) :
    ProgramSemanticWitness formation :=
  match normative with
  | @ProgramNorm.certified head _remaining =>
      { source := head.source
        target := head.target
        program := head.program
        formationExact := rfl
        semantics := head.program.evaluate
        semanticsExact := rfl }
  | .inherited prior => prior.semanticWitness

def regimeSound {corpus : List CertifiedProgramAbstraction}
    {formation : Formation}
    (admitted : ProgramRegime corpus formation) : ProgramNorm corpus formation :=
  match admitted with
  | .here => .certified
  | .later prior => .inherited (regimeSound prior)

def regimeComplete {corpus : List CertifiedProgramAbstraction}
    {formation : Formation}
    (normative : ProgramNorm corpus formation) : ProgramRegime corpus formation :=
  match normative with
  | .certified => .here
  | .inherited prior => .later (regimeComplete prior)

structure ProgramAdequacy (corpus : ProgramCorpus) where
  sound : (formation : Formation) →
    ProgramRegime corpus.abstractions formation →
      ProgramNorm corpus.abstractions formation
  complete : (formation : Formation) →
    ProgramNorm corpus.abstractions formation →
      ProgramRegime corpus.abstractions formation

def programAdequacy (corpus : ProgramCorpus) : ProgramAdequacy corpus :=
  { sound := fun _formation admitted => regimeSound admitted
    complete := fun _formation normative => regimeComplete normative }

def regimeAtEnd
    (priorEntries : List CertifiedProgramAbstraction)
    (abstraction : CertifiedProgramAbstraction) :
    ProgramRegime (priorEntries ++ [abstraction]) abstraction.formation :=
  match priorEntries with
  | [] => .here
  | _head :: remaining => .later (regimeAtEnd remaining abstraction)

def admittedAfterIncorporation
    (corpus : ProgramCorpus)
    (abstraction : CertifiedProgramAbstraction) :
    ProgramRegime (corpus.incorporate abstraction).abstractions
      abstraction.formation :=
  regimeAtEnd corpus.abstractions abstraction

def normativeAfterIncorporation
    (corpus : ProgramCorpus)
    (abstraction : CertifiedProgramAbstraction) :
    ProgramNorm (corpus.incorporate abstraction).abstractions
      abstraction.formation :=
  regimeSound (admittedAfterIncorporation corpus abstraction)

/-! ## Finite constructive instance -/

def negateAbstraction : CertifiedProgramAbstraction :=
  { address := 0
    source := .bit
    target := .bit
    program := .negate }

def initialCorpus : ProgramCorpus :=
  ⟨negateAbstraction, []⟩

def doubleNegateAbstraction : CertifiedProgramAbstraction :=
  { address := 1
    source := .bit
    target := .bit
    program := .compose .negate .negate }

theorem mismatchedComposition_isRejected :
    composeCertified
      { address := 3
        source := .bit
        target := .pair
        program := .duplicate }
      negateAbstraction = none :=
  rfl

def firstSuccessorCorpus : ProgramCorpus :=
  initialCorpus.incorporate doubleNegateAbstraction

def tripleNegateAbstraction : CertifiedProgramAbstraction :=
  { address := 2
    source := .bit
    target := .bit
    program := .compose .negate (.compose .negate .negate) }

def secondSuccessorCorpus : ProgramCorpus :=
  firstSuccessorCorpus.incorporate tripleNegateAbstraction

theorem doubleNegate_evaluatesAsIdentity (value : Bool) :
    doubleNegateAbstraction.evaluate value = value := by
  cases value <;> rfl

theorem doubleNegate_formationDiffersFromIdentity :
    doubleNegateAbstraction.formation =
      (Program.identity .bit).formation → False := by
  intro equality
  nomatch equality

theorem firstCertifiedAbstraction_isFresh :
    initialCorpus.containsFormation doubleNegateAbstraction.formation = false :=
  rfl

theorem firstFrontier_isDoubleNegate :
    (programFrontierCandidate initialCorpus).map
      CertifiedProgramAbstraction.formation =
      some doubleNegateAbstraction.formation :=
  rfl

theorem secondFrontier_isTripleNegate :
    (programFrontierCandidate firstSuccessorCorpus).map
      CertifiedProgramAbstraction.formation =
      some tripleNegateAbstraction.formation :=
  rfl

theorem firstIncorporation_changesNextFrontier :
    (programFrontierCandidate initialCorpus).map
        CertifiedProgramAbstraction.formation =
      (programFrontierCandidate firstSuccessorCorpus).map
        CertifiedProgramAbstraction.formation → False := by
  intro equality
  nomatch equality

def firstAbstractionAdmitted :
    ProgramRegime firstSuccessorCorpus.abstractions
      doubleNegateAbstraction.formation :=
  admittedAfterIncorporation initialCorpus doubleNegateAbstraction

def firstAbstractionNormative :
    ProgramNorm firstSuccessorCorpus.abstractions
      doubleNegateAbstraction.formation :=
  normativeAfterIncorporation initialCorpus doubleNegateAbstraction

def secondAbstractionAdmitted :
    ProgramRegime secondSuccessorCorpus.abstractions
      tripleNegateAbstraction.formation :=
  admittedAfterIncorporation firstSuccessorCorpus tripleNegateAbstraction

def secondAbstractionNormative :
    ProgramNorm secondSuccessorCorpus.abstractions
      tripleNegateAbstraction.formation :=
  normativeAfterIncorporation firstSuccessorCorpus tripleNegateAbstraction

end TypedProgram
end ConstitutiveAlignment

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveAlignment.TypedProgram.Formation.matches
#print axioms ConstitutiveAlignment.TypedProgram.ProgramCorpus.incorporate
#print axioms ConstitutiveAlignment.TypedProgram.programFrontierCandidate
#print axioms ConstitutiveAlignment.TypedProgram.Program.evaluate
#print axioms ConstitutiveAlignment.TypedProgram.searchFrontier
#print axioms ConstitutiveAlignment.TypedProgram.programFrontier
#print axioms ConstitutiveAlignment.TypedProgram.programAdequacy
#print axioms ConstitutiveAlignment.TypedProgram.ProgramNorm.semanticWitness
#print axioms ConstitutiveAlignment.TypedProgram.admittedAfterIncorporation
#print axioms ConstitutiveAlignment.TypedProgram.doubleNegate_evaluatesAsIdentity
#print axioms ConstitutiveAlignment.TypedProgram.doubleNegate_formationDiffersFromIdentity
#print axioms ConstitutiveAlignment.TypedProgram.mismatchedComposition_isRejected
#print axioms ConstitutiveAlignment.TypedProgram.firstCertifiedAbstraction_isFresh
#print axioms ConstitutiveAlignment.TypedProgram.firstFrontier_isDoubleNegate
#print axioms ConstitutiveAlignment.TypedProgram.secondFrontier_isTripleNegate
#print axioms ConstitutiveAlignment.TypedProgram.firstIncorporation_changesNextFrontier
/- AXIOM_AUDIT_END -/
