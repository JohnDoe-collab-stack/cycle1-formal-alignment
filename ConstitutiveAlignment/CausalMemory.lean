import ConstitutiveAlignment.Machine

set_option linter.checkUnivs false

/-!
# Memory relative to declared futures

Memory is specified by the future distinctions that it must preserve.  The
question family is explicit: no claim is made about every conceivable future
observation.  Soundness, relative completeness, exactness, and autonomous
updating remain separate contracts.
-/

namespace ConstitutiveAlignment

universe uState uQuestion uAnswer uMemory

structure FutureQuestions (State : Type uState) where
  Question : Type uQuestion
  Answer : Question → Type uAnswer
  behaviour : State → (question : Question) → Answer question

def FutureEquivalent
    {State : Type uState}
    (future : FutureQuestions State)
    (left right : State) : Prop :=
  (question : future.Question) →
    future.behaviour left question = future.behaviour right question

namespace FutureEquivalent

theorem reflexive
    {State : Type uState}
    {future : FutureQuestions State}
    (state : State) : FutureEquivalent future state state :=
  fun _question => rfl

theorem symmetric
    {State : Type uState}
    {future : FutureQuestions State}
    {left right : State}
    (equivalent : FutureEquivalent future left right) :
    FutureEquivalent future right left :=
  fun question => (equivalent question).symm

theorem transitive
    {State : Type uState}
    {future : FutureQuestions State}
    {first second third : State}
    (firstSecond : FutureEquivalent future first second)
    (secondThird : FutureEquivalent future second third) :
    FutureEquivalent future first third :=
  fun question => (firstSecond question).trans (secondThird question)

end FutureEquivalent

structure MemoryEncoding (State : Type uState) where
  Memory : Type uMemory
  encode : State → Memory

def MemorySound
    {State : Type uState}
    (future : FutureQuestions State)
    (encoding : MemoryEncoding State) : Prop :=
  ∀ {left right},
    encoding.encode left = encoding.encode right →
      FutureEquivalent future left right

def MemoryComplete
    {State : Type uState}
    (future : FutureQuestions State)
    (encoding : MemoryEncoding State) : Prop :=
  ∀ {left right},
    FutureEquivalent future left right →
      encoding.encode left = encoding.encode right

structure ExactCausalMemory
    {State : Type uState}
    (future : FutureQuestions State)
    (encoding : MemoryEncoding State) : Prop where
  sound : MemorySound future encoding
  complete : MemoryComplete future encoding

abbrev MachineFutureQuestions
    (machine : ConstitutiveMachine) :=
  FutureQuestions machine.State

/- Equal memory justifies contraction only for the declared future questions. -/
theorem safeContraction
    {State : Type uState}
    {future : FutureQuestions State}
    {encoding : MemoryEncoding State}
    (sound : MemorySound future encoding)
    {left right : State}
    (sameMemory : encoding.encode left = encoding.encode right) :
    FutureEquivalent future left right :=
  sound sameMemory

/- A declared future distinction cannot be fused by a sound memory. -/
theorem memoryDistinct_of_futureDistinction
    {State : Type uState}
    {future : FutureQuestions State}
    {encoding : MemoryEncoding State}
    (sound : MemorySound future encoding)
    {left right : State}
    (question : future.Question)
    (distinguished :
      future.behaviour left question = future.behaviour right question → False) :
    encoding.encode left = encoding.encode right → False :=
  fun sameMemory => distinguished (sound sameMemory question)

structure AutonomousMemoryUpdate
    {State : Type uState}
    (encoding : MemoryEncoding State)
    (advance : State → State) where
  update : encoding.Memory → encoding.Memory
  commutes : (state : State) →
    encoding.encode (advance state) = update (encoding.encode state)

/-! ## Finite witnesses and separators -/

namespace MemoryExamples

inductive HorizonState : Type
  | left
  | right

inductive RichQuestion : Type
  | present
  | later

def richBehaviour : HorizonState → RichQuestion → Bool
  | .left, .present => false
  | .right, .present => false
  | .left, .later => false
  | .right, .later => true

def richFuture : FutureQuestions HorizonState where
  Question := RichQuestion
  Answer := fun _question => Bool
  behaviour := richBehaviour

theorem samePresentReading :
    richFuture.behaviour .left .present =
      richFuture.behaviour .right .present :=
  rfl

theorem differentRelevantFuture :
    richFuture.behaviour .left .later =
      richFuture.behaviour .right .later → False := by
  intro impossible
  nomatch impossible

inductive PresentQuestion : Type
  | present

def presentOnlyFuture : FutureQuestions HorizonState where
  Question := PresentQuestion
  Answer := fun _question => Bool
  behaviour := fun _state _question => false

def collapsedEncoding : MemoryEncoding HorizonState where
  Memory := Unit
  encode := fun _state => ()

theorem collapsedMemoryExact :
    ExactCausalMemory presentOnlyFuture collapsedEncoding where
  sound := by
    intro firstState secondState _sameMemory question
    cases firstState <;> cases secondState <;> cases question <;> rfl
  complete := fun _equivalent => rfl

theorem enrichmentRevealsCollapsedDifference :
    FutureEquivalent richFuture .left .right → False :=
  fun allegedEquivalence =>
    differentRelevantFuture (allegedEquivalence .later)

def richEncoding : MemoryEncoding HorizonState where
  Memory := Bool
  encode
    | .left => false
    | .right => true

theorem richMemoryExact : ExactCausalMemory richFuture richEncoding where
  sound := by
    intro firstState secondState sameMemory question
    cases firstState <;> cases secondState
    · rfl
    · nomatch sameMemory
    · nomatch sameMemory
    · rfl
  complete := by
    intro firstState secondState equivalent
    cases firstState <;> cases secondState
    · rfl
    · nomatch equivalent .later
    · nomatch equivalent .later
    · rfl

def advance : HorizonState → HorizonState
  | .left => .right
  | .right => .left

def richMemoryUpdate : AutonomousMemoryUpdate richEncoding advance where
  update := Bool.not
  commutes := by
    intro state
    cases state <;> rfl

def badConstantUpdate (_memory : richEncoding.Memory) : richEncoding.Memory :=
  false

theorem badConstantUpdate_failsAtLeft :
    richEncoding.encode (advance .left) =
      badConstantUpdate (richEncoding.encode .left) → False := by
  intro impossible
  nomatch impossible

/- Retaining the whole state is sound but need not be complete relative to a
   deliberately coarser future interface. -/
def firstCoordinateFuture : FutureQuestions (Bool × Bool) where
  Question := Unit
  Answer := fun _question => Bool
  behaviour := fun state _question => state.1

def wholeStateEncoding : MemoryEncoding (Bool × Bool) where
  Memory := Bool × Bool
  encode := fun state => state

theorem wholeStateEncoding_sound :
    MemorySound firstCoordinateFuture wholeStateEncoding := by
  intro left right sameMemory
  cases sameMemory
  exact fun _question => rfl

theorem wholeStateEncoding_notComplete :
    MemoryComplete firstCoordinateFuture wholeStateEncoding → False := by
  intro complete
  have equivalent :
      FutureEquivalent firstCoordinateFuture (false, false) (false, true) :=
    fun _question => rfl
  have impossible := complete equivalent
  have secondCoordinate : false = true := congrArg Prod.snd impossible
  nomatch secondCoordinate

end MemoryExamples

end ConstitutiveAlignment

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveAlignment.FutureEquivalent.transitive
#print axioms ConstitutiveAlignment.safeContraction
#print axioms ConstitutiveAlignment.memoryDistinct_of_futureDistinction
#print axioms ConstitutiveAlignment.MemoryExamples.collapsedMemoryExact
#print axioms ConstitutiveAlignment.MemoryExamples.enrichmentRevealsCollapsedDifference
#print axioms ConstitutiveAlignment.MemoryExamples.richMemoryExact
#print axioms ConstitutiveAlignment.MemoryExamples.richMemoryUpdate
#print axioms ConstitutiveAlignment.MemoryExamples.badConstantUpdate_failsAtLeft
#print axioms ConstitutiveAlignment.MemoryExamples.wholeStateEncoding_notComplete
/- AXIOM_AUDIT_END -/
