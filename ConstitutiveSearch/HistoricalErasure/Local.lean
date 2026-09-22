import Init.Omega
import ConstitutiveSearch.AcceptingTransport

/-!
# Historically enabled, non-invertible local transport

Structural continuations and acceptance are separate. The incoming guard is
part of the state; it is not an acceptance oracle. A complete finite language
of two-input Boolean payload functions is searched, with a truth-table check
on each candidate. No successful relation witness is supplied to discovery.

Counters count explicit candidate and truth-table-row visits, not machine time.
-/

namespace ConstitutiveSearch.HistoricalErasure

structure LocalState where
  guard : Bool
  decision : Bool
  deriving DecidableEq, Repr

structure LocalContinuation where
  payload : Bool
  core : Bool
  nextDecision : Bool
  deriving DecidableEq, Repr

def source (guard : Bool) : LocalState := ⟨guard, false⟩
def target (guard : Bool) : LocalState := ⟨guard, true⟩

def localAccept (state : LocalState) (c : LocalContinuation) : Prop :=
  (state.decision = true → c.payload = c.core) ∧
  (state.decision = true → state.guard = true) ∧
  (c.nextDecision = true → state.decision = true ∨ c.payload ≠ c.core)

def localSystem : SearchSystem where
  State := LocalState
  Continuation := fun _ => LocalContinuation
  Accept := localAccept

def reset (c : LocalContinuation) : LocalContinuation :=
  ⟨c.core, c.core, c.nextDecision⟩

def enabledTransport (guard : Bool) (enabled : guard = true) :
    AcceptingContinuationTransport localSystem (source guard) (target guard) where
  map := reset
  preservesAccept := by
    intro c _accepted
    exact ⟨(fun _ => rfl), (fun _ => enabled), (fun _ => Or.inl rfl)⟩

def witnessZero : LocalContinuation := ⟨false, false, false⟩
def witnessOne : LocalContinuation := ⟨true, false, false⟩

theorem witnessZeroAccepted (guard : Bool) :
    localAccept (source guard) witnessZero := by
  exact ⟨(fun h => Bool.noConfusion h),
    (fun h => Bool.noConfusion h), (fun h => Bool.noConfusion h)⟩

theorem witnessOneAccepted (guard : Bool) :
    localAccept (source guard) witnessOne := by
  exact ⟨(fun h => Bool.noConfusion h),
    (fun h => Bool.noConfusion h), (fun h => Bool.noConfusion h)⟩

theorem witnessesDistinct : witnessZero ≠ witnessOne := by
  intro same
  have impossible : false = true := congrArg LocalContinuation.payload same
  cases impossible

theorem resetCollision : reset witnessZero = reset witnessOne := rfl

theorem acceptedCollision :
    localAccept (source true) witnessZero ∧
    localAccept (source true) witnessOne ∧
    witnessZero ≠ witnessOne ∧ reset witnessZero = reset witnessOne :=
  ⟨witnessZeroAccepted true, witnessOneAccepted true, witnessesDistinct, resetCollision⟩

theorem resetNotInjective : ¬ Function.Injective reset := by
  intro injective
  exact witnessesDistinct (injective resetCollision)

theorem resetNoLeftInverse :
    ¬ ∃ reverse : LocalContinuation → LocalContinuation,
      ∀ c, reverse (reset c) = c := by
  intro existsReverse
  rcases existsReverse with ⟨reverse, law⟩
  exact witnessesDistinct ((law witnessZero).symm.trans
    ((congrArg reverse resetCollision).trans (law witnessOne)))

theorem blockedTargetRejects (c : LocalContinuation) :
    ¬ localAccept (target false) c := by
  intro accepted
  have impossible : false = true := accepted.2.1 rfl
  cases impossible

theorem blockedTransportImpossible
    (transport : AcceptingContinuationTransport
      localSystem (source false) (target false)) : False :=
  blockedTargetRejects (transport.map witnessZero)
    (transport.preservesAccept witnessZero (witnessZeroAccepted false))

def outgoingGuard (decision payload core : Bool) : Bool :=
  decision || !(payload == core)

theorem executedTargetEnablesNext (c : LocalContinuation) :
    outgoingGuard (target true).decision (reset c).payload (reset c).core = true := rfl

/-- A payload function on the four (payload, core) inputs. -/
structure PayloadTable where
  ff : Bool
  ft : Bool
  tf : Bool
  tt : Bool
  deriving DecidableEq, Repr

def PayloadTable.eval (t : PayloadTable) (payload core : Bool) : Bool :=
  if payload then (if core then t.tt else t.tf)
  else (if core then t.ft else t.ff)

def PayloadTable.apply (t : PayloadTable) (c : LocalContinuation) : LocalContinuation :=
  ⟨t.eval c.payload c.core, c.core, c.nextDecision⟩

def resetTable : PayloadTable := ⟨false, true, false, true⟩

theorem resetTable_apply (c : LocalContinuation) : resetTable.apply c = reset c := by
  cases c with
  | mk p z s => cases p <;> cases z <;> rfl

def localAcceptB (state : LocalState) (c : LocalContinuation) : Bool :=
  (!state.decision || (c.payload == c.core)) &&
  (!state.decision || state.guard) &&
  (!c.nextDecision || state.decision || !(c.payload == c.core))

/-- Exactly the eight structural inputs; rejected inputs are not removed. -/
def localRows : List LocalContinuation :=
  [⟨false, false, false⟩, ⟨false, false, true⟩,
   ⟨false, true, false⟩, ⟨false, true, true⟩,
   ⟨true, false, false⟩, ⟨true, false, true⟩,
   ⟨true, true, false⟩, ⟨true, true, true⟩]

structure RowCheck where
  valid : Bool
  visits : Nat
  deriving DecidableEq, Repr

/-- The visit count forces traversal of the full supplied row list. -/
def checkRows (guard : Bool) (t : PayloadTable) : List LocalContinuation → RowCheck
  | [] => ⟨true, 0⟩
  | c :: rest =>
      let tail := checkRows guard t rest
      let thisRow := !localAcceptB (source guard) c ||
        localAcceptB (target guard) (t.apply c)
      ⟨thisRow && tail.valid, tail.visits + 1⟩

def checkTable (guard : Bool) (t : PayloadTable) : RowCheck :=
  checkRows guard t localRows

theorem checkRows_visits (g : Bool) (t : PayloadTable) (rows : List LocalContinuation) :
    (checkRows g t rows).visits = rows.length := by
  induction rows with
  | nil => rfl
  | cons c rest ih => exact congrArg Nat.succ ih

theorem checkTable_visits (g : Bool) (t : PayloadTable) :
    (checkTable g t).visits = 8 := checkRows_visits g t localRows

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem truthTableSound : ∀ (g a b c d p z s : Bool),
    (checkTable g ⟨a, b, c, d⟩).valid = true →
    localAccept (source g) ⟨p, z, s⟩ →
    localAccept (target g) ((PayloadTable.mk a b c d).apply ⟨p, z, s⟩) := by
  decide

theorem checkTable_sound (g : Bool) (t : PayloadTable)
    (valid : (checkTable g t).valid = true) (continuation : LocalContinuation) :
    localAccept (source g) continuation →
      localAccept (target g) (t.apply continuation) := by
  cases t with
  | mk a b c d =>
    cases continuation with
    | mk p z s => exact truthTableSound g a b c d p z s valid

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem truthTableUnique : ∀ (g a b c d : Bool),
    (checkTable g ⟨a, b, c, d⟩).valid = true →
    g = true ∧ (PayloadTable.mk a b c d) = resetTable := by
  decide

theorem checkTable_unique (g : Bool) (t : PayloadTable)
    (valid : (checkTable g t).valid = true) : g = true ∧ t = resetTable := by
  cases t with
  | mk a b c d => exact truthTableUnique g a b c d valid

abbrev Certificate (guard : Bool) := {t : PayloadTable // (checkTable guard t).valid = true}

def Certificate.transport {g : Bool} (c : Certificate g) :
    AcceptingContinuationTransport localSystem (source g) (target g) where
  map := c.val.apply
  preservesAccept := checkTable_sound g c.val c.property

/-- Enumerate all 16 tables from their bits, not from a list of valid transports. -/
def payloadTables : List PayloadTable :=
  [false, true].flatMap fun a => [false, true].flatMap fun b =>
    [false, true].flatMap fun c => [false, true].map fun d => ⟨a, b, c, d⟩

theorem payloadTables_complete (t : PayloadTable) : t ∈ payloadTables := by
  cases t with
  | mk a b c d => cases a <;> cases b <;> cases c <;> cases d <;> decide

structure Discovery (guard : Bool) where
  result : Option (Certificate guard)
  attempts : Nat
  rowVisits : Nat

def searchTables (guard : Bool) : List PayloadTable → Discovery guard
  | [] => ⟨none, 0, 0⟩
  | t :: rest =>
      let checked := checkTable guard t
      if valid : checked.valid = true then
        ⟨some ⟨t, valid⟩, 1, checked.visits⟩
      else
        let tail := searchTables guard rest
        ⟨tail.result, tail.attempts + 1, tail.rowVisits + checked.visits⟩

def discover (guard : Bool) : Discovery guard := searchTables guard payloadTables

set_option maxRecDepth 4096 in
theorem discover_true_found : (discover true).result ≠ none := by decide

set_option maxRecDepth 4096 in
theorem discover_false_none : (discover false).result = none := by decide

theorem discover_true_attempts : (discover true).attempts = 6 := by decide
theorem discover_true_rows : (discover true).rowVisits = 48 := by decide
theorem discover_false_attempts : (discover false).attempts = 16 := by decide

def discoveredCertificate (g : Bool) (enabled : g = true) : Certificate g :=
  match found : (discover g).result with
  | none => False.elim (by cases enabled; exact discover_true_found found)
  | some c => c

theorem discoveredCertificate_from_run (g : Bool) (enabled : g = true) :
    (discover g).result = some (discoveredCertificate g enabled) := by
  unfold discoveredCertificate
  split
  · rename_i found
    exact False.elim (by cases enabled; exact discover_true_found found)
  · rfl

theorem discoveredCertificate_table (g : Bool) (enabled : g = true) :
    (discoveredCertificate g enabled).val = resetTable :=
  (checkTable_unique g _ (discoveredCertificate g enabled).property).2

end ConstitutiveSearch.HistoricalErasure

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.HistoricalErasure.enabledTransport
#print axioms ConstitutiveSearch.HistoricalErasure.acceptedCollision
#print axioms ConstitutiveSearch.HistoricalErasure.resetNoLeftInverse
#print axioms ConstitutiveSearch.HistoricalErasure.blockedTransportImpossible
#print axioms ConstitutiveSearch.HistoricalErasure.checkTable_sound
#print axioms ConstitutiveSearch.HistoricalErasure.checkTable_unique
#print axioms ConstitutiveSearch.HistoricalErasure.Certificate.transport
#print axioms ConstitutiveSearch.HistoricalErasure.payloadTables_complete
#print axioms ConstitutiveSearch.HistoricalErasure.discover_true_found
#print axioms ConstitutiveSearch.HistoricalErasure.discover_false_none
#print axioms ConstitutiveSearch.HistoricalErasure.discoveredCertificate_from_run
#print axioms ConstitutiveSearch.HistoricalErasure.discoveredCertificate_table
/- AXIOM_AUDIT_END -/
