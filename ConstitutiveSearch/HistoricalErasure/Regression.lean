import ConstitutiveSearch.HistoricalErasure.Amplification

/-!
# Closed regressions and executable checks

Large reference widths are evaluated arithmetically. The exponential reference
frontier is enumerated only at depth four in these tests, never at depth 64.
The general claims are theorems in Amplification, not inferred from these runs.

The discovery and execution routines carry their compiler noinline attributes
in their defining modules. No imported declaration is modified here.
A single run produces a small observation record before IO rendering.
-/

namespace ConstitutiveSearch.HistoricalErasure.Regression

/-- A coupled core: neighboring core coordinates must differ. -/
def Alternates : List Bool → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => a ≠ b ∧ Alternates (b :: rest)

@[noinline] def alternatingCore : Nat → Bool → List Bool
  | 0, _ => []
  | n + 1, bit => bit :: alternatingCore n (!bit)

/-- All decisions start false; each outgoing source guard is nonetheless true. -/
@[noinline] def sample (n : Nat) : List Cell :=
  branchWitness (List.replicate n false) (alternatingCore n false)

theorem discovery_has_real_failures : (discover true).attempts = 6 :=
  discover_true_attempts

theorem no_certificate_when_blocked : (discover false).result = none :=
  discover_false_none

theorem corrupted_table_rejected :
    (checkTable true (PayloadTable.mk false false false false)).valid = false := by decide

theorem reference_four_distinct :
    (branches 4).length = 16 ∧ (branches 4).Nodup :=
  ⟨branches_length 4, branches_nodup 4⟩

theorem coupled_core_accepted : Alternates [false, true, false, true] := by
  change (false ≠ true) ∧ (true ≠ false) ∧ (false ≠ true) ∧ True
  decide

theorem every_four_bit_branch_viable :
    ∀ history, history ∈ branches 4 → (chainSystem 4 Alternates).Viable history :=
  all_reference_branches_viable 4 Alternates [false, true, false, true]
    rfl coupled_core_accepted

theorem actual_execution_collision :
    (execute [Cell.mk false false false]).output =
      (execute [Cell.mk false true false]).output := by decide

theorem collision_inputs_accepted_and_distinct :
    Accepted (fun _ => True) true [Cell.mk false false false] ∧
    Accepted (fun _ => True) true [Cell.mk false true false] ∧
    [Cell.mk false false false] ≠ [Cell.mk false true false] := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨True.intro, ⟨(fun h => Bool.noConfusion h), True.intro⟩⟩
  · exact ⟨True.intro, ⟨(fun h => Bool.noConfusion h), True.intro⟩⟩
  · decide

structure RunObservation where
  inputLength : Nat
  outputLength : Nat
  corePreserved : Bool
  decisionsRetained : Bool
  historyIsOutput : Bool
  codeTables : Nat
  attempts : Nat
  rowEventLedger : Nat
  deriving Repr

/-- Observe exactly one executed run; the exponential reference is not built. -/
@[noinline] def observeRun (n : Nat) : RunObservation :=
  let input := sample n
  let run := execute input
  let output := run.output
  let decisions := decisionValues output
  { inputLength := input.length
    outputLength := output.length
    corePreserved := coreValues output == coreValues input
    decisionsRetained := decisions == List.replicate n true
    historyIsOutput := run.history == decisions
    codeTables := run.program.length
    attempts := run.attempts
    rowEventLedger := run.work }

@[noinline] def validObservation (n : Nat) (o : RunObservation) : Bool :=
  (o.inputLength == n) && (o.outputLength == n) &&
    o.corePreserved && o.decisionsRetained && o.historyIsOutput &&
    (o.codeTables == n) && (o.attempts == 6 * n) && (o.rowEventLedger == 60 * n)

@[noinline] def checkRun (n : Nat) : Bool := validObservation n (observeRun n)

@[noinline] def printRun (n : Nat) : IO Unit := do
  let observed := observeRun n
  unless validObservation n observed do
    throw (IO.userError s!"historical erasure regression failed at depth {n}")
  IO.println s!"depth={n}; referenceWidth={2 ^ n}; retainedWidth=1; attempts={observed.attempts}; rowEventLedger={observed.rowEventLedger}; codeTables={observed.codeTables}"

def runChecks : IO Unit := do
  unless (discover false).result.isNone do
    throw (IO.userError "blocked guard produced a certificate")
  unless (checkTable true resetTable).valid do
    throw (IO.userError "valid certificate rejected")
  if (checkTable true (PayloadTable.mk false false false false)).valid then
    throw (IO.userError "corrupted certificate accepted")
  for n in [0, 1, 2, 4, 16, 32, 64] do
    printRun n
  IO.println "HISTORICAL_ERASURE_REGRESSIONS_PASSED"

end ConstitutiveSearch.HistoricalErasure.Regression

def main : IO Unit := ConstitutiveSearch.HistoricalErasure.Regression.runChecks

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.HistoricalErasure.Regression.discovery_has_real_failures
#print axioms ConstitutiveSearch.HistoricalErasure.Regression.no_certificate_when_blocked
#print axioms ConstitutiveSearch.HistoricalErasure.Regression.corrupted_table_rejected
#print axioms ConstitutiveSearch.HistoricalErasure.Regression.reference_four_distinct
#print axioms ConstitutiveSearch.HistoricalErasure.Regression.coupled_core_accepted
#print axioms ConstitutiveSearch.HistoricalErasure.Regression.every_four_bit_branch_viable
#print axioms ConstitutiveSearch.HistoricalErasure.Regression.actual_execution_collision
#print axioms ConstitutiveSearch.HistoricalErasure.Regression.collision_inputs_accepted_and_distinct
/- AXIOM_AUDIT_END -/
