import ConstitutiveSearch.HistoricalErasure.Amplification

/-!
# Closed regressions and executable checks

Large reference widths are evaluated arithmetically. The exponential reference
frontier is enumerated only at depth four in these tests, never at depth 64.
The general claims are theorems in Amplification, not inferred from these runs.
-/

namespace ConstitutiveSearch.HistoricalErasure.Regression

/-- A coupled core: neighboring core coordinates must differ. -/
def Alternates : List Bool → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => a ≠ b ∧ Alternates (b :: rest)

def alternatingCore : Nat → Bool → List Bool
  | 0, _ => []
  | n + 1, bit => bit :: alternatingCore n (!bit)

/-- All decisions start false; each outgoing source guard is nonetheless true. -/
def sample (n : Nat) : List Cell :=
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

theorem coupled_core_accepted : Alternates [false, true, false, true] := by decide

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
    [Cell.mk false false false] ≠ [Cell.mk false true false] := by decide

/-- Check only observations of the one actual run, not a reference replay. -/
def checkRun (n : Nat) : Bool :=
  let input := sample n
  let run := execute input
  (input.length == n) && (run.output.length == n) &&
    (coreValues run.output == coreValues input) &&
    (decisionValues run.output == List.replicate n true) &&
    (run.history == decisionValues run.output) &&
    (run.program.length == n) && (run.attempts == 6 * n) && (run.work == 60 * n)

def printRun (n : Nat) : IO Unit := do
  let input := sample n
  let run := execute input
  unless checkRun n do
    throw (IO.userError s!"historical erasure regression failed at depth {n}")
  IO.println s!"depth={n}; referenceWidth={2 ^ n}; retainedWidth=1; attempts={run.attempts}; rowEventLedger={run.work}; codeTables={run.program.length}"

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
