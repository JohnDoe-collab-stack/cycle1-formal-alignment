import ConstitutiveSearch.HistoricalErasure.LowerBound.QueryBound

/-!
# Regressions for the lower-bound attempt

Exhaustive finite tests supplement the quantified theorems. They compare full
outputs, including rejected structural inputs, and distinguish unrestricted
branch-answer tables from the actual uniform-viability promise.
-/

namespace ConstitutiveSearch.HistoricalErasure.LowerBound.Regression

def cellChoices : List Cell :=
  [false, true].flatMap fun d => [false, true].flatMap fun y =>
    [false, true].map fun z => ⟨d, y, z⟩

def chains : Nat → List (List Cell)
  | 0 => [[]]
  | n + 1 => cellChoices.flatMap fun c => (chains n).map (List.cons c)

@[noinline] def directCheck (cells : List Cell) : Bool :=
  let direct := directNormalize cells
  let original := execute cells
  direct.output == original.output && direct.cellVisits == cells.length &&
    coreValues direct.output == coreValues cells &&
    decisionValues direct.output == retainedHistory cells.length

theorem exact_query_optimum (n : Nat) :
    (∀ tree, ChainCorrect n tree → 1 ≤ (tree.trace QueryTree.zero).length) ∧
    ChainCorrect n (oneQuery n) ∧
    (∀ oracle, ((oneQuery n).trace oracle).length = 1) :=
  chain_query_optimum_one n

theorem claimed_query_necessity_false_at64 :
    ¬ (∀ tree : QueryTree (List Bool), ChainCorrect 64 tree →
      2 ^ 64 ≤ (tree.trace QueryTree.zero).length) :=
  no_exponential_query_necessity 63

theorem independent_necessity_at64 (tree : QueryTree (List Bool))
    (correct : tree.Correct (branches 64)) :
    2 ^ 64 ≤ (tree.trace QueryTree.zero).length :=
  independent_exponential_lower_bound 64 tree correct

theorem direct_output_all_inputs (cells : List Cell) :
    (execute cells).output = (directNormalize cells).output :=
  executed_output_eq_direct (execute cells)

theorem isolated_answer_breaks_oneQuery :
    (oneQuery 2).eval (QueryTree.singleton [false, false]) = false ∧
    (QueryTree.scan (branches 2)).eval (QueryTree.singleton [false, false]) = true := by
  decide

def putParts (out : IO.FS.Stream) : List String → IO Unit
  | [] => pure ()
  | s :: rest => do
      out.putStr s
      putParts out rest

/-- Separate writes avoid the unnecessary proof dependencies of string append. -/
def emitParts (parts : List String) : IO Unit := do
  let out ← IO.getStdout
  putParts out parts
  out.putStr "\n"

def runExhaustive : List Nat → IO Nat
  | [] => pure 0
  | n :: rest => do
      let inputs := chains n
      unless inputs.all directCheck do
        throw (IO.userError "exhaustive direct comparison failed")
      emitParts ["exhaustiveDepth=", Nat.repr n, "; chainsChecked=", Nat.repr inputs.length]
      let tail ← runExhaustive rest
      pure (inputs.length + tail)

def runQueries : List Nat → IO Unit
  | [] => pure ()
  | n :: rest => do
      let baseline := QueryTree.scan (branches n)
      let visits := (baseline.trace QueryTree.zero).length
      unless visits == 2 ^ n && baseline.eval QueryTree.zero == false do
        throw (IO.userError "independent baseline failed")
      let one := oneQuery n
      unless (one.trace QueryTree.zero).length == 1 &&
          one.eval QueryTree.zero == false && one.eval (fun _ => true) == true do
        throw (IO.userError "promised one-query check failed")
      emitParts ["depth=", Nat.repr n, "; independentQueries=", Nat.repr visits,
        "; chainPromiseQueries=1"]
      runQueries rest

def runLarge : List Nat → IO Unit
  | [] => pure ()
  | n :: rest => do
      let input := List.replicate n (Cell.mk false true false)
      unless directCheck input do
        throw (IO.userError "large direct comparison failed")
      emitParts ["depth=", Nat.repr n, "; directCellVisits=",
        Nat.repr (directNormalize input).cellVisits, "; originalLedger=",
        Nat.repr (execute input).work, "; outputsEqual=true"]
      runLarge rest

def runChecks : IO Unit := do
  let checked ← runExhaustive [0, 1, 2, 3, 4]
  unless checked == 4681 do
    throw (IO.userError "unexpected exhaustive chain count")
  runQueries [0, 1, 2, 4, 8]
  runLarge [16, 32, 64, 256, 1024]
  unless (oneQuery 2).eval (QueryTree.singleton [false, false]) == false &&
      (QueryTree.scan (branches 2)).eval (QueryTree.singleton [false, false]) == true do
    throw (IO.userError "independent singleton diagnostic failed")
  emitParts ["LOWER_BOUND_REGRESSIONS_PASSED"]

end ConstitutiveSearch.HistoricalErasure.LowerBound.Regression

def main : IO Unit := ConstitutiveSearch.HistoricalErasure.LowerBound.Regression.runChecks

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.HistoricalErasure.LowerBound.Regression.exact_query_optimum
#print axioms ConstitutiveSearch.HistoricalErasure.LowerBound.Regression.claimed_query_necessity_false_at64
#print axioms ConstitutiveSearch.HistoricalErasure.LowerBound.Regression.independent_necessity_at64
#print axioms ConstitutiveSearch.HistoricalErasure.LowerBound.Regression.direct_output_all_inputs
#print axioms ConstitutiveSearch.HistoricalErasure.LowerBound.Regression.isolated_answer_breaks_oneQuery
/- AXIOM_AUDIT_END -/
