import Audit407

/- Operational declaration inventory only; not part of either mathematical module. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names : List String := env.constants.toList.filterMap fun (n, _) =>
    if "Conjecture407".isPrefixOf n.toString then some n.toString else none
  for name in names.mergeSort (fun a b => decide (a ≤ b)) do
    logInfo m!"{name}"
