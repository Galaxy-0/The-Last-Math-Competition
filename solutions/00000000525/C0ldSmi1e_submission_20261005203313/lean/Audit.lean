import Conjecture525
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let env ← getEnv
  let names := env.constants.toList.filterMap fun (name, _) =>
    match env.getModuleIdxFor? name with
    | some idx => if env.header.moduleNames[idx.toNat]! == `Conjecture525 then some name else none
    | none => none
  let names := names.mergeSort Name.quickLt
  unless names.length > 0 do
    throwError "No authored declarations found."
  for name in names do
    let axioms ← collectAxioms name
    for axiomName in axioms do
      unless axiomName == `propext || axiomName == `Classical.choice || axiomName == `Quot.sound do
        throwError "Forbidden axiom {axiomName} in {name}."
    logInfo m!"AUDIT {name}: {axioms}"
  logInfo m!"Audited {names.length} authored declarations, including generated declarations."

#print axioms Conjecture525.local_conjecture_false
#print axioms Conjecture525.global_conjecture_false
