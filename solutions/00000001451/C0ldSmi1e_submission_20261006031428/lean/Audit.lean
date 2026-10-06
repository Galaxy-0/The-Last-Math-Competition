import Solution
import Lean.Util.CollectAxioms

open Lean Elab Command

/-! Recompute the declaration inventory from the actual imported compiled
modules, including generated and private declarations. No source-name scan
is used to identify the mathematical declarations. -/
run_cmd do
  let env ← getEnv
  let owned : Array Name := #[`Geometry, `Vanishing, `Solution]
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut rows : Array Json := #[]
  for (name, info) in env.constants.toList do
    if let some idx := env.const2ModIdx[name]? then
      let modName := env.header.moduleNames[idx.toNat]!
      if owned.contains modName then
        let axioms ← collectAxioms name
        for ax in axioms do
          unless allowed.contains ax do
            throwError "Disallowed axiom {ax} used by {name}"
        let kind := match info with
          | .axiomInfo _ => "axiom"
          | .defnInfo _ => "definition"
          | .thmInfo _ => "theorem"
          | .opaqueInfo _ => "opaque"
          | .quotInfo _ => "quotient"
          | .inductInfo _ => "inductive"
          | .ctorInfo _ => "constructor"
          | .recInfo _ => "recursor"
        if kind == "axiom" then throwError "Authored axiom declaration {name}"
        if info.isUnsafe then throwError "Unsafe authored declaration {name}"
        let ty ← liftTermElabM do
          return (← Meta.ppExpr info.type).pretty
        rows := rows.push <| Json.mkObj [
          ("module", toJson modName.toString),
          ("name", toJson name.toString),
          ("kind", toJson kind),
          ("type", toJson ty),
          ("axioms", toJson (axioms.map Name.toString))]
  for modName in owned do
    unless rows.any (fun row => (row.getObjValAs? String "module").toOption == some modName.toString) do
      throwError "No compiled declarations found for {modName}"
  let output := Json.mkObj [
    ("modules", toJson (owned.map Name.toString)),
    ("allowed_axioms", toJson (allowed.map Name.toString)),
    ("declaration_count", toJson rows.size),
    ("declarations", Json.arr rows)]
  liftIO <| IO.FS.writeFile "evidence/compiled-inventory.json" output.pretty
  logInfo m!"Audited {rows.size} compiled declarations across {owned.size} authored mathematical modules."

#print axioms TLMC1451.dimension_two_not_exact
#print axioms TLMC1451.dimension_two_not_asymptotic
#print axioms TLMC1451.dimension_two_not_theta
#print axioms TLMC1451.conjecture_exact_false
#print axioms TLMC1451.conjecture_asymptotic_false
#print axioms TLMC1451.conjecture_order_false
