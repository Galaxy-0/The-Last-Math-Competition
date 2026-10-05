import Conjecture7158
import Lean

set_option pp.universes true
set_option pp.fullNames true

open Lean in
run_elab do
  let env ← getEnv
  let modules : Array Name := #[`Conjecture7158]
  let mut count := 0
  for (name, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let moduleName := env.allImportedModuleNames[idx.toNat]!
      if modules.contains moduleName then
        let kind := match ci with
          | .axiomInfo _ => "axiom"
          | .defnInfo _ => "definition"
          | .thmInfo _ => "theorem"
          | .opaqueInfo _ => "opaque"
          | .quotInfo _ => "quotient"
          | .inductInfo _ => "inductive"
          | .ctorInfo _ => "constructor"
          | .recInfo _ => "recursor"
        let typeText ← Meta.ppExpr ci.type
        let axioms ← collectAxioms name
        let record := Json.mkObj [
          ("name", toJson name.toString),
          ("module", toJson moduleName.toString),
          ("kind", toJson kind),
          ("type", toJson typeText.pretty),
          ("unsafe", toJson ci.isUnsafe),
          ("partial", toJson ci.isPartial),
          ("axioms", toJson (axioms.map Name.toString))]
        IO.println ("ENVDECL " ++ record.compress)
        count := count + 1
  IO.println ("ENVCOUNT " ++ toString count)
