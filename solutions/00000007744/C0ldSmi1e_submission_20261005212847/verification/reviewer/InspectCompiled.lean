import Check
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

open Lean Elab Command Meta

set_option maxHeartbeats 0
set_option pp.all true

private def kindName : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

run_cmd do
  let env ← getEnv
  let selectedModules := [`Conjecture7744, `Audit, `Check]
  let names := env.constants.toList.map Prod.fst |>.filter fun name =>
    match env.getModuleIdxFor? name with
    | some idx => selectedModules.contains env.header.moduleNames[idx]!
    | none => false
  let names := names.mergeSort (fun a b => a.toString ≤ b.toString)
  let mut rows : Array Json := #[]
  for name in names do
    let some ci := env.find? name | throwError "Missing inspected declaration {name}"
    let (_, closure) := ((Lean.CollectAxioms.collect name).run env).run {}
    let mut closureUnsafe : Array String := #[]
    let mut closurePartial : Array String := #[]
    let mut closureMissing : Array String := #[]
    let mut closureNames : Array String := #[]
    for dep in closure.visited do
      closureNames := closureNames.push dep.toString
      match env.find? dep with
      | none => closureMissing := closureMissing.push dep.toString
      | some info =>
        if info.isUnsafe then closureUnsafe := closureUnsafe.push dep.toString
        if info.isPartial then closurePartial := closurePartial.push dep.toString
    let ty ← liftTermElabM <| Meta.ppExpr ci.type
    let val ← match ci.value? (allowOpaque := true) with
      | some value => do
        let text ← liftTermElabM <| Meta.ppExpr value
        pure text.pretty
      | none => pure "<no value>"
    rows := rows.push <| Json.mkObj [
      ("name", toJson name.toString),
      ("module", toJson env.header.moduleNames[(env.getModuleIdxFor? name).get!]!.toString),
      ("kind", toJson (kindName ci)),
      ("unsafe", toJson ci.isUnsafe),
      ("partial", toJson ci.isPartial),
      ("type", toJson ty.pretty),
      ("value", toJson val),
      ("direct_dependencies", toJson (ci.getUsedConstantsAsSet.toList.map Name.toString)),
      ("dependency_closure", toJson closureNames),
      ("axioms", toJson (closure.axioms.map Name.toString)),
      ("unsafe_dependencies", toJson closureUnsafe),
      ("partial_dependencies", toJson closurePartial),
      ("missing_dependencies", toJson closureMissing)]
  liftIO <| IO.FS.writeFile "/private/tmp/tlmc7744-review/compiled-declarations.json"
    ((Json.arr rows).pretty ++ "\n")
  logInfo m!"Independently inspected {rows.size} compiled declarations."
