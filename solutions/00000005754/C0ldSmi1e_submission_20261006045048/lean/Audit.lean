import Counterexample
import Lean

open Lean Elab Command

/- This is a verification program, not an additional mathematical assumption.
   It enumerates declarations by their compiled module ownership, including
   private/generated declarations, and uses Lean's transitive axiom collector. -/
run_cmd do
  let env ← getEnv
  let mut rows : Array Json := #[]
  let mut count := 0
  for (name, info) in env.constants.toList.toArray.qsort (fun a b => Name.lt a.1 b.1) do
    let some idx := env.getModuleIdxFor? name | continue
    let moduleName := env.header.moduleNames[idx.toNat]!
    unless moduleName == `Counterexample do continue
    count := count + 1
    if info.isUnsafe then throwError "Unsafe authored declaration: {name}"
    if info.isAxiom then throwError "Authored axiom declaration: {name}"
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Forbidden transitive axiom {ax} in {name}"
    let kind : String := match info with
      | .axiomInfo _ => "axiom"
      | .defnInfo _ => "definition"
      | .thmInfo _ => "theorem"
      | .opaqueInfo _ => "opaque"
      | .quotInfo _ => "quotient"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
      | .inductInfo _ => "inductive"
    let typeText : String := (← liftTermElabM <| Meta.ppExpr info.type).pretty
    let refs := info.type.getUsedConstants ++
      ((info.value? true).map Expr.getUsedConstants |>.getD #[])
    let refs := refs.toList.eraseDups.toArray.qsort Name.lt
    rows := rows.push <| Json.mkObj [
      ("name", toJson name.toString), ("module", toJson moduleName.toString),
      ("kind", toJson kind), ("unsafe", toJson info.isUnsafe),
      ("type", toJson typeText),
      ("transitive_axioms", toJson (axioms.qsort Name.lt |>.map Name.toString)),
      ("direct_constants", toJson (refs.map Name.toString))]
    logInfo m!"AUDITED {name}: {kind}; axioms={axioms.qsort Name.lt}"
  if count == 0 then throwError "No mathematical declarations found"
  liftIO <| IO.FS.writeFile "logs/declarations.json" (Json.pretty (Json.arr rows) ++ "\n")
  logInfo m!"PASS: audited every one of {count} declarations owned by Counterexample"
