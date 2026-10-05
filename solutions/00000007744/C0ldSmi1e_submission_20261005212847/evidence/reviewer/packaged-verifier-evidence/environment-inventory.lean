import Conjecture7744
import Audit
import Lean

set_option pp.universes true
set_option pp.fullNames true

set_option maxRecDepth 20000
set_option maxHeartbeats 0

open Lean
namespace IndependentTrustInspection

def deps (ci : ConstantInfo) : Array Name :=
  let body := match ci with
    | .defnInfo v => v.value.getUsedConstants
    | .thmInfo v => v.value.getUsedConstants
    | .opaqueInfo v => v.value.getUsedConstants
    | .inductInfo v => v.all.toArray ++ v.ctors.toArray
    | .recInfo v => v.all.toArray ++ v.rules.foldl (fun acc rule =>
        acc ++ #[rule.ctor] ++ rule.rhs.getUsedConstants) #[]
    | _ => #[]
  ci.type.getUsedConstants ++ body

partial def closure (env : Environment) (todo : List Name) (seen : NameSet := {}) : NameSet :=
  match todo with
  | [] => seen
  | n :: todo =>
    if seen.contains n then closure env todo seen else
    let seen := seen.insert n
    match env.checked.get.find? n with
    | none => closure env todo seen
    | some ci => closure env ((deps ci).toList ++ todo) seen

run_elab do
  let env ← getEnv
  let modules : Array Name := #[`Conjecture7744, `Audit]
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
        let reach := closure env [name]
        let unsafeReach := reach.toList.filter fun c =>
          (env.checked.get.find? c).any (·.isUnsafe)
        let partialReach := reach.toList.filter fun c =>
          (env.checked.get.find? c).any (·.isPartial)
        let missingReach := reach.toList.filter fun c => (env.checked.get.find? c).isNone
        let record := Json.mkObj [
          ("name", toJson name.toString),
          ("module", toJson moduleName.toString),
          ("kind", toJson kind),
          ("type", toJson typeText.pretty),
          ("unsafe", toJson ci.isUnsafe),
          ("partial", toJson ci.isPartial),
          ("axioms", toJson (axioms.map Name.toString)),
          ("direct_dependencies", toJson ((deps ci).map Name.toString)),
          ("closure_size", toJson reach.toList.length),
          ("unsafe_closure", toJson (unsafeReach.map Name.toString)),
          ("partial_closure", toJson (partialReach.map Name.toString)),
          ("missing_closure", toJson (missingReach.map Name.toString))]
        IO.println ("ENVDECL " ++ record.compress)
        count := count + 1
  IO.println ("ENVCOUNT " ++ toString count)
end IndependentTrustInspection
