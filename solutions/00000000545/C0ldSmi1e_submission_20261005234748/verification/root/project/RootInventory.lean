import Audit
import Lean.Util.CollectAxioms

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let modules := #[`Connectivity, `IdealBridge, `Conjecture545, `Check, `Audit]
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let moduleName := env.header.moduleNames[idx.toNat]!
      if modules.contains moduleName then
        let kind := match info with
          | .axiomInfo _ => "axiom"
          | .defnInfo _ => "definition"
          | .thmInfo _ => "theorem"
          | .opaqueInfo _ => "opaque"
          | .quotInfo _ => "quotient"
          | .inductInfo _ => "inductive"
          | .ctorInfo _ => "constructor"
          | .recInfo _ => "recursor"
        let axioms ← Lean.collectAxioms name
        logInfo m!"ROOT_DECL|{moduleName}|{name}|{kind}|{axioms}"

#check @CompleteGraph.conjecture545_false_positive
#check @CompleteGraph.hasQuadraticMarkovBasis
#print CompleteGraph.HasQuadraticMarkovBasis
#print CompleteGraph.graphRingMap
#print CompleteGraph.toricIdeal
