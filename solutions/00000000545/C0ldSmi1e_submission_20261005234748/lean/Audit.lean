import Check
import Lean.Util.CollectAxioms

open Lean Elab Command

/- Inventory every declaration, including generated and private declarations,
whose defining module is one of the authored mathematical modules. -/
run_cmd do
  let env ← getEnv
  let modules := #[`Connectivity, `IdealBridge, `Conjecture545, `Check]
  let mut total := 0
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let moduleName := env.header.moduleNames[idx.toNat]!
      if modules.contains moduleName then
        let axioms ← Lean.collectAxioms name
        logInfo m!"DECL {moduleName} {name} AXIOMS {axioms}"
        total := total + 1
  logInfo m!"AUTHORED_DECLARATION_TOTAL {total}"

#print axioms CompleteGraph.conjecture545_false
#print axioms CompleteGraph.conjecture545_false_positive
#print axioms CompleteGraph.counterexample_six
#print axioms CompleteGraph.hasQuadraticMarkovBasis
#print axioms CompleteGraph.toricIdeal_eq_span_quadraticBinomials
#print axioms CompleteGraph.connected_of_degree_eq
