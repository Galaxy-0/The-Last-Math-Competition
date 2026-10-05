import Conjecture236
import Lean.Util.CollectAxioms

set_option maxRecDepth 10000
set_option maxHeartbeats 0

/- Executable inspection only; this file is outside the mathematical project. -/
run_cmd do
  let env ← Lean.getEnv
  -- Explicitly start from all public declarations written in the source, including unused bridges.
  let names := #[`Conjecture236.product_gap, `Conjecture236.spectral_moments,
    `Conjecture236.SignMatrix, `Conjecture236.integerMatrix, `Conjecture236.realMatrix,
    `Conjecture236.gram, `Conjecture236.gram_psd, `Conjecture236.gram_diag,
    `Conjecture236.gram_symmetric, `Conjecture236.gram_odd_integer,
    `Conjecture236.gram_entry_sq_lower, `Conjecture236.gram_trace,
    `Conjecture236.gram_square_trace_lower, `Conjecture236.sign_determinant_gap,
    `Conjecture236.IsSignMatrix, `Conjecture236.realMatrix_isSignMatrix,
    `Conjecture236.sign_encoding_complete, `Conjecture236.D, `Conjecture236.D_attained,
    `Conjecture236.determinant_le_D, `Conjecture236.D_isMaximum,
    `Conjecture236.IsHadamard, `Conjecture236.isHadamard_iff_rows,
    `Conjecture236.HadamardConjecture, `Conjecture236.normalizedMaximum,
    `Conjecture236.AllOrdersLimit, `Conjecture236.OriginalConjecture,
    `Conjecture236.allOrdersLimit_iff_positive_epsilon, `Conjecture236.normalization_pos,
    `Conjecture236.normalization_square, `Conjecture236.normalizedMaximum_odd_gap,
    `Conjecture236.not_AllOrdersLimit, `Conjecture236.conjecture236_false]
  let mut pending := names
  let mut visited : Lean.NameSet := {}
  let mut axioms : Lean.NameSet := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if !visited.contains name then
      visited := visited.insert name
      match env.checked.get.find? name with
      | none => throwError "Missing kernel declaration {name}"
      | some info =>
        if info.isUnsafe then throwError "Unsafe logical dependency: {name}"
        if info.isPartial then throwError "Partial logical dependency: {name}"
        match info with
        | .axiomInfo _ =>
          axioms := axioms.insert name
          unless #[`propext, `Classical.choice, `Quot.sound].contains name do
            throwError "Unapproved axiom: {name}"
        | _ => pure ()
        for dep in info.getUsedConstantsAsSet.toList do
          unless visited.contains dep do pending := pending.push dep
  Lean.logInfo m!"Source roots: {names.size}"
  Lean.logInfo m!"Transitive kernel declarations inspected: {visited.toList.length}"
  Lean.logInfo m!"Axioms: {axioms.toList}"
  Lean.logInfo "No unsafe or partial declaration occurs in this transitive logical closure."
  for name in names do
    let used ← Lean.collectAxioms name
    Lean.logInfo m!"{name}: {used}"
  for (name, info) in env.constants.toList do
    if name.toString.startsWith "Conjecture236." && (info.isUnsafe || info.isPartial) then
      if visited.contains name then throwError "Unexpected reached runtime artifact {name}"
      Lean.logInfo m!"Generated runtime artifact outside the logical closure: {name}; unsafe={info.isUnsafe}; partial={info.isPartial}"
