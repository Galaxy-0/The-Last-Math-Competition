import Conjecture236

open scoped BigOperators ComplexOrder
open Matrix

set_option pp.all true
set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true

-- Every named source declaration: full actual type and transitive axioms.
#check @Conjecture236.product_gap
#print axioms Conjecture236.product_gap
#check @Conjecture236.spectral_moments
#print axioms Conjecture236.spectral_moments
#check @Conjecture236.SignMatrix
#print axioms Conjecture236.SignMatrix
#check @Conjecture236.integerMatrix
#print axioms Conjecture236.integerMatrix
#check @Conjecture236.realMatrix
#print axioms Conjecture236.realMatrix
#check @Conjecture236.gram
#print axioms Conjecture236.gram
#check @Conjecture236.gram_psd
#print axioms Conjecture236.gram_psd
#check @Conjecture236.gram_diag
#print axioms Conjecture236.gram_diag
#check @Conjecture236.gram_symmetric
#print axioms Conjecture236.gram_symmetric
#check @Conjecture236.gram_odd_integer
#print axioms Conjecture236.gram_odd_integer
#check @Conjecture236.gram_entry_sq_lower
#print axioms Conjecture236.gram_entry_sq_lower
#check @Conjecture236.gram_trace
#print axioms Conjecture236.gram_trace
#check @Conjecture236.gram_square_trace_lower
#print axioms Conjecture236.gram_square_trace_lower
#check @Conjecture236.sign_determinant_gap
#print axioms Conjecture236.sign_determinant_gap
#check @Conjecture236.IsSignMatrix
#print axioms Conjecture236.IsSignMatrix
#check @Conjecture236.realMatrix_isSignMatrix
#print axioms Conjecture236.realMatrix_isSignMatrix
#check @Conjecture236.sign_encoding_complete
#print axioms Conjecture236.sign_encoding_complete
#check @Conjecture236.D
#print axioms Conjecture236.D
#check @Conjecture236.D_attained
#print axioms Conjecture236.D_attained
#check @Conjecture236.determinant_le_D
#print axioms Conjecture236.determinant_le_D
#check @Conjecture236.D_isMaximum
#print axioms Conjecture236.D_isMaximum
#check @Conjecture236.IsHadamard
#print axioms Conjecture236.IsHadamard
#check @Conjecture236.isHadamard_iff_rows
#print axioms Conjecture236.isHadamard_iff_rows
#check @Conjecture236.HadamardConjecture
#print axioms Conjecture236.HadamardConjecture
#check @Conjecture236.normalizedMaximum
#print axioms Conjecture236.normalizedMaximum
#check @Conjecture236.AllOrdersLimit
#print axioms Conjecture236.AllOrdersLimit
#check @Conjecture236.OriginalConjecture
#print axioms Conjecture236.OriginalConjecture
#check @Conjecture236.allOrdersLimit_iff_positive_epsilon
#print axioms Conjecture236.allOrdersLimit_iff_positive_epsilon
#check @Conjecture236.normalization_pos
#print axioms Conjecture236.normalization_pos
#check @Conjecture236.normalization_square
#print axioms Conjecture236.normalization_square
#check @Conjecture236.normalizedMaximum_odd_gap
#print axioms Conjecture236.normalizedMaximum_odd_gap
#check @Conjecture236.not_AllOrdersLimit
#print axioms Conjecture236.not_AllOrdersLimit
#check @Conjecture236.conjecture236_false
#print axioms Conjecture236.conjecture236_false

-- Bodies of every source definition.
#print Conjecture236.SignMatrix
#print Conjecture236.integerMatrix
#print Conjecture236.realMatrix
#print Conjecture236.gram
#print Conjecture236.IsSignMatrix
#print Conjecture236.D
#print Conjecture236.IsHadamard
#print Conjecture236.HadamardConjecture
#print Conjecture236.normalizedMaximum
#print Conjecture236.AllOrdersLimit
#print Conjecture236.OriginalConjecture

-- Names include any generated constants in the source namespace.
run_cmd do
  let env ← Lean.getEnv
  for (name, info) in env.constants.toList do
    if name.toString.startsWith "Conjecture236." ||
        name.toString.startsWith "_private.Conjecture236." then
      Lean.logInfo m!"SOURCE CONSTANT {name}: {info.type}"

-- Actual standard operations and their defining bodies.
#print Matrix
#print Matrix.transpose
#print Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
#print Matrix.det
#print Matrix.trace
#print Matrix.IsHermitian
#print Matrix.PosSemidef
#print Matrix.IsHermitian.eigenvalues
#print Real.sqrt
#print Real.rpow
#print Real.exp
#print Finset.sup'
#print Filter.Tendsto
#print Filter.atTop
#print nhds

-- Resolved standard instances used in the formalization.
#synth RCLike ℝ
#synth StarOrderedRing ℝ
#synth LinearOrder ℝ
#synth HPow ℝ ℝ ℝ
#synth HPow ℝ ℕ ℝ
#check @abs
#print abs
#synth TopologicalSpace ℝ
#synth MetricSpace ℝ
#synth OrderTopology ℝ
#synth Fintype (Conjecture236.SignMatrix 5)
#synth Nonempty (Conjecture236.SignMatrix 0)
#synth HMul (Matrix (Fin 5) (Fin 5) ℝ) (Matrix (Fin 5) (Fin 5) ℝ) (Matrix (Fin 5) (Fin 5) ℝ)
#synth SMul ℝ (Matrix (Fin 5) (Fin 5) ℝ)

-- The standard choice/decidability constants are explicit.
#check @Classical.choice
#check @Classical.propDecidable
#check @Quot.sound
#check @propext

#print Real.instPow
#check @RCLike.toStarOrderedRing
