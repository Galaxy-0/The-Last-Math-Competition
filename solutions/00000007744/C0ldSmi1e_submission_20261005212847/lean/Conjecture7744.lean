import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Variance
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic

/-!
# Disproof of conjecture 00000007744

The uniform model is the uniform distribution on all labelled simple regular graphs.
The quadratic trace is deterministic. We compute its actual expectation and its
pushforward law, and use uniqueness in the topology of weak convergence to identify
any limiting law. No interchange of a variance and a limit is used.
-/

noncomputable section
open scoped Classical
open MeasureTheory ProbabilityTheory Filter

namespace Conjecture7744

variable (V : Type) [Fintype V]

/-- All labelled simple graphs on `V` that are regular of degree `d`. -/
def RegularGraph (d : ℕ) := {G : SimpleGraph V // G.IsRegularOfDegree d}

instance regularGraphFintype (d : ℕ) : Fintype (RegularGraph V d) := by
  unfold RegularGraph
  exact Fintype.ofFinite _
instance regularGraphMeasurableSpace (d : ℕ) : MeasurableSpace (RegularGraph V d) := ⊤

/-- The actual normalized quadratic trace of a deterministically rescaled adjacency
matrix. `a` rescales the matrix and `b` rescales the trace. In particular, the
empirical spectral normalization is `b = 1 / card V`. -/
def quadraticTrace (d : ℕ) (a b : ℝ) (G : RegularGraph V d) : ℝ :=
  b * Matrix.trace ((a • G.val.adjMatrix ℝ) ^ 2)

theorem quadraticTrace_eq (d : ℕ) (a b : ℝ) (G : RegularGraph V d) :
    quadraticTrace V d a b G = b * a ^ 2 * Fintype.card V * d := by
  have hdiag (v : V) : (G.val.adjMatrix ℝ ^ 2) v v = (d : ℝ) := by
    rw [pow_two, G.val.adjMatrix_mul_self_apply_self, G.property v]
  simp only [quadraticTrace, smul_pow, Matrix.trace_smul, smul_eq_mul,
    Matrix.trace, Matrix.diag, Matrix.smul_apply, smul_eq_mul, hdiag,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

variable (d : ℕ) [Nonempty (RegularGraph V d)]

/-- Uniform probability mass function on the entire finite regular graph space. -/
def uniformGraphs : PMF (RegularGraph V d) := PMF.uniformOfFintype _

theorem uniformGraphs_mass (G : RegularGraph V d) :
    uniformGraphs V d G = (Fintype.card (RegularGraph V d) : ENNReal)⁻¹ :=
  PMF.uniformOfFintype_apply G

/-- Expectation with respect to the actual uniform graph probability measure. -/
def quadraticExpectation (a b : ℝ) : ℝ :=
  ∫ G, quadraticTrace V d a b G ∂(uniformGraphs V d).toMeasure

theorem quadraticExpectation_eq (a b : ℝ) :
    quadraticExpectation V d a b = b * a ^ 2 * Fintype.card V * d := by
  simp [quadraticExpectation, quadraticTrace_eq]

/-- The x² coordinate of the centered trace process, with the stated sqrt(n) scale. -/
def quadraticFluctuation (a b : ℝ) (G : RegularGraph V d) : ℝ :=
  (quadraticTrace V d a b G - quadraticExpectation V d a b) *
    Real.sqrt (Fintype.card V)

theorem quadraticFluctuation_zero (a b : ℝ) (G : RegularGraph V d) :
    quadraticFluctuation V d a b G = 0 := by
  simp [quadraticFluctuation, quadraticTrace_eq, quadraticExpectation_eq]

theorem finite_quadratic_variance_zero (a b : ℝ) :
    variance (quadraticFluctuation V d a b) (uniformGraphs V d).toMeasure = 0 := by
  have hz : quadraticFluctuation V d a b = 0 := funext (quadraticFluctuation_zero V d a b)
  rw [hz, variance_zero]

/-- The probability law of the actual centered quadratic trace. -/
def quadraticLaw (a b : ℝ) : ProbabilityMeasure ℝ :=
  ⟨((uniformGraphs V d).map (quadraticFluctuation V d a b)).toMeasure, inferInstance⟩

/-- The point mass at zero, viewed as a probability measure. -/
def zeroLaw : ProbabilityMeasure ℝ := ⟨Measure.dirac 0, inferInstance⟩

theorem quadraticLaw_is_pushforward (a b : ℝ) :
    (quadraticLaw V d a b : Measure ℝ) =
      Measure.map (quadraticFluctuation V d a b) (uniformGraphs V d).toMeasure := by
  symm
  apply PMF.toMeasure_map
  have hz : quadraticFluctuation V d a b = fun _ => 0 :=
    funext (quadraticFluctuation_zero V d a b)
  rw [hz]
  exact measurable_const

theorem quadraticLaw_eq_zeroLaw (a b : ℝ) : quadraticLaw V d a b = zeroLaw := by
  apply Subtype.ext
  change ((uniformGraphs V d).map (quadraticFluctuation V d a b)).toMeasure = _
  have hz : quadraticFluctuation V d a b = Function.const _ 0 :=
    funext (quadraticFluctuation_zero V d a b)
  rw [hz, PMF.map_const, PMF.toMeasure_pure]
  rfl

/-- Normalized trace of an arbitrary real polynomial evaluated at the actual
scaled adjacency matrix. -/
def polynomialTrace (a b : ℝ) (p : Polynomial ℝ) (G : RegularGraph V d) : ℝ :=
  b * Matrix.trace (Polynomial.aeval (a • G.val.adjMatrix ℝ) p)

omit [Nonempty (RegularGraph V d)] in
theorem polynomialTrace_square (a b : ℝ) (G : RegularGraph V d) :
    polynomialTrace V d a b (Polynomial.X ^ 2) G = quadraticTrace V d a b G := by
  simp [polynomialTrace, quadraticTrace]

theorem polynomialTrace_integrable (a b : ℝ) (p : Polynomial ℝ) :
    Integrable (polynomialTrace V d a b p) (uniformGraphs V d).toMeasure := by
  exact Integrable.of_finite

/-- The expectation in the source's centered trace-polynomial definition. -/
def polynomialExpectation (a b : ℝ) (p : Polynomial ℝ) : ℝ :=
  ∫ G, polynomialTrace V d a b p G ∂(uniformGraphs V d).toMeasure

/-- The source's centered trace-polynomial coordinate, multiplied by sqrt(n). -/
def polynomialFluctuation (a b : ℝ) (p : Polynomial ℝ) (G : RegularGraph V d) : ℝ :=
  (polynomialTrace V d a b p G - polynomialExpectation V d a b p) *
    Real.sqrt (Fintype.card V)

theorem polynomialFluctuation_square (a b : ℝ) (G : RegularGraph V d) :
    polynomialFluctuation V d a b (Polynomial.X ^ 2) G =
      quadraticFluctuation V d a b G := by
  simp only [polynomialFluctuation, polynomialExpectation, polynomialTrace_square,
    quadraticFluctuation, quadraticExpectation]

/-- The actual law of each centered trace-polynomial coordinate. -/
def polynomialLaw (a b : ℝ) (p : Polynomial ℝ) : ProbabilityMeasure ℝ :=
  ⟨((uniformGraphs V d).map (polynomialFluctuation V d a b p)).toMeasure, inferInstance⟩

theorem polynomialLaw_is_pushforward (a b : ℝ) (p : Polynomial ℝ) :
    (polynomialLaw V d a b p : Measure ℝ) =
      Measure.map (polynomialFluctuation V d a b p) (uniformGraphs V d).toMeasure := by
  symm
  exact PMF.toMeasure_map _ _ (measurable_of_countable _)

theorem polynomialLaw_square (a b : ℝ) :
    polynomialLaw V d a b (Polynomial.X ^ 2) = quadraticLaw V d a b := by
  apply Subtype.ext
  have hf : polynomialFluctuation V d a b (Polynomial.X ^ 2) =
      quadraticFluctuation V d a b := funext (polynomialFluctuation_square V d a b)
  change ((uniformGraphs V d).map _).toMeasure = ((uniformGraphs V d).map _).toMeasure
  rw [hf]

/-- The finite-dimensional centered trace process for a list of polynomials. -/
def jointFluctuation (a b : ℝ) {m : ℕ} (p : Fin m → Polynomial ℝ)
    (G : RegularGraph V d) : Fin m → ℝ :=
  fun i => polynomialFluctuation V d a b (p i) G

/-- Actual finite-dimensional distributions of the uniform graph trace process. -/
def jointLaw (a b : ℝ) {m : ℕ} (p : Fin m → Polynomial ℝ) :
    ProbabilityMeasure (Fin m → ℝ) :=
  ⟨((uniformGraphs V d).map (jointFluctuation V d a b p)).toMeasure, inferInstance⟩

theorem jointLaw_is_pushforward (a b : ℝ) {m : ℕ} (p : Fin m → Polynomial ℝ) :
    (jointLaw V d a b p : Measure (Fin m → ℝ)) =
      Measure.map (jointFluctuation V d a b p) (uniformGraphs V d).toMeasure := by
  symm
  exact PMF.toMeasure_map _ _ (measurable_of_countable _)

/-- The marginal law obtained by projecting to one coordinate. -/
def coordinateLaw {m : ℕ} (ν : ProbabilityMeasure (Fin m → ℝ)) (i : Fin m) :
    ProbabilityMeasure ℝ := ν.map (measurable_pi_apply i).aemeasurable

theorem jointLaw_coordinate (a b : ℝ) {m : ℕ} (p : Fin m → Polynomial ℝ) (i : Fin m) :
    coordinateLaw (jointLaw V d a b p) i = polynomialLaw V d a b (p i) := by
  apply Subtype.ext
  change Measure.map (fun x : Fin m → ℝ => x i)
    ((uniformGraphs V d).map (jointFluctuation V d a b p)).toMeasure = _
  rw [PMF.toMeasure_map _ _ (measurable_pi_apply i), PMF.map_comp]
  rfl

/-- Weak convergence of a vector law implies weak convergence of each marginal. -/
theorem coordinateLaw_tendsto {m : ℕ} (νs : ℕ → ProbabilityMeasure (Fin m → ℝ))
    (ν : ProbabilityMeasure (Fin m → ℝ)) (i : Fin m)
    (h : Tendsto νs atTop (nhds ν)) :
    Tendsto (fun k => coordinateLaw (νs k) i) atTop (nhds (coordinateLaw ν i)) := by
  exact ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous νs ν h (continuous_apply i)

/-- A concrete unbounded family of vertex sets. -/
def BlockVertices (d k : ℕ) := Fin (k + 1) × Fin (d + 1)

instance blockVerticesFintype (d k : ℕ) : Fintype (BlockVertices d k) :=
  inferInstanceAs (Fintype (Fin (k + 1) × Fin (d + 1)))

/-- Disjoint copies of the complete graph on `d+1` vertices. These witness that
there are regular graphs for arbitrarily large admissible model sizes. -/
def blockGraph (d k : ℕ) : SimpleGraph (BlockVertices d k) where
  Adj v w := v.1 = w.1 ∧ v.2 ≠ w.2
  symm := fun _ _ h => ⟨h.1.symm, h.2.symm⟩
  loopless := fun _ h => h.2 rfl

theorem blockGraph_regular (d k : ℕ) : (blockGraph d k).IsRegularOfDegree d := by
  intro v
  have hn : (blockGraph d k).neighborFinset v =
      ({v.1} : Finset (Fin (k + 1))) ×ˢ (Finset.univ.erase v.2) := by
    apply Finset.ext
    intro w
    rw [SimpleGraph.mem_neighborFinset, Finset.mem_product]
    change (v.1 = w.1 ∧ v.2 ≠ w.2) ↔ _
    simp only [Finset.mem_singleton, Finset.mem_erase, Finset.mem_univ, and_true]
    exact ⟨fun h => ⟨h.1.symm, h.2.symm⟩, fun h => ⟨h.1.symm, h.2.symm⟩⟩
  rw [SimpleGraph.degree, hn, Finset.card_product]
  simp

instance blockRegularGraphsNonempty (d k : ℕ) :
    Nonempty (RegularGraph (BlockVertices d k) d) :=
  ⟨⟨blockGraph d k, blockGraph_regular d k⟩⟩

theorem blockVertices_card (d k : ℕ) :
    Fintype.card (BlockVertices d k) = (k + 1) * (d + 1) := by
  simp [BlockVertices]

theorem blockVertices_card_pos (d k : ℕ) : 0 < Fintype.card (BlockVertices d k) := by
  rw [blockVertices_card]
  positivity

theorem blockVertices_card_tendsto (d : ℕ) :
    Tendsto (fun k => Fintype.card (BlockVertices d k)) atTop atTop := by
  apply tendsto_atTop_mono (fun k => ?_) tendsto_id
  rw [blockVertices_card]
  change k ≤ (k + 1) * (d + 1)
  nlinarith

/-- The variance of a probability law is the variance of its identity random variable. -/
def lawVariance (ν : ProbabilityMeasure ℝ) : ℝ := variance id (ν : Measure ℝ)

theorem zeroLaw_variance : lawVariance zeroLaw = 0 := by
  simp [lawVariance, zeroLaw, variance, evariance]

/-- The quadratic fluctuation laws converge weakly to the point mass at zero.
The scale and trace normalization can vary freely with the number of vertices. -/
theorem quadraticLaws_tendsto_zero (d : ℕ) (a b : ℕ → ℝ) :
    Tendsto (fun k => quadraticLaw (BlockVertices d k) d (a k) (b k))
      atTop (nhds zeroLaw) := by
  simp only [quadraticLaw_eq_zeroLaw]
  exact tendsto_const_nhds

/-- Any weak limit of the actual quadratic coordinate has variance zero. -/
theorem quadratic_weak_limit_variance (d : ℕ) (a b : ℕ → ℝ)
    (ν : ProbabilityMeasure ℝ)
    (h : Tendsto (fun k => quadraticLaw (BlockVertices d k) d (a k) (b k))
      atTop (nhds ν)) : lawVariance ν = 0 := by
  have heq : ν = zeroLaw := tendsto_nhds_unique h (quadraticLaws_tendsto_zero d a b)
  rw [heq, zeroLaw_variance]

/-- The source's prescribed variance for the x² coordinate. -/
def claimedVariance (d : ℕ) : ℝ := 4 - 12 / d + 8 / (d : ℝ) ^ 2

theorem claimedVariance_three : claimedVariance 3 = 8 / 9 := by
  norm_num [claimedVariance]

/-- At degree three no weak limit of the actual coordinate can have the source's
prescribed variance. This refutes the necessary x² marginal of the joint claim. -/
theorem no_claimed_quadratic_limit (a b : ℕ → ℝ) :
    ¬ ∃ ν : ProbabilityMeasure ℝ,
      Tendsto (fun k => quadraticLaw (BlockVertices 3 k) 3 (a k) (b k))
        atTop (nhds ν) ∧ lawVariance ν = claimedVariance 3 := by
  rintro ⟨ν, hlim, hvar⟩
  have hz := quadratic_weak_limit_variance 3 a b ν hlim
  rw [claimedVariance_three] at hvar
  linarith

/-- A necessary part of the source conjecture: all finite-dimensional trace laws
have weak limits, and the x² marginal has the stated variance. Gaussianity and the
other covariance prescriptions are additional requirements; disproving this
necessary part therefore disproves the original conjunction. -/
def RequiredSecondOrderLimit (d : ℕ) (a b : ℕ → ℝ) : Prop :=
  ∃ limits : (m : ℕ) → (Fin m → Polynomial ℝ) → ProbabilityMeasure (Fin m → ℝ),
    (∀ m p, Tendsto (fun k => jointLaw (BlockVertices d k) d (a k) (b k) p)
      atTop (nhds (limits m p))) ∧
    lawVariance (coordinateLaw (limits 1 (fun _ => Polynomial.X ^ 2)) 0) = claimedVariance d

/-- The finite-dimensional limit assertion fails at degree three for every
choice of deterministic adjacency scaling and trace normalization. -/
theorem no_required_second_order_limit (a b : ℕ → ℝ) :
    ¬ RequiredSecondOrderLimit 3 a b := by
  rintro ⟨limits, hlim, hvar⟩
  let p : Fin 1 → Polynomial ℝ := fun _ => Polynomial.X ^ 2
  have hcoord := coordinateLaw_tendsto
    (fun k => jointLaw (BlockVertices 3 k) 3 (a k) (b k) p)
    (limits 1 p) 0 (hlim 1 p)
  simp only [jointLaw_coordinate, p, polynomialLaw_square] at hcoord
  exact no_claimed_quadratic_limit a b ⟨coordinateLaw (limits 1 p) 0, hcoord, hvar⟩

/-- In particular, the source conjecture fails with ordinary adjacency matrices
and the empirical normalized trace `tr / n`, on nonempty cubic uniform models
whose vertex counts tend to infinity. -/
theorem conjecture7744_false :
    ¬ RequiredSecondOrderLimit 3 (fun _ => 1)
      (fun k => 1 / (Fintype.card (BlockVertices 3 k) : ℝ)) :=
  no_required_second_order_limit _ _

end Conjecture7744
