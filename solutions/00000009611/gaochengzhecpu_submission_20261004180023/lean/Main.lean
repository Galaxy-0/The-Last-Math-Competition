import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.IntermediateValue

/-! Two Perron numbers of algebraic degree three whose minimal realising matrices have
different sizes: the real root of `X^3 - X - 1` is the Perron eigenvalue of a primitive
`3 × 3` matrix, while the real root of `X^3 + X^2 - 3X - 4` in `[3/2, 2]` is the Perron
eigenvalue of a primitive `4 × 4` matrix and of no nonnegative integer matrix of size at most
three. Hence the minimal size is not a function of the algebraic degree. -/
namespace Conjecture9611

open Matrix Polynomial

/-! ### Nonnegative integer matrices, primitivity and Perron eigenvalues -/

section Defs

variable {n : ℕ}

/-- The real matrix with the same entries as a nonnegative integer matrix. -/
def realMat (A : Matrix (Fin n) (Fin n) ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  A.map (Nat.cast : ℕ → ℝ)

/-- A nonnegative integer matrix is primitive if some positive power has all entries positive.
The subshift of finite type defined by `A` is mixing exactly when `A` is primitive. -/
def IsPrimitive (A : Matrix (Fin n) (Fin n) ℕ) : Prop :=
  ∃ k : ℕ, 0 < k ∧ ∀ i j, 0 < (A ^ k) i j

/-- `lam` is an eigenvalue of `A` with an entrywise positive eigenvector. For a primitive
matrix this is the Perron eigenvalue; see `norm_le_of_isPerronEigenvalue`,
`pathCount_bounds` and `hasEntropy_log`. -/
def IsPerronEigenvalue (A : Matrix (Fin n) (Fin n) ℕ) (lam : ℝ) : Prop :=
  ∃ v : Fin n → ℝ, (∀ i, 0 < v i) ∧ realMat A *ᵥ v = lam • v

/-- `lam` is a real eigenvalue of `A` (with any nonzero real eigenvector). -/
def IsEigenvalue (A : Matrix (Fin n) (Fin n) ℕ) (lam : ℝ) : Prop :=
  ∃ v : Fin n → ℝ, v ≠ 0 ∧ realMat A *ᵥ v = lam • v

theorem IsPerronEigenvalue.isEigenvalue {A : Matrix (Fin n) (Fin n) ℕ} {lam : ℝ}
    (hn : 0 < n) (h : IsPerronEigenvalue A lam) : IsEigenvalue A lam := by
  obtain ⟨v, hv, hAv⟩ := h
  refine ⟨v, fun h0 => ?_, hAv⟩
  have := hv ⟨0, hn⟩
  rw [h0] at this
  exact lt_irrefl _ this

end Defs

/-- `lam` is realised in size `n`: it is the Perron eigenvalue of a primitive nonnegative
integer `n × n` matrix, `n ≥ 1`; that is, `log lam` is the entropy of a mixing subshift of
finite type presented by a matrix of size `n`. -/
def Realizable (lam : ℝ) (n : ℕ) : Prop :=
  0 < n ∧ ∃ A : Matrix (Fin n) (Fin n) ℕ, IsPrimitive A ∧ IsPerronEigenvalue A lam

/-- `m` is the minimal size of a matrix realising `lam`. -/
def IsMinSize (lam : ℝ) (m : ℕ) : Prop :=
  Realizable lam m ∧ ∀ k, k < m → ¬ Realizable lam k

theorem IsMinSize.unique {lam : ℝ} {m m' : ℕ} (h : IsMinSize lam m) (h' : IsMinSize lam m') :
    m = m' := by
  rcases lt_trichotomy m m' with hlt | heq | hgt
  · exact absurd h.1 (h'.2 m hlt)
  · exact heq
  · exact absurd h'.1 (h.2 m' hgt)

/-- The algebraic degree of a real number: the degree of its minimal polynomial over `ℚ`. -/
noncomputable def algDegree (lam : ℝ) : ℕ := (minpoly ℚ lam).natDegree

/-- A Perron number: a real algebraic integer `lam ≥ 1` such that every other complex root of
its minimal polynomial has modulus strictly smaller than `lam`. -/
def IsPerronNumber (lam : ℝ) : Prop :=
  IsIntegral ℤ lam ∧ 1 ≤ lam ∧
    ∀ mu : ℂ, aeval mu (minpoly ℚ lam) = 0 → mu ≠ (lam : ℂ) → ‖mu‖ < lam

/-- The first clause of the conjecture, quantified over Perron numbers: the minimal size of
a matrix realising a Perron number is a function of its algebraic degree. -/
def ClaimedDegreeLaw : Prop :=
  ∃ f : ℕ → ℕ, ∀ lam : ℝ, IsPerronNumber lam → IsMinSize lam (f (algDegree lam))

/-- The same clause, quantified over the numbers that are realised by some primitive matrix.
By Lind's theorem these are exactly the Perron numbers. -/
def ClaimedDegreeLawRealized : Prop :=
  ∃ f : ℕ → ℕ, ∀ lam : ℝ, (∃ n, Realizable lam n) → IsMinSize lam (f (algDegree lam))

/-- Adjacent coefficients never have the same strict sign. A polynomial whose coefficients
alternate in sign, strictly or with zero coefficients allowed, has this property. -/
def WeaklySignAlternating (p : ℚ[X]) : Prop :=
  ∀ k, k < p.natDegree → p.coeff k * p.coeff (k + 1) ≤ 0

/-- The second clause, read for each Perron number separately: the minimal size equals the
algebraic degree exactly when the minimal polynomial is sign-alternating. -/
def ClaimedSignCriterion : Prop :=
  ∀ lam : ℝ, IsPerronNumber lam →
    (IsMinSize lam (algDegree lam) ↔ WeaklySignAlternating (minpoly ℚ lam))

/-! ### Eigenvalues are roots of the characteristic polynomial -/

section Charpoly

variable {n : ℕ}

theorem eval_charpoly_eq_zero {M : Matrix (Fin n) (Fin n) ℝ} {lam : ℝ} {v : Fin n → ℝ}
    (hv : v ≠ 0) (hMv : M *ᵥ v = lam • v) : M.charpoly.eval lam = 0 := by
  rw [Matrix.charpoly, Matrix.eval_det, Matrix.matPolyEquiv_charmatrix, eval_sub, eval_X, eval_C]
  by_contra hdet
  have hu : IsUnit (scalar (Fin n) lam - M).det := isUnit_iff_ne_zero.mpr hdet
  have h0 : (scalar (Fin n) lam - M) *ᵥ v = 0 := by
    rw [Matrix.sub_mulVec, hMv]
    have : scalar (Fin n) lam *ᵥ v = lam • v := by
      ext i
      simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
    rw [this, sub_self]
  apply hv
  have h1 : (scalar (Fin n) lam - M)⁻¹ *ᵥ ((scalar (Fin n) lam - M) *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  rw [← h1, h0, Matrix.mulVec_zero]

theorem ratMat_map (A : Matrix (Fin n) (Fin n) ℕ) :
    (A.map (Nat.cast : ℕ → ℚ)).map (algebraMap ℚ ℝ) = realMat A := by
  ext i j
  simp [realMat]

/-- The minimal polynomial of a real eigenvalue divides the characteristic polynomial. -/
theorem minpoly_dvd_charpoly {A : Matrix (Fin n) (Fin n) ℕ} {lam : ℝ}
    (h : IsEigenvalue A lam) : minpoly ℚ lam ∣ (A.map (Nat.cast : ℕ → ℚ)).charpoly := by
  obtain ⟨v, hv, hAv⟩ := h
  apply minpoly.dvd
  rw [aeval_def, eval₂_eq_eval_map, ← Matrix.charpoly_map, ratMat_map]
  exact eval_charpoly_eq_zero hv hAv

/-- A real eigenvalue of an `n × n` integer matrix has algebraic degree at most `n`. -/
theorem algDegree_le {A : Matrix (Fin n) (Fin n) ℕ} {lam : ℝ} (h : IsEigenvalue A lam) :
    algDegree lam ≤ n := by
  have hdvd := minpoly_dvd_charpoly h
  have hne : (A.map (Nat.cast : ℕ → ℚ)).charpoly ≠ 0 := (Matrix.charpoly_monic _).ne_zero
  have := natDegree_le_of_dvd hdvd hne
  rwa [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at this

theorem not_realizable_of_lt {lam : ℝ} {k : ℕ} (hk : k < algDegree lam) :
    ¬ Realizable lam k := by
  rintro ⟨hpos, A, -, hA⟩
  have := algDegree_le (hA.isEigenvalue hpos)
  omega

end Charpoly

/-! ### A positive eigenvector identifies the spectral radius and the growth rate -/

section Perron

variable {n : ℕ}

/-- If `A` has a positive eigenvector for `lam`, every complex eigenvalue of `A` has modulus
at most `lam`. So `lam` is the spectral radius of `A`. -/
theorem norm_le_of_isPerronEigenvalue {A : Matrix (Fin n) (Fin n) ℕ} {lam : ℝ}
    (h : IsPerronEigenvalue A lam) (mu : ℂ) (w : Fin n → ℂ) (hw : w ≠ 0)
    (hAw : A.map (Nat.cast : ℕ → ℂ) *ᵥ w = mu • w) : ‖mu‖ ≤ lam := by
  obtain ⟨v, hv, hAv⟩ := h
  obtain ⟨j0, hj0⟩ : ∃ j, w j ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hw (funext hcon)
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun j => ‖w j‖ / v j)
    ⟨j0, Finset.mem_univ j0⟩
  have hcpos : 0 < ‖w i‖ / v i :=
    lt_of_lt_of_le (div_pos (norm_pos_iff.mpr hj0) (hv j0)) (hi j0 (Finset.mem_univ j0))
  have hwi : 0 < ‖w i‖ := by
    by_contra hcon
    have h0 : ‖w i‖ = 0 := le_antisymm (not_lt.mp hcon) (norm_nonneg _)
    rw [h0, zero_div] at hcpos
    exact lt_irrefl _ hcpos
  have hbound : ∀ j, ‖w j‖ ≤ ‖w i‖ / v i * v j := fun j =>
    (div_le_iff₀ (hv j)).mp (hi j (Finset.mem_univ j))
  have hrow : (realMat A *ᵥ v) i = lam * v i := by rw [hAv]; rfl
  have hsum : ∑ j, (A i j : ℝ) * v j = lam * v i := by
    rw [← hrow]; rfl
  have hmu : mu * w i = ∑ j, (A i j : ℂ) * w j := by
    have := congrFun hAw i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul] at this
    exact this.symm
  have h1 : ‖mu‖ * ‖w i‖ ≤ lam * ‖w i‖ := by
    calc ‖mu‖ * ‖w i‖ = ‖mu * w i‖ := (norm_mul _ _).symm
      _ = ‖∑ j, (A i j : ℂ) * w j‖ := by rw [hmu]
      _ ≤ ∑ j, ‖(A i j : ℂ) * w j‖ := norm_sum_le _ _
      _ = ∑ j, (A i j : ℝ) * ‖w j‖ := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [norm_mul, Complex.norm_natCast]
      _ ≤ ∑ j, (A i j : ℝ) * (‖w i‖ / v i * v j) :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hbound j) (Nat.cast_nonneg _)
      _ = ‖w i‖ / v i * ∑ j, (A i j : ℝ) * v j := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
      _ = ‖w i‖ / v i * (lam * v i) := by rw [hsum]
      _ = lam * ‖w i‖ := by
          have := (hv i).ne'
          field_simp
          ring
  exact le_of_mul_le_mul_right h1 hwi

theorem realMat_pow (A : Matrix (Fin n) (Fin n) ℕ) (k : ℕ) :
    realMat (A ^ k) = realMat A ^ k := by
  have := map_pow (Nat.castRingHom ℝ).mapMatrix A k
  simpa [realMat, RingHom.mapMatrix_apply] using this

theorem pow_mulVec_eigen {M : Matrix (Fin n) (Fin n) ℝ} {lam : ℝ} {v : Fin n → ℝ}
    (hMv : M *ᵥ v = lam • v) (k : ℕ) : (M ^ k) *ᵥ v = lam ^ k • v := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, hMv, Matrix.mulVec_smul, ih, smul_smul, pow_succ,
      mul_comm]

/-- The number of paths of length `k` in the graph of `A`, that is the number of allowed words
of the subshift with `k` transitions. -/
def pathCount (A : Matrix (Fin n) (Fin n) ℕ) (k : ℕ) : ℕ := ∑ i, ∑ j, (A ^ k) i j

/-- With a positive eigenvector for `lam`, the number of paths of length `k` lies between two
positive constant multiples of `lam ^ k`. Consequently the entropy, the exponential growth
rate of the number of allowed words, equals `log lam`. -/
theorem pathCount_bounds {A : Matrix (Fin n) (Fin n) ℕ} {lam : ℝ} (hn : 0 < n)
    (h : IsPerronEigenvalue A lam) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ k : ℕ, c * lam ^ k ≤ (pathCount A k : ℝ) ∧ (pathCount A k : ℝ) ≤ C * lam ^ k := by
  obtain ⟨v, hv, hAv⟩ := h
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  obtain ⟨a, -, ha⟩ := Finset.exists_min_image Finset.univ v hne
  obtain ⟨b, -, hb⟩ := Finset.exists_max_image Finset.univ v hne
  have hS : 0 < ∑ i, v i := Finset.sum_pos (fun i _ => hv i) hne
  refine ⟨(∑ i, v i) / v b, (∑ i, v i) / v a, div_pos hS (hv b), div_pos hS (hv a), fun k => ?_⟩
  have hk : ∑ i, ∑ j, ((A ^ k) i j : ℝ) * v j = lam ^ k * ∑ i, v i := by
    have h1 := pow_mulVec_eigen hAv k
    rw [← realMat_pow] at h1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h2 := congrFun h1 i
    simpa [Matrix.mulVec, dotProduct, realMat] using h2
  have hcast : (pathCount A k : ℝ) = ∑ i, ∑ j, ((A ^ k) i j : ℝ) := by
    simp [pathCount]
  constructor
  · rw [div_mul_eq_mul_div, div_le_iff₀ (hv b), hcast, mul_comm (∑ i, v i), ← hk,
      Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (hb j (Finset.mem_univ j)) (Nat.cast_nonneg _)
  · rw [div_mul_eq_mul_div, le_div_iff₀ (hv a), hcast, mul_comm (∑ i, v i), ← hk,
      Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (ha j (Finset.mem_univ j)) (Nat.cast_nonneg _)

/-- `h` is the topological entropy of the subshift of finite type presented by `A`: the
exponential growth rate of the number of allowed words. -/
def HasEntropy (A : Matrix (Fin n) (Fin n) ℕ) (h : ℝ) : Prop :=
  Filter.Tendsto (fun k : ℕ => Real.log (pathCount A k) / k) Filter.atTop (nhds h)

/-- The Perron eigenvalue of a primitive matrix is positive. -/
theorem perron_pos {A : Matrix (Fin n) (Fin n) ℕ} {lam : ℝ} (hn : 0 < n)
    (hprim : IsPrimitive A) (h : IsPerronEigenvalue A lam) : 0 < lam := by
  obtain ⟨v, hv, hAv⟩ := h
  obtain ⟨k, hk, hpos⟩ := hprim
  have hnonneg : 0 ≤ lam := by
    have h1 := congrFun hAv ⟨0, hn⟩
    have h2 : 0 ≤ (realMat A *ᵥ v) ⟨0, hn⟩ := by
      simp only [Matrix.mulVec, dotProduct, realMat, Matrix.map_apply]
      exact Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (hv j).le
    rw [h1] at h2
    have h3 : 0 ≤ lam * v ⟨0, hn⟩ := h2
    exact nonneg_of_mul_nonneg_left h3 (hv _)
  have hne : lam ≠ 0 := by
    rintro rfl
    have h1 := pow_mulVec_eigen hAv k
    rw [← realMat_pow] at h1
    have h2 := congrFun h1 ⟨0, hn⟩
    have h3 : 0 < (realMat (A ^ k) *ᵥ v) ⟨0, hn⟩ := by
      simp only [Matrix.mulVec, dotProduct, realMat, Matrix.map_apply]
      exact Finset.sum_pos (fun j _ => mul_pos (Nat.cast_pos.mpr (hpos _ j)) (hv j))
        ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    rw [h2] at h3
    simp [zero_pow hk.ne'] at h3
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

/-- The entropy of the subshift presented by a primitive matrix is the logarithm of its
Perron eigenvalue. -/
theorem hasEntropy_log {A : Matrix (Fin n) (Fin n) ℕ} {lam : ℝ} (hn : 0 < n)
    (hprim : IsPrimitive A) (h : IsPerronEigenvalue A lam) : HasEntropy A (Real.log lam) := by
  have hlam := perron_pos hn hprim h
  obtain ⟨c, C, hc, hC, hb⟩ := pathCount_bounds hn h
  have hlow : Filter.Tendsto (fun k : ℕ => Real.log c / k + Real.log lam) Filter.atTop
      (nhds (Real.log lam)) := by
    have := (tendsto_const_div_atTop_nhds_zero_nat (Real.log c)).add
      (tendsto_const_nhds (x := Real.log lam))
    simpa using this
  have hup : Filter.Tendsto (fun k : ℕ => Real.log C / k + Real.log lam) Filter.atTop
      (nhds (Real.log lam)) := by
    have := (tendsto_const_div_atTop_nhds_zero_nat (Real.log C)).add
      (tendsto_const_nhds (x := Real.log lam))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop 1] with k hk
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
    have h1 : Real.log (c * lam ^ k) ≤ Real.log (pathCount A k) :=
      Real.log_le_log (mul_pos hc (pow_pos hlam k)) (hb k).1
    rw [Real.log_mul hc.ne' (pow_pos hlam k).ne', Real.log_pow] at h1
    rw [le_div_iff₀ hkpos]
    have h2 : (Real.log c / k + Real.log lam) * k = Real.log c + k * Real.log lam := by
      field_simp
      ring
    rw [h2]
    exact h1
  · filter_upwards [Filter.eventually_ge_atTop 1] with k hk
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
    have hNpos : (0 : ℝ) < pathCount A k :=
      lt_of_lt_of_le (mul_pos hc (pow_pos hlam k)) (hb k).1
    have h1 : Real.log (pathCount A k) ≤ Real.log (C * lam ^ k) :=
      Real.log_le_log hNpos (hb k).2
    rw [Real.log_mul hC.ne' (pow_pos hlam k).ne', Real.log_pow] at h1
    rw [div_le_iff₀ hkpos]
    have h2 : (Real.log C / k + Real.log lam) * k = Real.log C + k * Real.log lam := by
      field_simp
      ring
    rw [h2]
    exact h1

end Perron

/-! ### Monic cubics over `ℚ` without rational roots are irreducible -/

/-- A rational root of a monic cubic with integer coefficients is an integer. -/
theorem int_of_rat_root (a b c : ℤ) (r : ℚ) (h : r ^ 3 + a * r ^ 2 + b * r + c = 0) :
    ∃ z : ℤ, (z : ℚ) = r := by
  have hden0 : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  have key : (r.num : ℚ) = r * r.den := by
    rw [← div_eq_iff hden0]
    exact Rat.num_div_den r
  have h1 : (r.num : ℚ) ^ 3 + a * (r.num : ℚ) ^ 2 * r.den + b * (r.num : ℚ) * (r.den : ℚ) ^ 2
      + c * (r.den : ℚ) ^ 3 = 0 := by
    rw [key]
    linear_combination (r.den : ℚ) ^ 3 * h
  have h2 : r.num ^ 3 + a * r.num ^ 2 * (r.den : ℤ) + b * r.num * (r.den : ℤ) ^ 2
      + c * (r.den : ℤ) ^ 3 = 0 := by exact_mod_cast h1
  have hdvd : (r.den : ℤ) ∣ r.num ^ 3 :=
    ⟨-(a * r.num ^ 2 + b * r.num * r.den + c * (r.den : ℤ) ^ 2), by linear_combination h2⟩
  have hcop : IsCoprime r.num (r.den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd] using r.reduced
  have hunit : IsUnit (r.den : ℤ) := (hcop.pow_left (m := 3)).isUnit_of_dvd' hdvd dvd_rfl
  have hden : (r.den : ℤ) = 1 := by
    rcases Int.isUnit_iff.mp hunit with h | h
    · exact h
    · have := r.den_pos
      omega
  refine ⟨r.num, ?_⟩
  have h3 : (r.den : ℚ) = 1 := by exact_mod_cast hden
  rw [key, h3, mul_one]

/-- A monic cubic over `ℚ` without rational roots is irreducible. -/
theorem irreducible_of_monic_cubic {p : ℚ[X]} (hm : p.Monic) (hd : p.natDegree = 3)
    (hroot : ∀ r : ℚ, p.eval r ≠ 0) : Irreducible p := by
  have hp1 : p ≠ 1 := by
    rintro rfl
    simp at hd
  rw [hm.irreducible_iff_lt_natDegree_lt hp1]
  intro q hq hdeg hdvd
  rw [hd, Finset.mem_Ioc] at hdeg
  have hq1 : q.natDegree = 1 := by omega
  obtain ⟨a, rfl⟩ : ∃ a, q = X + C a := ⟨_, hq.eq_X_add_C hq1⟩
  obtain ⟨g, rfl⟩ := hdvd
  apply hroot (-a)
  simp

/-! ### The two cubics -/

/-- The cubic `X^3 - X - 1`. -/
noncomputable def p1 : ℚ[X] := X ^ 3 - X - 1

/-- The cubic `X^3 + X^2 - 3X - 4`. -/
noncomputable def p2 : ℚ[X] := X ^ 3 + X ^ 2 - C 3 * X - C 4

theorem p1_natDegree : p1.natDegree = 3 := by
  unfold p1
  compute_degree!

theorem p2_natDegree : p2.natDegree = 3 := by
  unfold p2
  compute_degree!

theorem p1_monic : p1.Monic := by
  unfold p1
  monicity!

theorem p2_monic : p2.Monic := by
  unfold p2
  monicity!

theorem p1_no_root (r : ℚ) : p1.eval r ≠ 0 := by
  intro h
  have hr : r ^ 3 + (0 : ℤ) * r ^ 2 + (-1 : ℤ) * r + (-1 : ℤ) = 0 := by
    simp [p1] at h
    push_cast
    linear_combination h
  obtain ⟨z, rfl⟩ := int_of_rat_root 0 (-1) (-1) r hr
  have hz : z ^ 3 - z - 1 = 0 := by
    have : (z : ℚ) ^ 3 - z - 1 = 0 := by
      push_cast at hr
      linear_combination hr
    exact_mod_cast this
  have hdvd : z ∣ 1 := ⟨z ^ 2 - 1, by linear_combination -hz⟩
  have h1 : z ≤ 1 := Int.le_of_dvd one_pos hdvd
  have h2 : -z ≤ 1 := Int.le_of_dvd one_pos ((neg_dvd).mpr hdvd)
  have h3 : -1 ≤ z := by omega
  interval_cases z <;> omega

theorem p2_no_root (r : ℚ) : p2.eval r ≠ 0 := by
  intro h
  have hr : r ^ 3 + (1 : ℤ) * r ^ 2 + (-3 : ℤ) * r + (-4 : ℤ) = 0 := by
    simp [p2] at h
    push_cast
    linear_combination h
  obtain ⟨z, rfl⟩ := int_of_rat_root 1 (-3) (-4) r hr
  have hz : z ^ 3 + z ^ 2 - 3 * z - 4 = 0 := by
    have : (z : ℚ) ^ 3 + (z : ℚ) ^ 2 - 3 * z - 4 = 0 := by
      push_cast at hr
      linear_combination hr
    exact_mod_cast this
  have hdvd : z ∣ 4 := ⟨z ^ 2 + z - 3, by linear_combination -hz⟩
  have h1 : z ≤ 4 := Int.le_of_dvd (by norm_num) hdvd
  have h2 : -z ≤ 4 := Int.le_of_dvd (by norm_num) ((neg_dvd).mpr hdvd)
  have h3 : -4 ≤ z := by omega
  interval_cases z <;> omega

theorem p1_irreducible : Irreducible p1 :=
  irreducible_of_monic_cubic p1_monic p1_natDegree p1_no_root

theorem p2_irreducible : Irreducible p2 :=
  irreducible_of_monic_cubic p2_monic p2_natDegree p2_no_root

theorem minpoly_eq_p1 {x : ℝ} (hx : x ^ 3 - x - 1 = 0) : minpoly ℚ x = p1 := by
  refine (minpoly.eq_of_irreducible_of_monic p1_irreducible ?_ p1_monic).symm
  simp [p1, hx]

theorem minpoly_eq_p2 {y : ℝ} (hy : y ^ 3 + y ^ 2 - 3 * y - 4 = 0) : minpoly ℚ y = p2 := by
  refine (minpoly.eq_of_irreducible_of_monic p2_irreducible ?_ p2_monic).symm
  simp [p2, hy]

theorem algDegree_root_p1 {x : ℝ} (hx : x ^ 3 - x - 1 = 0) : algDegree x = 3 := by
  rw [algDegree, minpoly_eq_p1 hx, p1_natDegree]

theorem algDegree_root_p2 {y : ℝ} (hy : y ^ 3 + y ^ 2 - 3 * y - 4 = 0) : algDegree y = 3 := by
  rw [algDegree, minpoly_eq_p2 hy, p2_natDegree]

/-! ### Existence of the two real roots -/

theorem exists_root_p1 : ∃ x : ℝ, 5 / 4 ≤ x ∧ x ≤ 2 ∧ x ^ 3 - x - 1 = 0 := by
  have hc : ContinuousOn (fun x : ℝ => x ^ 3 - x - 1) (Set.Icc (5 / 4) 2) := by fun_prop
  have h0 : (0 : ℝ) ∈ Set.Icc (((5 : ℝ) / 4) ^ 3 - 5 / 4 - 1) ((2 : ℝ) ^ 3 - 2 - 1) := by
    constructor <;> norm_num
  obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc (by norm_num : (5 / 4 : ℝ) ≤ 2) hc h0
  exact ⟨x, hx.1, hx.2, hfx⟩

theorem exists_root_p2 :
    ∃ y : ℝ, 9 / 5 ≤ y ∧ y ≤ 2 ∧ y ^ 3 + y ^ 2 - 3 * y - 4 = 0 := by
  have hc : ContinuousOn (fun y : ℝ => y ^ 3 + y ^ 2 - 3 * y - 4) (Set.Icc (9 / 5) 2) := by
    fun_prop
  have h0 : (0 : ℝ) ∈ Set.Icc (((9 : ℝ) / 5) ^ 3 + ((9 : ℝ) / 5) ^ 2 - 3 * (9 / 5) - 4)
      ((2 : ℝ) ^ 3 + (2 : ℝ) ^ 2 - 3 * 2 - 4) := by
    constructor <;> norm_num
  obtain ⟨y, hy, hfy⟩ := intermediate_value_Icc (by norm_num : (9 / 5 : ℝ) ≤ 2) hc h0
  exact ⟨y, hy.1, hy.2, hfy⟩

/-! ### The realising matrices -/

/-- A primitive `3 × 3` matrix with characteristic polynomial `X^3 - X - 1`. -/
def A3 : Matrix (Fin 3) (Fin 3) ℕ := !![0, 1, 0; 0, 0, 1; 1, 1, 0]

/-- A primitive `4 × 4` matrix with characteristic polynomial
`(X - 1)(X^3 + X^2 - 3X - 4)`. -/
def A4 : Matrix (Fin 4) (Fin 4) ℕ := !![0, 0, 1, 2; 1, 0, 2, 0; 0, 1, 0, 0; 1, 0, 0, 0]

theorem A3_primitive : IsPrimitive A3 := ⟨5, by norm_num, by decide⟩

theorem A4_primitive : IsPrimitive A4 := ⟨5, by norm_num, by decide⟩

theorem A3_perron {x : ℝ} (hx0 : 5 / 4 ≤ x) (hx : x ^ 3 - x - 1 = 0) :
    IsPerronEigenvalue A3 x := by
  have hpos : 0 < x := by linarith
  refine ⟨![1, x, x ^ 2], ?_, ?_⟩
  · intro i
    fin_cases i
    · exact one_pos
    · exact hpos
    · exact pow_pos hpos 2
  · ext i
    fin_cases i
    · simp [realMat, A3, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    · simp [realMat, A3, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      ring
    · simp [realMat, A3, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      linear_combination -hx

theorem A4_perron {y : ℝ} (hy0 : 9 / 5 ≤ y) (hy : y ^ 3 + y ^ 2 - 3 * y - 4 = 0) :
    IsPerronEigenvalue A4 y := by
  have hpos : 0 < y := by linarith
  have hsq : 0 < y ^ 2 - 2 := by nlinarith
  refine ⟨![y, y ^ 3 - 2 * y, y ^ 2 - 2, 1], ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hpos
    · have : y ^ 3 - 2 * y = y * (y ^ 2 - 2) := by ring
      show 0 < y ^ 3 - 2 * y
      rw [this]
      exact mul_pos hpos hsq
    · exact hsq
    · exact one_pos
  · ext i
    fin_cases i
    · simp [realMat, A4, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
      ring
    · simp [realMat, A4, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
      linear_combination (1 - y) * hy
    · simp [realMat, A4, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
      ring
    · simp [realMat, A4, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-! ### No matrix of size three realises the second root -/

/-- A real root of `X^3 + X^2 - 3X - 4` is not an eigenvalue of any nonnegative integer
`3 × 3` matrix: the characteristic polynomial would be `X^3 + X^2 - 3X - 4`, so the trace
would be `-1`. -/
theorem not_isEigenvalue_three {y : ℝ} (hy : y ^ 3 + y ^ 2 - 3 * y - 4 = 0)
    (A : Matrix (Fin 3) (Fin 3) ℕ) : ¬ IsEigenvalue A y := by
  intro h
  have hdvd := minpoly_dvd_charpoly h
  rw [minpoly_eq_p2 hy] at hdvd
  have hchar : (A.map (Nat.cast : ℕ → ℚ)).charpoly = p2 := by
    refine eq_of_monic_of_dvd_of_natDegree_le p2_monic (Matrix.charpoly_monic _) hdvd ?_
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, p2_natDegree]
  have htr := Matrix.trace_eq_neg_charpoly_coeff (A.map (Nat.cast : ℕ → ℚ))
  rw [hchar, Fintype.card_fin] at htr
  have hcoeff : p2.coeff (3 - 1) = 1 := by
    simp [p2, coeff_X, coeff_one]
  rw [hcoeff] at htr
  have hnonneg : (0 : ℚ) ≤ (A.map (Nat.cast : ℕ → ℚ)).trace := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.map_apply]
    exact Finset.sum_nonneg fun i _ => Nat.cast_nonneg _
  rw [htr] at hnonneg
  norm_num at hnonneg

/-! ### Minimal sizes and the refutation -/

theorem isMinSize_root_p1 {x : ℝ} (hx0 : 5 / 4 ≤ x) (hx : x ^ 3 - x - 1 = 0) :
    IsMinSize x 3 := by
  refine ⟨⟨by norm_num, A3, A3_primitive, A3_perron hx0 hx⟩, fun k hk => ?_⟩
  apply not_realizable_of_lt
  rw [algDegree_root_p1 hx]
  exact hk

theorem isMinSize_root_p2 {y : ℝ} (hy0 : 9 / 5 ≤ y) (hy : y ^ 3 + y ^ 2 - 3 * y - 4 = 0) :
    IsMinSize y 4 := by
  refine ⟨⟨by norm_num, A4, A4_primitive, A4_perron hy0 hy⟩, fun k hk => ?_⟩
  by_cases hk3 : k < 3
  · apply not_realizable_of_lt
    rw [algDegree_root_p2 hy]
    exact hk3
  · have hk' : k = 3 := by omega
    subst hk'
    rintro ⟨hpos, A, -, hA⟩
    exact not_isEigenvalue_three hy A (hA.isEigenvalue hpos)

/-! ### Both roots are Perron numbers -/

/-- The other two complex roots of `X^3 - X - 1` are smaller in modulus than the real root. -/
theorem root_p1_conj_lt {x : ℝ} (hx0 : 5 / 4 ≤ x) (hx : x ^ 3 - x - 1 = 0) (mu : ℂ)
    (hmu : mu ^ 3 - mu - 1 = 0) (hne : mu ≠ (x : ℂ)) : ‖mu‖ < x := by
  have hxC : (x : ℂ) ^ 3 - x - 1 = 0 := by exact_mod_cast congrArg Complex.ofReal hx
  have h2 : (mu - x) * (mu ^ 2 + x * mu + ((x : ℂ) ^ 2 - 1)) = 0 := by
    linear_combination hmu - hxC
  have h3 : mu ^ 2 + x * mu + ((x : ℂ) ^ 2 - 1) = 0 :=
    (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hne)
  have hre : mu.re * mu.re - mu.im * mu.im + x * mu.re + (x * x - 1) = 0 := by
    have := congrArg Complex.re h3
    simpa [pow_two] using this
  have him : mu.re * mu.im + mu.im * mu.re + x * mu.im = 0 := by
    have := congrArg Complex.im h3
    simpa [pow_two] using this
  have hx2 : 25 / 16 ≤ x * x := by nlinarith
  have hsq : ‖mu‖ ^ 2 < x ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    have hb : mu.im * (2 * mu.re + x) = 0 := by linear_combination him
    rcases mul_eq_zero.mp hb with hb0 | hax
    · exfalso
      rw [hb0] at hre
      nlinarith [sq_nonneg (2 * mu.re + x)]
    · have ha : mu.re = -x / 2 := by linarith
      rw [ha] at hre ⊢
      nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 (by linarith) hsq

/-- The other two complex roots of `X^3 + X^2 - 3X - 4` are smaller in modulus than the real
root in `[9/5, 2]`. -/
theorem root_p2_conj_lt {y : ℝ} (hy0 : 9 / 5 ≤ y) (hy2 : y ≤ 2)
    (hy : y ^ 3 + y ^ 2 - 3 * y - 4 = 0) (mu : ℂ) (hmu : mu ^ 3 + mu ^ 2 - 3 * mu - 4 = 0)
    (hne : mu ≠ (y : ℂ)) : ‖mu‖ < y := by
  have hyC : (y : ℂ) ^ 3 + (y : ℂ) ^ 2 - 3 * y - 4 = 0 := by
    exact_mod_cast congrArg Complex.ofReal hy
  have h2 : (mu - y) * (mu ^ 2 + (y + 1) * mu + ((y : ℂ) ^ 2 + y - 3)) = 0 := by
    linear_combination hmu - hyC
  have h3 : mu ^ 2 + (y + 1) * mu + ((y : ℂ) ^ 2 + y - 3) = 0 :=
    (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hne)
  have hre : mu.re * mu.re - mu.im * mu.im + (y + 1) * mu.re + (y * y + y - 3) = 0 := by
    have := congrArg Complex.re h3
    simpa [pow_two] using this
  have him : mu.re * mu.im + mu.im * mu.re + (y + 1) * mu.im = 0 := by
    have := congrArg Complex.im h3
    simpa [pow_two] using this
  have hy3 : 81 / 25 ≤ y * y := by nlinarith
  have hsq : ‖mu‖ ^ 2 < y ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    have hb : mu.im * (2 * mu.re + y + 1) = 0 := by linear_combination him
    rcases mul_eq_zero.mp hb with hb0 | hay
    · exfalso
      rw [hb0] at hre
      nlinarith [sq_nonneg (2 * mu.re + y + 1)]
    · have ha : mu.re = -(y + 1) / 2 := by linarith
      rw [ha] at hre ⊢
      nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 (by linarith) hsq

theorem isPerronNumber_root_p1 {x : ℝ} (hx0 : 5 / 4 ≤ x) (hx : x ^ 3 - x - 1 = 0) :
    IsPerronNumber x := by
  refine ⟨⟨X ^ 3 - X - 1, by monicity!, by simp [hx]⟩, by linarith, fun mu hmu hne => ?_⟩
  rw [minpoly_eq_p1 hx] at hmu
  refine root_p1_conj_lt hx0 hx mu ?_ hne
  simpa [p1] using hmu

theorem isPerronNumber_root_p2 {y : ℝ} (hy0 : 9 / 5 ≤ y) (hy2 : y ≤ 2)
    (hy : y ^ 3 + y ^ 2 - 3 * y - 4 = 0) : IsPerronNumber y := by
  refine ⟨⟨X ^ 3 + X ^ 2 - C 3 * X - C 4, by monicity!, by simp [hy]⟩, by linarith,
    fun mu hmu hne => ?_⟩
  rw [minpoly_eq_p2 hy] at hmu
  refine root_p2_conj_lt hy0 hy2 hy mu ?_ hne
  simpa [p2] using hmu

/-- Two adjacent coefficients of `X^3 - X - 1` are both equal to `-1`. -/
theorem p1_not_alternating : ¬ WeaklySignAlternating p1 := by
  intro h
  have h0 := h 0 (by rw [p1_natDegree]; norm_num)
  have c0 : p1.coeff 0 = -1 := by simp [p1, coeff_X, coeff_one]
  have c1 : p1.coeff 1 = -1 := by simp [p1, coeff_X, coeff_one]
  rw [c0, c1] at h0
  norm_num at h0

/-- There are two Perron numbers of algebraic degree three, with minimal realising sizes
three and four. The minimal polynomial of the first is not sign-alternating. -/
theorem two_cubic_perron_numbers :
    ∃ x y : ℝ, IsPerronNumber x ∧ IsPerronNumber y ∧ algDegree x = 3 ∧ algDegree y = 3 ∧
      IsMinSize x 3 ∧ IsMinSize y 4 ∧ ¬ WeaklySignAlternating (minpoly ℚ x) := by
  obtain ⟨x, hx0, -, hx⟩ := exists_root_p1
  obtain ⟨y, hy0, hy2, hy⟩ := exists_root_p2
  refine ⟨x, y, isPerronNumber_root_p1 hx0 hx, isPerronNumber_root_p2 hy0 hy2 hy,
    algDegree_root_p1 hx, algDegree_root_p2 hy, isMinSize_root_p1 hx0 hx,
    isMinSize_root_p2 hy0 hy, ?_⟩
  rw [minpoly_eq_p1 hx]
  exact p1_not_alternating

/-- The minimal size of a realising matrix is not a function of the algebraic degree. -/
theorem conjecture_false : ¬ ClaimedDegreeLaw := by
  rintro ⟨f, hf⟩
  obtain ⟨x, y, hPx, hPy, hdx, hdy, hx, hy, -⟩ := two_cubic_perron_numbers
  have h3 := hf x hPx
  have h4 := hf y hPy
  rw [hdx] at h3
  rw [hdy] at h4
  have e3 : f 3 = 3 := h3.unique hx
  have e4 : f 3 = 4 := h4.unique hy
  omega

/-- The same refutation when the clause is quantified over all realised numbers. -/
theorem conjecture_false_realized : ¬ ClaimedDegreeLawRealized := by
  rintro ⟨f, hf⟩
  obtain ⟨x, y, -, -, hdx, hdy, hx, hy, -⟩ := two_cubic_perron_numbers
  have h3 := hf x ⟨3, hx.1⟩
  have h4 := hf y ⟨4, hy.1⟩
  rw [hdx] at h3
  rw [hdy] at h4
  have e3 : f 3 = 3 := h3.unique hx
  have e4 : f 3 = 4 := h4.unique hy
  omega

/-- The sign-alternation criterion fails: the real root of `X^3 - X - 1` has minimal size
equal to its degree, and its minimal polynomial is not sign-alternating. -/
theorem sign_criterion_false : ¬ ClaimedSignCriterion := by
  intro h
  obtain ⟨x, -, hPx, -, hdx, -, hx, -, hnot⟩ := two_cubic_perron_numbers
  have := (h x hPx).mp (by rw [hdx]; exact hx)
  exact hnot this

#print axioms norm_le_of_isPerronEigenvalue
#print axioms pathCount_bounds
#print axioms hasEntropy_log
#print axioms p1_irreducible
#print axioms p2_irreducible
#print axioms A3_primitive
#print axioms A4_primitive
#print axioms not_isEigenvalue_three
#print axioms isMinSize_root_p1
#print axioms isMinSize_root_p2
#print axioms isPerronNumber_root_p1
#print axioms isPerronNumber_root_p2
#print axioms two_cubic_perron_numbers
#print axioms conjecture_false
#print axioms conjecture_false_realized
#print axioms sign_criterion_false

end Conjecture9611
