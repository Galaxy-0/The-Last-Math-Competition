import Mathlib

/-!
# Conjecture 00000003238: the "edge theorem" for direct sums of operators is false

The conjecture asserts that for a direct sum `⊕ₙ Aₙ` of bounded operators on Hilbert spaces, the
closure of the spectrum of the direct sum is the closure of the union of the block spectra
(followed by an undefined clause about "accumulated edges", which is not needed here).

We give a uniformly bounded family where this fails.  The `n`-th block is the nilpotent shift
`Jₙ` on `ℂ^{n+1}` (a single nilpotent Jordan block of size `n+1`), so `σ(Jₙ) = {0}` and the closure
of the union of the block spectra is `{0}`.  The direct sum `T = ⊕ₙ Jₙ` acts on Mathlib's Hilbert
sum `lp (fun n => EuclideanSpace ℂ (Fin (n+1))) 2`, has `‖T‖ ≤ 1`, and its spectrum is the closed
unit disc.  In particular `1/2 ∈ σ(T)`, so `closure σ(T) ≠ closure (⋃ₙ σ(Jₙ))`.

All spectra are Mathlib's `spectrum ℂ` in the Banach algebra of bounded operators.
-/

open scoped ENNReal

namespace C3238

/-! ## The Hilbert direct sum of a contractive family -/

section DirectSum

variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)] [∀ n, InnerProductSpace ℂ (E n)]
variable (A : ∀ n, E n →L[ℂ] E n) (hA : ∀ n, ‖A n‖ ≤ 1)

include hA in
theorem norm_block_apply_le (n : ℕ) (v : E n) : ‖A n v‖ ≤ ‖v‖ := by
  simpa using (A n).le_of_opNorm_le (hA n) v

include hA in
theorem memℓp_blockApply (x : lp E 2) : Memℓp (fun n => A n (x n)) 2 :=
  (lp.memℓp x).mono' fun n => norm_block_apply_le A hA n (x n)

/-- Blockwise application `x ↦ (Aₙ xₙ)ₙ`, as a linear map on the Hilbert sum `lp E 2`. -/
def dsumLin : lp E 2 →ₗ[ℂ] lp E 2 where
  toFun x := ⟨fun n => A n (x n), memℓp_blockApply A hA x⟩
  map_add' x y := lp.ext <| funext fun n => by
    change A n ((x + y) n) = A n (x n) + A n (y n)
    rw [lp.coeFn_add, Pi.add_apply, map_add]
  map_smul' c x := lp.ext <| funext fun n => by
    change A n ((c • x) n) = c • A n (x n)
    rw [lp.coeFn_smul, Pi.smul_apply, map_smul]

/-- The direct sum operator `⊕ₙ Aₙ` on the Hilbert sum `lp E 2`, a bounded operator. -/
noncomputable def dsum : lp E 2 →L[ℂ] lp E 2 :=
  (dsumLin A hA).mkContinuous 1 fun x => by
    rw [one_mul]
    exact lp.norm_mono two_ne_zero fun n => norm_block_apply_le A hA n (x n)

/-- The defining property of the direct sum: it acts on the `n`-th coordinate as `Aₙ`. -/
@[simp] theorem dsum_apply (x : lp E 2) (n : ℕ) : dsum A hA x n = A n (x n) := rfl

theorem norm_dsum_le : ‖dsum A hA‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- On the `n`-th summand the direct sum is `Aₙ`. -/
theorem dsum_single (n : ℕ) (v : E n) :
    dsum A hA (lp.single 2 n v) = lp.single 2 n (A n v) := by
  refine lp.ext (funext fun m => ?_)
  rw [dsum_apply]
  rcases eq_or_ne m n with rfl | h
  · rw [lp.single_apply_self, lp.single_apply_self]
  · rw [lp.single_apply_ne _ _ _ h, lp.single_apply_ne _ _ _ h, map_zero]

/-- Uniqueness: a bounded operator acting blockwise as `(Aₙ)` is `dsum A`. -/
theorem dsum_unique (S : lp E 2 →L[ℂ] lp E 2) (hS : ∀ x n, S x n = A n (x n)) :
    S = dsum A hA :=
  ContinuousLinearMap.ext fun x => lp.ext <| funext fun n => hS x n

end DirectSum

/-- The conjecture's identity, for all contractive families of operators on Hilbert spaces indexed
by `ℕ`: `closure σ(⊕ₙ Aₙ) = closure (⋃ₙ σ(Aₙ))`.  (Contractive families are uniformly bounded, so
this is a special case of the conjecture's claim.) -/
def EdgeTheorem : Prop :=
  ∀ (E : ℕ → Type) [∀ n, NormedAddCommGroup (E n)] [∀ n, InnerProductSpace ℂ (E n)]
    [∀ n, CompleteSpace (E n)] (A : ∀ n, E n →L[ℂ] E n) (hA : ∀ n, ‖A n‖ ≤ 1),
    closure (spectrum ℂ (dsum A hA)) = closure (⋃ n, spectrum ℂ (A n))

/-! ## The blocks: nilpotent shifts -/

/-- The `n`-th summand: `ℂ^{n+1}` with the Euclidean norm. -/
abbrev Block (n : ℕ) : Type := EuclideanSpace ℂ (Fin (n + 1))

/-- The shift on `ℂ^{n+1}`: `(J v)ⱼ = v_{j+1}` for `j < n` and `(J v)ₙ = 0`. -/
def shiftFun (n : ℕ) (v : Block n) : Block n :=
  WithLp.toLp 2 fun j : Fin (n + 1) => if h : (j : ℕ) < n then v ⟨j + 1, by omega⟩ else 0

theorem shiftFun_apply (n : ℕ) (v : Block n) (j : Fin (n + 1)) :
    shiftFun n v j = if h : (j : ℕ) < n then v ⟨j + 1, by omega⟩ else 0 := rfl

/-- The shift as a linear map. -/
def shiftLin (n : ℕ) : Block n →ₗ[ℂ] Block n where
  toFun := shiftFun n
  map_add' v w := by
    ext j
    simp only [shiftFun_apply, PiLp.add_apply]
    split_ifs <;> simp
  map_smul' c v := by
    ext j
    simp only [shiftFun_apply, PiLp.smul_apply, RingHom.id_apply]
    split_ifs <;> simp

theorem norm_shiftFun_le (n : ℕ) (v : Block n) : ‖shiftFun n v‖ ≤ ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_succ]
  have h1 : ∀ i : Fin n, shiftFun n v (Fin.castSucc i) = v i.succ := fun i => by
    rw [shiftFun_apply, dif_pos (by simp)]
    rfl
  have h2 : shiftFun n v (Fin.last n) = 0 := by
    rw [shiftFun_apply, dif_neg (by simp)]
  simp only [h1, h2, norm_zero]
  nlinarith [sq_nonneg ‖v 0‖]

/-- The nilpotent shift `Jₙ` on `ℂ^{n+1}` as a bounded operator. -/
noncomputable def shift (n : ℕ) : Block n →L[ℂ] Block n :=
  (shiftLin n).mkContinuous 1 fun v => by
    rw [one_mul]
    exact norm_shiftFun_le n v

theorem shift_apply (n : ℕ) (v : Block n) (j : Fin (n + 1)) :
    shift n v j = if h : (j : ℕ) < n then v ⟨j + 1, by omega⟩ else 0 := rfl

theorem norm_shift_le (n : ℕ) : ‖shift n‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem shift_pow_apply (n k : ℕ) (v : Block n) (j : Fin (n + 1)) :
    (shift n ^ k) v j = if h : (j : ℕ) + k ≤ n then v ⟨j + k, by omega⟩ else 0 := by
  induction k generalizing v with
  | zero =>
    rw [pow_zero, one_apply_eq_self, dif_pos (by have := j.isLt; omega)]
    rfl
  | succ k ih =>
    rw [pow_succ, mul_apply_eq_comp, ih]
    split_ifs with h1 h2 h2
    · rw [shift_apply, dif_pos (by simp only; omega)]
      exact congrArg (fun i => v i) (Fin.ext (by simp only; omega))
    · rw [shift_apply, dif_neg (by simp only; omega)]
    · omega
    · rfl

theorem shift_pow_eq_zero (n : ℕ) : shift n ^ (n + 1) = 0 := by
  ext v j
  rw [shift_pow_apply, dif_neg (by omega)]
  simp

theorem isNilpotent_shift (n : ℕ) : IsNilpotent (shift n) := ⟨n + 1, shift_pow_eq_zero n⟩

/-- Each block has spectrum `{0}`. -/
theorem spectrum_shift (n : ℕ) : spectrum ℂ (shift n) = {0} := by
  ext μ
  rw [Set.mem_singleton_iff, spectrum.mem_iff]
  constructor
  · intro h
    by_contra hμ
    apply h
    rw [sub_eq_add_neg]
    exact (isNilpotent_shift n).neg.isUnit_add_left_of_commute
      ((IsUnit.mk0 μ hμ).map (algebraMap ℂ _)) (Algebra.commutes μ (-shift n)).symm
  · rintro rfl
    rw [map_zero, zero_sub]
    intro hu
    have : Nontrivial (Block n →L[ℂ] Block n) := by
      refine ⟨⟨0, 1, fun h0 => ?_⟩⟩
      have := congrArg (fun f : Block n →L[ℂ] Block n => f (EuclideanSpace.single 0 1) 0) h0
      simp at this
    exact hu.not_isNilpotent (isNilpotent_shift n).neg

theorem iUnion_spectrum_shift : ⋃ n, spectrum ℂ (shift n) = {0} := by
  simp only [spectrum_shift, Set.iUnion_const]

theorem closure_iUnion_spectrum_shift : closure (⋃ n, spectrum ℂ (shift n)) = {0} := by
  rw [iUnion_spectrum_shift, closure_singleton]

/-! ## The direct sum `T = ⊕ₙ Jₙ` has the closed unit disc as spectrum -/

/-- The direct sum `T = ⊕ₙ Jₙ` on the Hilbert sum `⊕ₙ ℂ^{n+1}`. -/
noncomputable def T : lp Block 2 →L[ℂ] lp Block 2 := dsum shift norm_shift_le

/-- The test vector `(1, z, z², …, zⁿ)` in `ℂ^{n+1}`. -/
def testVec (n : ℕ) (z : ℂ) : Block n := WithLp.toLp 2 fun j => z ^ (j : ℕ)

theorem block_identity (n : ℕ) (z : ℂ) :
    (algebraMap ℂ (Block n →L[ℂ] Block n) z - shift n) (testVec n z) =
      EuclideanSpace.single (Fin.last n) (z ^ (n + 1)) := by
  ext j
  rw [sub_apply, PiLp.sub_apply, Algebra.algebraMap_eq_smul_one,
    smul_apply, one_apply_eq_self, PiLp.smul_apply, shift_apply,
    PiLp.single_apply]
  simp only [testVec, PiLp.toLp_apply, smul_eq_mul]
  by_cases h : (j : ℕ) < n
  · have hj : j ≠ Fin.last n := fun hj => by rw [hj] at h; simp at h
    rw [dif_pos h, if_neg hj, pow_succ]
    ring
  · have hj : j = Fin.last n := Fin.ext (by have := j.isLt; simp; omega)
    rw [dif_neg h, if_pos hj, hj, Fin.val_last, pow_succ]
    ring

theorem sum_identity (n : ℕ) (z : ℂ) :
    (algebraMap ℂ (lp Block 2 →L[ℂ] lp Block 2) z - T) (lp.single 2 n (testVec n z)) =
      lp.single 2 n (EuclideanSpace.single (Fin.last n) (z ^ (n + 1))) := by
  rw [← block_identity, Algebra.algebraMap_eq_smul_one, sub_apply,
    smul_apply, one_apply_eq_self, T, dsum_single,
    ← lp.single_smul, ← lp.single_sub, Algebra.algebraMap_eq_smul_one,
    sub_apply, smul_apply, one_apply_eq_self]

/-- Every `z` in the open unit disc lies in `σ(T)`: `z - T` is not bounded below. -/
theorem mem_spectrum_T {z : ℂ} (hz : ‖z‖ < 1) : z ∈ spectrum ℂ T := by
  rw [spectrum.mem_iff]
  rintro ⟨u, hu⟩
  set S : lp Block 2 →L[ℂ] lp Block 2 := ↑u⁻¹ with hSdef
  have key : ∀ n : ℕ, 1 ≤ ‖S‖ * ‖z‖ ^ (n + 1) := by
    intro n
    set x := lp.single 2 n (testVec n z) with hxdef
    have hx : x = S ((algebraMap ℂ _ z - T) x) := by
      rw [← hu, hSdef, ← mul_apply_eq_comp, Units.inv_mul,
        one_apply_eq_self]
    have h1 : 1 ≤ ‖x‖ := by
      rw [hxdef, lp.norm_single zero_lt_two]
      calc (1 : ℝ) = ‖testVec n z 0‖ := by simp [testVec]
        _ ≤ ‖testVec n z‖ := PiLp.norm_apply_le _ _
    calc 1 ≤ ‖x‖ := h1
      _ = ‖S ((algebraMap ℂ _ z - T) x)‖ := by rw [← hx]
      _ ≤ ‖S‖ * ‖(algebraMap ℂ _ z - T) x‖ := S.le_opNorm _
      _ = ‖S‖ * ‖z‖ ^ (n + 1) := by
        rw [hxdef, sum_identity, lp.norm_single zero_lt_two, PiLp.norm_single,
          norm_pow]
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
    (show (0 : ℝ) < 1 / (‖S‖ + 1) by positivity) hz
  have h2 : ‖z‖ ^ (n + 1) ≤ ‖z‖ ^ n :=
    pow_le_pow_of_le_one (norm_nonneg _) hz.le (Nat.le_succ n)
  have h3 : ‖S‖ * ‖z‖ ^ (n + 1) ≤ ‖S‖ * ‖z‖ ^ n :=
    mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
  rw [lt_div_iff₀ (by positivity)] at hn
  nlinarith [key n, norm_nonneg S, pow_nonneg (norm_nonneg z) n]

/-- The spectrum of `T = ⊕ₙ Jₙ` is the closed unit disc. -/
theorem spectrum_T : spectrum ℂ T = Metric.closedBall 0 1 := by
  apply le_antisymm
  · intro z hz
    have h := spectrum.subset_closedBall_norm_mul T hz
    rw [Metric.mem_closedBall] at h ⊢
    calc dist z 0 ≤ ‖T‖ * ‖(1 : lp Block 2 →L[ℂ] lp Block 2)‖ := h
      _ ≤ 1 * 1 := mul_le_mul (norm_dsum_le _ _) ContinuousLinearMap.norm_id_le
          (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · rw [← closure_ball (0 : ℂ) one_ne_zero]
    exact closure_minimal (fun z hz => mem_spectrum_T (by simpa using hz)) (spectrum.isClosed T)

theorem half_mem_spectrum_T : (1 / 2 : ℂ) ∈ spectrum ℂ T := mem_spectrum_T (by norm_num)

/-- **Main theorem.** For the uniformly bounded family of nilpotent shifts `Jₙ` on `ℂ^{n+1}`, the
closure of the spectrum of the direct sum `⊕ₙ Jₙ` (the closed unit disc) differs from the closure
of the union of the block spectra (`{0}`). -/
theorem edge_theorem_counterexample :
    closure (spectrum ℂ T) ≠ closure (⋃ n, spectrum ℂ (shift n)) := by
  rw [closure_iUnion_spectrum_shift]
  intro h
  have h1 : (1 / 2 : ℂ) ∈ closure (spectrum ℂ T) := subset_closure half_mem_spectrum_T
  rw [h, Set.mem_singleton_iff] at h1
  norm_num at h1

/-- The conjecture's identity fails (for a contractive family on finite-dimensional Hilbert
spaces). -/
theorem not_edgeTheorem : ¬ EdgeTheorem := fun h =>
  edge_theorem_counterexample (h Block shift norm_shift_le)

end C3238
