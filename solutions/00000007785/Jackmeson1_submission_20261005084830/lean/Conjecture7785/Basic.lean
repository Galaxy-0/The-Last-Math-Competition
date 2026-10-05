import Mathlib

/-!
# Conjecture 00000007785: the literal "4^n" Mahler statement fails

The conjecture (bilingual text) uses the Mahler product `M(K) = vol(K) vol(K°)`, asserts the
symmetric bound `M(K) ≥ 4^n`, and claims that the symmetric equality cases of that bound are the
Hanner polytopes.  We show that in every dimension `n ≥ 2` the cube `[-1,1]^n`, a Hanner polytope
(a Cartesian product of `n` segments), is an origin-symmetric convex body with

  `M([-1,1]^n) = 4^n / n! < 4^n`.

Hence, for every `n ≥ 2`, both the inequality `M(K) ≥ 4^n` for symmetric convex bodies and the
claim that every Hanner polytope is an equality case `M(K) = 4^n` are false.

Conventions: `ℝ^n` is `Fin n → ℝ` with the standard dot product `∑ i, x i * y i` and Lebesgue
measure `volume` (the product measure, which is Euclidean volume).  The polar is
`K° = {y | ∀ x ∈ K, x · y ≤ 1}`.  Volumes are `ℝ≥0∞`-valued.
-/

open MeasureTheory Set Finset
open scoped Nat ENNReal

namespace C7785

/-- Polar body `K° = {y | x · y ≤ 1 for all x ∈ K}` (standard dot product on `ℝ^n`). -/
def polar {n : ℕ} (K : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {y | ∀ x ∈ K, ∑ i, x i * y i ≤ 1}

/-- Mahler product `M(K) = vol(K) · vol(K°)` with Lebesgue measure. -/
noncomputable def mahler {n : ℕ} (K : Set (Fin n → ℝ)) : ℝ≥0∞ :=
  volume K * volume (polar K)

/-- An origin-symmetric convex body: compact, convex, nonempty interior, and `K = -K`. -/
structure IsSymmetricConvexBody {n : ℕ} (K : Set (Fin n → ℝ)) : Prop where
  convex : Convex ℝ K
  compact : IsCompact K
  interior_nonempty : (interior K).Nonempty
  symm : ∀ x ∈ K, -x ∈ K

/-- Hanner polytopes, built recursively from the segment `[-1,1] ⊂ ℝ^1` by Cartesian products
(dimensions add, coordinates concatenated) and polar duals. -/
inductive IsHanner : (n : ℕ) → Set (Fin n → ℝ) → Prop
  | segment : IsHanner 1 {x | |x 0| ≤ 1}
  | prod {m k : ℕ} {K : Set (Fin m → ℝ)} {L : Set (Fin k → ℝ)} :
      IsHanner m K → IsHanner k L →
      IsHanner (m + k)
        {z | (fun i => z (Fin.castAdd k i)) ∈ K ∧ (fun j => z (Fin.natAdd m j)) ∈ L}
  | dual {m : ℕ} {K : Set (Fin m → ℝ)} : IsHanner m K → IsHanner m (polar K)

/-- The cube `[-1,1]^n`. -/
def cube (n : ℕ) : Set (Fin n → ℝ) := {x | ∀ i, |x i| ≤ 1}

/-- The cross-polytope `{y | ∑ |y i| ≤ 1}`. -/
def crossPolytope (n : ℕ) : Set (Fin n → ℝ) := {y | ∑ i, |y i| ≤ 1}

theorem cube_eq_Icc (n : ℕ) : cube n = Set.Icc (-1) 1 := by
  ext x
  simp only [cube, mem_ofPred_eq, Set.mem_Icc, Pi.le_def, Pi.neg_apply, Pi.one_apply, abs_le]
  exact ⟨fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩, fun h i => ⟨h.1 i, h.2 i⟩⟩

/-- The polar of the cube is the cross-polytope. -/
theorem polar_cube (n : ℕ) : polar (cube n) = crossPolytope n := by
  ext y
  simp only [polar, cube, crossPolytope, mem_ofPred_eq]
  constructor
  · intro h
    have key := h (fun i => if 0 ≤ y i then 1 else -1) (fun i => by split_ifs <;> norm_num)
    convert key using 2 with i
    split_ifs with hi
    · rw [one_mul, abs_of_nonneg hi]
    · rw [abs_of_neg (not_le.mp hi)]; ring
  · intro hy x hx
    calc ∑ i, x i * y i ≤ ∑ i, |y i| := by
          refine Finset.sum_le_sum fun i _ => ?_
          calc x i * y i ≤ |x i * y i| := le_abs_self _
            _ = |x i| * |y i| := abs_mul _ _
            _ ≤ 1 * |y i| := by gcongr; exact hx i
            _ = |y i| := one_mul _
      _ ≤ 1 := hy

theorem volume_cube (n : ℕ) : volume (cube n) = 2 ^ n := by
  rw [cube_eq_Icc, Real.volume_Icc_pi]
  simp only [Pi.one_apply, Pi.neg_apply, sub_neg_eq_add]
  norm_num

theorem volume_crossPolytope (n : ℕ) (hn : 1 ≤ n) :
    volume (crossPolytope n) = ENNReal.ofReal (2 ^ n / n !) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hset : crossPolytope n = {x : Fin n → ℝ | (∑ i, |x i| ^ (1 : ℝ)) ^ (1 / (1 : ℝ)) ≤ 1} := by
    ext x; simp [crossPolytope, Real.rpow_one]
  rw [hset, volume_sum_rpow_le (Fin n) le_rfl 1]
  simp only [ENNReal.ofReal_one, one_pow, one_mul, Fintype.card_fin, div_one]
  norm_num [Real.Gamma_two, Real.Gamma_nat_eq_factorial]

/-- The Mahler product of the cube is `4^n / n!`. -/
theorem mahler_cube (n : ℕ) (hn : 1 ≤ n) : mahler (cube n) = ENNReal.ofReal (4 ^ n / n !) := by
  rw [mahler, polar_cube, volume_cube, volume_crossPolytope n hn]
  have h2 : (2 : ℝ≥0∞) ^ n = ENNReal.ofReal (2 ^ n) := by
    rw [ENNReal.ofReal_pow (by norm_num)]; norm_num
  rw [h2, ← ENNReal.ofReal_mul (by positivity), mul_div_assoc', ← mul_pow]
  norm_num

theorem mahler_cube_lt (n : ℕ) (hn : 2 ≤ n) : mahler (cube n) < 4 ^ n := by
  rw [mahler_cube n (by omega)]
  have h4 : (4 : ℝ≥0∞) ^ n = ENNReal.ofReal (4 ^ n) := by
    rw [ENNReal.ofReal_pow (by norm_num)]; norm_num
  rw [h4, ENNReal.ofReal_lt_ofReal_iff (by positivity)]
  have hf : (1 : ℝ) < n ! := by exact_mod_cast Nat.one_lt_factorial.mpr (by omega)
  exact div_lt_self (by positivity) hf

theorem cube_isSymmetricConvexBody (n : ℕ) : IsSymmetricConvexBody (cube n) where
  convex := by rw [cube_eq_Icc]; exact convex_Icc (-1 : Fin n → ℝ) 1
  compact := by rw [cube_eq_Icc]; exact isCompact_Icc
  interior_nonempty := by
    refine ⟨0, mem_interior.2 ⟨Metric.ball 0 1, fun x hx i => ?_, Metric.isOpen_ball,
      Metric.mem_ball_self one_pos⟩⟩
    have h1 : ‖x i‖ ≤ ‖x‖ := norm_le_pi_norm x i
    rw [mem_ball_zero_iff] at hx
    rw [← Real.norm_eq_abs]; linarith
  symm := fun x hx i => by simpa using hx i

/-- The cube `[-1,1]^(n+1)` is a Hanner polytope (iterated product of segments). -/
theorem cube_isHanner_succ : ∀ n : ℕ, IsHanner (n + 1) (cube (n + 1))
  | 0 => by
    have hc : cube 1 = {x : Fin 1 → ℝ | |x 0| ≤ 1} := by
      ext x; simp [cube, Fin.forall_fin_one]
    rw [hc]; exact IsHanner.segment
  | n + 1 => by
    have h := IsHanner.prod (cube_isHanner_succ n) IsHanner.segment
    convert h using 1
    ext z
    simp only [cube, mem_ofPred_eq]
    rw [Fin.forall_fin_add, Fin.forall_fin_one]

theorem cube_isHanner (n : ℕ) (hn : 1 ≤ n) : IsHanner n (cube n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact cube_isHanner_succ m

/-- **Main theorem.** For every `n ≥ 2` the cube `[-1,1]^n` is a Hanner polytope and an
origin-symmetric convex body whose Mahler product is `4^n / n! < 4^n`. Consequently, in every
dimension `n ≥ 2`: (i) the inequality `M(K) ≥ 4^n` fails for some symmetric convex body, and
(ii) not every Hanner polytope is an equality case `M(K) = 4^n`. -/
theorem conjecture_7785_symmetric_clause_false (n : ℕ) (hn : 2 ≤ n) :
    (IsHanner n (cube n) ∧ IsSymmetricConvexBody (cube n) ∧
        mahler (cube n) = ENNReal.ofReal (4 ^ n / n !) ∧ mahler (cube n) < 4 ^ n) ∧
      ¬ (∀ K : Set (Fin n → ℝ), IsSymmetricConvexBody K → (4 : ℝ≥0∞) ^ n ≤ mahler K) ∧
      ¬ (∀ K : Set (Fin n → ℝ), IsHanner n K → mahler K = 4 ^ n) := by
  have hlt := mahler_cube_lt n hn
  have hH := cube_isHanner n (by omega)
  have hS := cube_isSymmetricConvexBody n
  refine ⟨⟨hH, hS, mahler_cube n (by omega), hlt⟩, fun h => ?_, fun h => ?_⟩
  · exact absurd (h _ hS) (not_le.mpr hlt)
  · exact absurd (h _ hH) (ne_of_lt hlt)

end C7785
