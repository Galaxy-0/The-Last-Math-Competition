import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

noncomputable section
open scoped Topology InnerProductSpace ENNReal
open Filter
namespace Counterexample
abbrev B := EuclideanSpace ℂ (Fin 2)
abbrev H := lp (fun _ : ℕ => B) 2

def embed (n : ℕ) : B →L[ℂ] H := lp.singleContinuousLinearMap ℂ (fun _ : ℕ => B) 2 n

def coord (n : ℕ) : H →L[ℂ] B :=
  LinearMap.mkContinuous
    { toFun := fun x => x n
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } 1
    (fun x => by simpa using lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) x n)

def projection (n : ℕ) : H →L[ℂ] H := (embed n).comp (coord n)
def weight (n : ℕ) : ℂ := Complex.I * ((1/2 : ℂ)^n)
def term (n : ℕ) : H →L[ℂ] H := weight n • projection n

theorem projection_apply (n : ℕ) (x : H) : projection n x = lp.single 2 n (x n) := rfl

theorem projection_norm (n : ℕ) : ‖projection n‖ ≤ 1 := by
  apply (projection n).opNorm_le_bound (by norm_num)
  intro x
  rw [projection_apply, lp.norm_single (by norm_num)]
  simpa using lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) x n

theorem weight_norm (n : ℕ) : ‖weight n‖ = (1/2 : ℝ)^n := by
  simp [weight, norm_mul, norm_pow]

theorem terms_summable : Summable term := by
  apply Summable.of_norm_bounded (fun n => (1/2 : ℝ)^n)
    (summable_geometric_of_lt_one (by norm_num) (by norm_num))
  intro n
  calc
    ‖term n‖ ≤ ‖weight n‖ * ‖projection n‖ := by
      simpa only [term] using norm_smul_le (weight n) (projection n)
    _ ≤ (1/2 : ℝ)^n := by
      rw [weight_norm]
      simpa using mul_le_mul_of_nonneg_left (projection_norm n) (by positivity : 0 ≤ (1/2:ℝ)^n)

def T : H →L[ℂ] H := ∑' n, term n

theorem projection_compact (n : ℕ) : IsCompactOperator (projection n) := by
  have hid : IsCompactOperator (id : B → B) :=
    ⟨Metric.closedBall 0 1, isCompact_closedBall 0 1, by simpa using Metric.closedBall_mem_nhds (0:B) (by norm_num : (0:ℝ)<1)⟩
  exact (hid.comp_clm (coord n)).clm_comp (embed n)

theorem T_compact : IsCompactOperator T := by
  apply isCompactOperator_of_tendsto terms_summable.hasSum
  apply Filter.Eventually.of_forall
  intro s
  change (∑ n ∈ s, term n) ∈ compactOperator (RingHom.id ℂ) H H
  exact Submodule.sum_mem _ (fun n _ => (projection_compact n).smul (weight n))

theorem projection_embed (m n : ℕ) (v : B) :
    projection m (embed n v) = if m = n then embed n v else 0 := by
  by_cases h : m = n
  · subst m
    simp [projection_apply, embed, lp.single_apply_self]
  · simp [projection_apply, embed, h, lp.single_apply_ne (E := fun _ : ℕ => B) 2 n v h]

theorem T_embed (n : ℕ) (v : B) : T (embed n v) = weight n • embed n v := by
  have hs := terms_summable.hasSum.mapL (ContinuousLinearMap.apply ℂ H (embed n v))
  have ht : HasSum (fun m => term m (embed n v)) (weight n • embed n v) := by
    convert hasSum_ite_eq n (weight n • embed n v) using 1
    ext m
    simp only [term, ContinuousLinearMap.smul_apply, projection_embed]
    split_ifs with h
    · subst m; rfl
    · simp
  exact hs.unique ht

def eigenvectors (n : ℕ) (j : Fin 2) : H := embed n (EuclideanSpace.single j 1)

theorem eigenvectors_independent (n : ℕ) : LinearIndependent ℂ (eigenvectors n) := by
  apply (EuclideanSpace.orthonormal_single.linearIndependent).map' (embed n).toLinearMap
  apply LinearMap.ker_eq_bot.mpr
  exact (lp.isometry_single (E := fun _ : ℕ => B) (p := 2) n).injective

theorem eigenvectors_equation (n : ℕ) (j : Fin 2) :
    T (eigenvectors n j) = weight n • eigenvectors n j := T_embed n _

def MultipleEigenvalue (z : ℂ) : Prop :=
  ∃ v : Fin 2 → H, LinearIndependent ℂ v ∧ ∀ j, T (v j) = z • v j

theorem weight_multiple (n : ℕ) : MultipleEigenvalue (weight n) :=
  ⟨eigenvectors n, eigenvectors_independent n, eigenvectors_equation n⟩

theorem weight_injective : Function.Injective weight := by
  intro m n h
  have he := congrArg norm h
  simp only [weight_norm] at he
  exact (pow_right_injective₀ (by norm_num : (0:ℝ) < 1/2) (by norm_num : (1/2:ℝ) ≠ 1)) he

theorem infinitely_many_multiple : {z : ℂ | MultipleEigenvalue z}.Infinite := by
  apply (Set.infinite_range_of_injective weight_injective).mono
  rintro z ⟨n, rfl⟩
  exact weight_multiple n

theorem weight_ne_zero (n : ℕ) : weight n ≠ 0 := by
  exact mul_ne_zero Complex.I_ne_zero (pow_ne_zero _ (by norm_num))

theorem not_selfadjoint : ¬ ∀ x y : H, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ := by
  intro h
  have he := h (eigenvectors 0 0) (eigenvectors 0 0)
  simp only [eigenvectors_equation] at he
  simp [inner_smul_left, inner_smul_right, eigenvectors, embed, lp.inner_single_left,
    EuclideanSpace.inner_single_left, weight] at he
  have hi := congrArg Complex.im he
  norm_num at hi

theorem counterexample : IsCompactOperator T ∧
    (¬ ∀ x y : H, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ) ∧
    {z : ℂ | MultipleEigenvalue z}.Infinite :=
  ⟨T_compact, not_selfadjoint, infinitely_many_multiple⟩

#print axioms terms_summable
#print axioms T_compact
#print axioms T_embed
#print axioms eigenvectors_independent
#print axioms weight_injective
#print axioms weight_ne_zero
#print axioms not_selfadjoint
#print axioms counterexample
end Counterexample
