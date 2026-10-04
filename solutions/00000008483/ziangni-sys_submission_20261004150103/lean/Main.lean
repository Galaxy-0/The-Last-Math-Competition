import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Seminorm
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

noncomputable section
open Filter Set
open scoped Topology
namespace BarabanovCounterexample

abbrev E := ℝ × ℝ
abbrev Op := E →L[ℝ] E
def J : Op :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    (ContinuousLinearMap.snd ℝ ℝ ℝ)
def A : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 0, 1]
def family : Set Op := {J}
def e1 : E := (1, 0)
def e2 : E := (0, 1)

@[simp] theorem J_apply (x : E) : J x = (x.1 + x.2, x.2) := rfl
theorem matrix_action (v : Fin 2 → ℝ) :
    J (v 0, v 1) = ((A.mulVec v) 0, (A.mulVec v) 1) := by
  simp [A, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
theorem compact_family : IsCompact family := isCompact_singleton

theorem power_apply (n : ℕ) (x : E) : (J ^ n) x = (x.1 + n * x.2, x.2) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', ContinuousLinearMap.mul_apply, ih, J_apply]
      ext <;> simp [add_mul, add_assoc]

theorem power_norm (n : ℕ) : ‖J ^ n‖ = n + 1 := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro x
    rw [power_apply, Prod.norm_def]
    apply max_le
    · calc
        ‖x.1 + (n : ℝ) * x.2‖ ≤ ‖x.1‖ + ‖(n : ℝ) * x.2‖ := norm_add_le _ _
        _ = ‖x.1‖ + n * ‖x.2‖ := by simp [norm_mul]
        _ ≤ ‖x‖ + n * ‖x‖ := add_le_add (norm_fst_le x)
          (mul_le_mul_of_nonneg_left (norm_snd_le x) (by positivity))
        _ = (n + 1) * ‖x‖ := by ring
    · have := norm_snd_le x
      have := norm_nonneg x
      nlinarith
  · have h := (J ^ n).le_opNorm (1, 1)
    have hf := (norm_fst_le ((J ^ n) (1, 1))).trans h
    have hh : |(n : ℝ) + 1| ≤ ‖J ^ n‖ := by
      simpa [power_apply, Prod.norm_def, Real.norm_eq_abs, add_comm] using hf
    simpa only [abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) + 1)] using hh

def products (K : Set Op) (n : ℕ) : Set Op :=
  {P | ∃ w : List Op, w.length = n ∧ (∀ L ∈ w, L ∈ K) ∧ w.prod = P}
def jointBound (K : Set Op) (n : ℕ) : ℝ := sSup (norm '' products K n)
def jointRadius (K : Set Op) : ℝ :=
  Filter.limsup (fun n : ℕ => jointBound K n ^ (1 / (n : ℝ))) atTop

theorem products_singleton (n : ℕ) : products family n = {J ^ n} := by
  ext P
  constructor
  · rintro ⟨w, hn, hw, rfl⟩
    have heq : w = List.replicate n J := List.eq_replicate_iff.mpr
      ⟨hn, fun L hL => by simpa [family] using hw L hL⟩
    simp [heq]
  · rintro rfl
    refine ⟨List.replicate n J, by simp, ?_, by simp⟩
    intro L hL
    simpa [family] using (List.mem_replicate.mp hL).2

theorem joint_bound (n : ℕ) : jointBound family n = n + 1 := by
  simp [jointBound, products_singleton, power_norm]

theorem root_growth_limit :
    Tendsto (fun n : ℕ => jointBound family n ^ (1 / (n : ℝ))) atTop (𝓝 1) := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
    exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have ht := (tendsto_rpow_div_mul_add 1 1 (-1) (by norm_num)).comp hnat
  convert ht using 1
  funext n
  rw [joint_bound]
  simp only [Function.comp_apply, one_mul]
  congr 1
  ring

theorem joint_radius_one : jointRadius family = 1 := root_growth_limit.limsup_eq

def Definite (N : Seminorm ℝ E) : Prop := ∀ x, N x = 0 → x = 0
def Extremal (K : Set Op) (r : ℝ) (N : Seminorm ℝ E) : Prop :=
  ∀ L ∈ K, ∀ x, N (L x) ≤ r * N x

theorem no_nonexpansive_norm (N : Seminorm ℝ E) (hd : Definite N) :
    ¬ ∀ x, N (J x) ≤ N x := by
  intro hJ
  have hnz : N e1 ≠ 0 := by
    intro hz
    have := hd e1 hz
    norm_num [e1] at this
  have hp : 0 < N e1 := lt_of_le_of_ne (apply_nonneg N e1) (Ne.symm hnz)
  have hpow (n : ℕ) : N ((J ^ n) e2) ≤ N e2 := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ', ContinuousLinearMap.mul_apply]
        exact (hJ _).trans ih
  have hbound (n : ℕ) : (n : ℝ) * N e1 ≤ 2 * N e2 := by
    have heq : (n : ℝ) • e1 = (J ^ n) e2 - e2 := by
      rw [power_apply]
      ext <;> simp [e1, e2]
    have htri := map_sub_le_add N ((J ^ n) e2) e2
    rw [← heq, map_smul_eq_mul] at htri
    simpa only [Real.norm_natCast] using htri.trans (by linarith [hpow n])
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * N e2 / N e1)
  have hstrict := (div_lt_iff₀ hp).mp hn
  linarith [hbound n]

theorem no_extremal_norm :
    ¬ ∃ N : Seminorm ℝ E, Definite N ∧ Extremal family (jointRadius family) N := by
  rintro ⟨N, hd, h⟩
  apply no_nonexpansive_norm N hd
  intro x
  simpa [joint_radius_one] using h J (by simp [family]) x

#print axioms matrix_action
#print axioms compact_family
#print axioms power_norm
#print axioms products_singleton
#print axioms root_growth_limit
#print axioms joint_radius_one
#print axioms no_nonexpansive_norm
#print axioms no_extremal_norm
end BarabanovCounterexample
