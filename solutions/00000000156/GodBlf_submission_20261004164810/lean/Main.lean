import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Topology.Instances.Real.Lemmas

namespace Conjecture156

open Matrix Filter
open scoped Topology

def SignMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  ∀ i j, A i j = 1 ∨ A i j = -1

theorem sign_difference_even (a b : ℤ)
    (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    a - b = 2 * ((a - b) / 2) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num

/-- Two row subtractions suffice for the uniform obstruction in every n >= 3. -/
theorem four_dvd_det {n : ℕ} (hn : 3 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℤ) (hA : SignMatrix A) : (4 : ℤ) ∣ A.det := by
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  let i2 : Fin n := ⟨2, by omega⟩
  have h10 : i1 ≠ i0 := by intro h; have := congrArg Fin.val h; norm_num [i1, i0] at this
  have h20 : i2 ≠ i0 := by intro h; have := congrArg Fin.val h; norm_num [i2, i0] at this
  have h21 : i2 ≠ i1 := by intro h; have := congrArg Fin.val h; norm_num [i2, i1] at this
  let u : Fin n → ℤ := fun j => (A i1 j - A i0 j) / 2
  let v : Fin n → ℤ := fun j => (A i2 j - A i0 j) / 2
  have hu : A i1 + (-1 : ℤ) • A i0 = (2 : ℤ) • u := by
    funext j
    simpa [u, Pi.add_apply, Pi.smul_apply, smul_eq_mul, sub_eq_add_neg] using
      sign_difference_even (A i1 j) (A i0 j) (hA i1 j) (hA i0 j)
  have hv : A i2 + (-1 : ℤ) • A i0 = (2 : ℤ) • v := by
    funext j
    simpa [v, Pi.add_apply, Pi.smul_apply, smul_eq_mul, sub_eq_add_neg] using
      sign_difference_even (A i2 j) (A i0 j) (hA i2 j) (hA i0 j)
  have hd1 := det_updateRow_add_smul_self A h10 (-1 : ℤ)
  rw [hu, det_updateRow_smul] at hd1
  let B := A.updateRow i1 u
  have hb0 : B i0 = A i0 := by exact updateRow_ne h10.symm
  have hb2 : B i2 = A i2 := by exact updateRow_ne h21
  have hd2 := det_updateRow_add_smul_self B h20 (-1 : ℤ)
  rw [hb0, hb2, hv, det_updateRow_smul] at hd2
  refine ⟨(B.updateRow i2 v).det, ?_⟩
  calc
    A.det = 2 * B.det := hd1.symm
    _ = 4 * (B.updateRow i2 v).det := by rw [← hd2]; ring

theorem no_prime_det {n : ℕ} (hn : 3 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℤ) (hA : SignMatrix A) :
    ¬ A.det.natAbs.Prime := by
  intro hp
  have h4 : 4 ∣ A.det.natAbs := Int.natCast_dvd.mp (four_dvd_det hn A hA)
  have h2 : 2 ∣ A.det.natAbs := dvd_trans (by norm_num : 2 ∣ 4) h4
  have heq : A.det.natAbs = 2 := by
    rcases hp.eq_one_or_self_of_dvd 2 h2 with h | h
    · norm_num at h
    · exact h.symm
  rw [heq] at h4
  norm_num at h4

/-- Each Boolean matrix encodes one equally likely sign matrix. -/
def sampleMatrix {n : ℕ} (s : Fin n → Fin n → Bool) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => if s i j then 1 else -1

theorem sample_sign {n : ℕ} (s : Fin n → Fin n → Bool) : SignMatrix (sampleMatrix s) := by
  intro i j
  simp only [sampleMatrix]
  split <;> simp

noncomputable def primeProbability (n : ℕ) : ℝ := by
  classical
  exact ((Finset.univ.filter (fun s : Fin n → Fin n → Bool =>
    (sampleMatrix s).det.natAbs.Prime)).card : ℝ) /
    (Fintype.card (Fin n → Fin n → Bool) : ℝ)

theorem probability_zero {n : ℕ} (hn : 3 ≤ n) : primeProbability n = 0 := by
  classical
  have h : (Finset.univ.filter (fun s : Fin n → Fin n → Bool =>
      (sampleMatrix s).det.natAbs.Prime)) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro s hs
    exact no_prime_det hn (sampleMatrix s) (sample_sign s) (Finset.mem_filter.mp hs).2
  simp [primeProbability, h]

/-- The actual ratio in the conjecture converges to zero for every constant c. -/
theorem ratio_tendsto_zero (c : ℝ) :
    Tendsto (fun n : ℕ => primeProbability n / (c / (n : ℝ))) atTop (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop 3] with n hn
  simp [probability_zero hn]

theorem not_asymptotic (c : ℝ) :
    ¬ Tendsto (fun n : ℕ => primeProbability n / (c / (n : ℝ))) atTop (𝓝 1) := by
  intro h
  have : (0 : ℝ) = 1 := tendsto_nhds_unique (ratio_tendsto_zero c) h
  norm_num at this

theorem conjecture_false : ¬ ∃ c : ℝ, 0 < c ∧
    Tendsto (fun n : ℕ => primeProbability n / (c / (n : ℝ))) atTop (𝓝 1) := by
  rintro ⟨c, _, h⟩
  exact not_asymptotic c h

end Conjecture156
