import Mathlib

/-!
# Conjecture 00000008338: the optimal Siegel constant is not `(nH)^{m/(n-m)}`

The conjecture's Definition line names `sieg_c` as the height upper bound of minimal
solutions of integer linear systems, and its first clause says that this optimal constant
equals `(nH)^{m/(n-m)}`.

We formalize, for an `m × n` system with integer coefficients not all `0` and bounded by `H`:
* the height of an integer vector (sup norm) and of an integer matrix (largest `|a_ij|`);
* `minSolHeight A`, the least height of a nonzero integer solution `x` of `A x = 0`;
* `siegC m n H`, the supremum of `minSolHeight A` over all admissible `A`;
* `bvValue m n H = (n * H)^(m / (n - m))` (real power).

At `(m, n) = (1, 2)` and every `H ≥ 1` we prove `siegC 1 2 H = H`, that `H` is the least real
upper bound of the minimal-solution heights, and that `bvValue 1 2 H = 2 * H`. So the
claimed value is wrong for every `H ≥ 1`, and no admissible `1 × 2` system has a minimal
solution of height `bvValue 1 2 H`.
-/

namespace Conjecture8338

open Matrix

/-- Height of an integer vector: `max_i |x_i|` (sup norm). -/
def vecHeight {n : ℕ} (x : Fin n → ℤ) : ℕ :=
  Finset.univ.sup fun i => (x i).natAbs

/-- Height of an integer matrix: `max_{i,j} |a_ij|`. -/
def matHeight {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) : ℕ :=
  Finset.univ.sup fun p : Fin m × Fin n => (A p.1 p.2).natAbs

/-- Heights of the nonzero integer solutions `x` of the homogeneous system `A x = 0`. -/
def kerHeights {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) : Set ℕ :=
  {h | ∃ x : Fin n → ℤ, x ≠ 0 ∧ A *ᵥ x = 0 ∧ vecHeight x = h}

/-- Height of a minimal solution: the least height of a nonzero integer solution of `A x = 0`
(`sInf` on `ℕ`; we only use it where solutions exist). -/
noncomputable def minSolHeight {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) : ℕ :=
  sInf (kerHeights A)

/-- Admissible systems: `m × n`, integer coefficients, not all `0`, bounded by `H`. -/
def Admissible {m n : ℕ} (H : ℕ) (A : Matrix (Fin m) (Fin n) ℤ) : Prop :=
  A ≠ 0 ∧ matHeight A ≤ H

/-- Minimal-solution heights of all admissible `m × n` systems with coefficients bounded by `H`. -/
def siegValues (m n H : ℕ) : Set ℕ :=
  {h | ∃ A : Matrix (Fin m) (Fin n) ℤ, Admissible H A ∧ minSolHeight A = h}

/-- `sieg_c(m, n, H)`: the height upper bound of minimal solutions, i.e. the supremum of the
minimal-solution heights over all admissible systems. -/
noncomputable def siegC (m n H : ℕ) : ℕ :=
  sSup (siegValues m n H)

/-- The conjectured explicit value `(n H)^{m/(n-m)}` (real power). -/
noncomputable def bvValue (m n H : ℕ) : ℝ :=
  ((n : ℝ) * H) ^ ((m : ℝ) / ((n : ℝ) - m))

/-! ### Basic facts about heights -/

lemma natAbs_le_vecHeight {n : ℕ} (x : Fin n → ℤ) (i : Fin n) :
    (x i).natAbs ≤ vecHeight x :=
  Finset.le_sup (f := fun i => (x i).natAbs) (Finset.mem_univ i)

lemma vecHeight_le_iff {n : ℕ} (x : Fin n → ℤ) (H : ℕ) :
    vecHeight x ≤ H ↔ ∀ i, (x i).natAbs ≤ H := by
  simp [vecHeight, Finset.sup_le_iff]

lemma natAbs_le_matHeight {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (i : Fin m) (j : Fin n) :
    (A i j).natAbs ≤ matHeight A :=
  Finset.le_sup (f := fun p : Fin m × Fin n => (A p.1 p.2).natAbs) (Finset.mem_univ (i, j))

lemma matHeight_le_iff {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (H : ℕ) :
    matHeight A ≤ H ↔ ∀ i j, (A i j).natAbs ≤ H := by
  simp [matHeight, Finset.sup_le_iff]

/-- For a `1 × 2` system, `A x = 0` is the single equation `a x₀ + b x₁ = 0`. -/
lemma mulVec_eq_zero_iff (A : Matrix (Fin 1) (Fin 2) ℤ) (x : Fin 2 → ℤ) :
    A *ᵥ x = 0 ↔ A 0 0 * x 0 + A 0 1 * x 1 = 0 := by
  constructor
  · intro h
    have := congrFun h 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  · intro h
    funext i
    fin_cases i
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h

/-! ### Upper bound: every admissible `1 × 2` system has a solution of height `≤ H` -/

/-- Every `1 × 2` integer system with coefficients bounded by `H ≥ 1` has a nonzero integer
solution of height at most `H`: `(b, -a)` if `(a, b) ≠ 0`, and `(1, 0)` otherwise. -/
theorem exists_kerHeight_le (A : Matrix (Fin 1) (Fin 2) ℤ) (H : ℕ) (hH : 1 ≤ H)
    (hA : matHeight A ≤ H) : ∃ h ∈ kerHeights A, h ≤ H := by
  rw [matHeight_le_iff] at hA
  by_cases h0 : A 0 0 = 0 ∧ A 0 1 = 0
  · refine ⟨vecHeight ![1, 0], ⟨![1, 0], ?_, ?_, rfl⟩, ?_⟩
    · intro h
      have := congrFun h 0
      simp at this
    · rw [mulVec_eq_zero_iff]
      simp [h0.1, h0.2]
    · rw [vecHeight_le_iff]
      intro i
      fin_cases i <;> simp [hH]
  · refine ⟨vecHeight ![A 0 1, -A 0 0], ⟨![A 0 1, -A 0 0], ?_, ?_, rfl⟩, ?_⟩
    · intro h
      apply h0
      have h1 := congrFun h 0
      have h2 := congrFun h 1
      simp at h1 h2
      exact ⟨h2, h1⟩
    · rw [mulVec_eq_zero_iff]
      simp
      ring
    · rw [vecHeight_le_iff]
      intro i
      fin_cases i
      · simpa using hA 0 1
      · simpa using hA 0 0

/-- Every admissible `1 × 2` system has nonzero integer solutions. -/
theorem kerHeights_nonempty (A : Matrix (Fin 1) (Fin 2) ℤ) (H : ℕ) (hH : 1 ≤ H)
    (hA : matHeight A ≤ H) : (kerHeights A).Nonempty := by
  obtain ⟨h, hh, -⟩ := exists_kerHeight_le A H hH hA
  exact ⟨h, hh⟩

/-- The minimal solution of every `1 × 2` system with coefficients bounded by `H ≥ 1` has
height at most `H`. -/
theorem minSolHeight_le (A : Matrix (Fin 1) (Fin 2) ℤ) (H : ℕ) (hH : 1 ≤ H)
    (hA : matHeight A ≤ H) : minSolHeight A ≤ H := by
  obtain ⟨h, hh, hle⟩ := exists_kerHeight_le A H hH hA
  exact le_trans (Nat.sInf_le hh) hle

/-! ### Lower bound: the system `H x₀ + (H - 1) x₁ = 0` -/

/-- The `1 × 2` system with coefficient row `(H, H - 1)`. -/
def witnessMatrix (H : ℕ) : Matrix (Fin 1) (Fin 2) ℤ :=
  !![(H : ℤ), (H : ℤ) - 1]

lemma witnessMatrix_admissible (H : ℕ) (hH : 1 ≤ H) : Admissible H (witnessMatrix H) := by
  refine ⟨?_, ?_⟩
  · intro h
    have := congrFun (congrFun h 0) 0
    simp [witnessMatrix] at this
    omega
  · rw [matHeight_le_iff]
    intro i j
    fin_cases i
    fin_cases j
    · simp [witnessMatrix]
    · simp [witnessMatrix]
      omega

/-- Every nonzero integer solution of `H x₀ + (H - 1) x₁ = 0` has height at least `H`:
the equation says `x₁ = H (x₀ + x₁)`, and `x₁ ≠ 0`. -/
theorem le_vecHeight_of_witness (H : ℕ) (hH : 1 ≤ H) (x : Fin 2 → ℤ) (hx : x ≠ 0)
    (hk : witnessMatrix H *ᵥ x = 0) : H ≤ vecHeight x := by
  rw [mulVec_eq_zero_iff] at hk
  simp [witnessMatrix] at hk
  have hx1 : x 1 = (H : ℤ) * (x 0 + x 1) := by linarith
  have hne : x 1 ≠ 0 := by
    intro h1
    apply hx
    funext i
    fin_cases i
    · have : (H : ℤ) * x 0 = 0 := by rw [h1] at hk; simpa using hk
      have hHpos : (H : ℤ) ≠ 0 := by exact_mod_cast (by omega : H ≠ 0)
      simpa using (mul_eq_zero.mp this).resolve_left hHpos
    · simpa using h1
  have hdvd : (H : ℤ) ∣ x 1 := ⟨x 0 + x 1, hx1⟩
  have h1 : H ≤ (x 1).natAbs := by
    have := Int.natAbs_dvd_natAbs.mpr hdvd
    simpa using Nat.le_of_dvd (Int.natAbs_pos.mpr hne) this
  exact le_trans h1 (natAbs_le_vecHeight x 1)

/-- The minimal solution of `H x₀ + (H - 1) x₁ = 0` has height exactly `H`. -/
theorem minSolHeight_witness (H : ℕ) (hH : 1 ≤ H) : minSolHeight (witnessMatrix H) = H := by
  apply le_antisymm
  · exact minSolHeight_le _ H hH (witnessMatrix_admissible H hH).2
  · apply le_csInf (kerHeights_nonempty _ H hH (witnessMatrix_admissible H hH).2)
    rintro h ⟨x, hx, hk, rfl⟩
    exact le_vecHeight_of_witness H hH x hx hk

/-! ### The sharp value of `sieg_c(1, 2, H)` -/

/-- `H` is the largest minimal-solution height among admissible `1 × 2` systems. -/
theorem isGreatest_siegValues (H : ℕ) (hH : 1 ≤ H) : IsGreatest (siegValues 1 2 H) H := by
  refine ⟨⟨witnessMatrix H, witnessMatrix_admissible H hH, minSolHeight_witness H hH⟩, ?_⟩
  rintro h ⟨A, hA, rfl⟩
  exact minSolHeight_le A H hH hA.2

/-- `sieg_c(1, 2, H) = H` for every `H ≥ 1`. -/
theorem siegC_one_two (H : ℕ) (hH : 1 ≤ H) : siegC 1 2 H = H :=
  (isGreatest_siegValues H hH).csSup_eq

/-- `H` is also the least real number bounding the minimal-solution heights of all admissible
`1 × 2` systems (the optimal constant, taken over the reals). -/
theorem isLeast_real_bound (H : ℕ) (hH : 1 ≤ H) :
    IsLeast {B : ℝ | ∀ A : Matrix (Fin 1) (Fin 2) ℤ, Admissible H A → (minSolHeight A : ℝ) ≤ B}
      (H : ℝ) := by
  refine ⟨fun A hA => by exact_mod_cast minSolHeight_le A H hH hA.2, ?_⟩
  intro B hB
  have := hB (witnessMatrix H) (witnessMatrix_admissible H hH)
  rwa [minSolHeight_witness H hH] at this

/-- The conjectured value at `(m, n) = (1, 2)`: `(2 H)^{1/(2-1)} = 2 H`. -/
theorem bvValue_one_two (H : ℕ) : bvValue 1 2 H = 2 * H := by
  simp [bvValue]
  norm_num

/-! ### Refutation -/

/-- No admissible `1 × 2` system (random or not) has a minimal solution of height
`(nH)^{m/(n-m)} = 2H`: every minimal-solution height is `< 2H`. -/
theorem minSolHeight_lt_bvValue (H : ℕ) (hH : 1 ≤ H) (A : Matrix (Fin 1) (Fin 2) ℤ)
    (hA : Admissible H A) : (minSolHeight A : ℝ) < bvValue 1 2 H := by
  rw [bvValue_one_two]
  have h1 : (minSolHeight A : ℝ) ≤ H := by exact_mod_cast minSolHeight_le A H hH hA.2
  have h2 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  linarith

/-- **Main theorem.** For every `H ≥ 1`, the optimal Siegel constant for `1 × 2` systems with
coefficients bounded by `H` is `sieg_c(1, 2, H) = H`, which is strictly smaller than the
claimed value `(nH)^{m/(n-m)} = 2H`; no admissible system attains `2H`. -/
theorem conjecture8338_false (H : ℕ) (hH : 1 ≤ H) :
    siegC 1 2 H = H ∧ (siegC 1 2 H : ℝ) < bvValue 1 2 H ∧ (siegC 1 2 H : ℝ) ≠ bvValue 1 2 H ∧
      ∀ A : Matrix (Fin 1) (Fin 2) ℤ, Admissible H A → (minSolHeight A : ℝ) ≠ bvValue 1 2 H := by
  have hlt : (siegC 1 2 H : ℝ) < bvValue 1 2 H := by
    rw [siegC_one_two H hH, bvValue_one_two]
    have h2 : (1 : ℝ) ≤ H := by exact_mod_cast hH
    linarith
  exact ⟨siegC_one_two H hH, hlt, hlt.ne,
    fun A hA => (minSolHeight_lt_bvValue H hH A hA).ne⟩

/-- The general law `sieg_c(m, n, H) = (nH)^{m/(n-m)}` for all `0 < m < n` and `H ≥ 1` fails. -/
theorem not_siegC_eq_bvValue :
    ¬ ∀ m n H : ℕ, 0 < m → m < n → 1 ≤ H → (siegC m n H : ℝ) = bvValue m n H := by
  intro h
  exact (conjecture8338_false 1 le_rfl).2.2.1 (h 1 2 1 one_pos one_lt_two le_rfl)

end Conjecture8338
