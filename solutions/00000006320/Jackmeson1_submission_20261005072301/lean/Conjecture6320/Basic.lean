import Mathlib

/-!
# Conjecture 00000006320

> Definition: The permanent lower bound and the support structure are two layers. Conjecture:
> There exist two matrix classes with the same lower-bound constant but different support
> structures, and the separation is realized by an explicit pair with the same constant but
> different support families.

## Reading

* A *matrix class* is a set `𝒞` of real `n × n` matrices.
* Its *permanent lower-bound constant* is the optimal constant `c` with `perm M ≥ c` for all
  `M ∈ 𝒞`, i.e. the infimum of `perm` over `𝒞`. We prove the stronger statement that it is a
  least element (`IsLeast`), so the optimal bound is also attained, and also compute `sInf`.
* The *support* of `M` is the set of positions `(i, j)` with `M i j ≠ 0`; the *support family* of a
  class is the set of supports of its members (its support structure).

## The explicit pair (n = 2)

* `Ω₂ = doublyStochastic ℝ (Fin 2)` (Mathlib's doubly stochastic matrices), and
* `Ω₂⁺ = {M ∈ Ω₂ | all entries > 0}` (positive doubly stochastic matrices).

Both have permanent lower-bound constant `1/2 = 2!/2²` (the van der Waerden bound for `n = 2`),
attained at `J₂/2` (all entries `1/2`). Their support families differ: `Ω₂` contains the identity
(support = diagonal) and the swap matrix (support = anti-diagonal), whereas every member of `Ω₂⁺`
has full support. We compute both support families exactly.
-/

namespace Conjecture6320

open Matrix Finset

/-- The permanent lower-bound constant of a matrix class: the infimum of the permanent. -/
noncomputable def lbConst {n : Type*} [Fintype n] [DecidableEq n] (𝒞 : Set (Matrix n n ℝ)) : ℝ :=
  sInf (permanent '' 𝒞)

/-- Support of a matrix: the positions of its nonzero entries. -/
def supp {n : Type*} (M : Matrix n n ℝ) : Set (n × n) := {p | M p.1 p.2 ≠ 0}

/-- Support family (support structure) of a class. -/
def suppFamily {n : Type*} (𝒞 : Set (Matrix n n ℝ)) : Set (Set (n × n)) := supp '' 𝒞

/-- `Ω₂`: the 2 × 2 doubly stochastic matrices. -/
def Omega2 : Set (Matrix (Fin 2) (Fin 2) ℝ) := doublyStochastic ℝ (Fin 2)

/-- `Ω₂⁺`: the 2 × 2 doubly stochastic matrices with all entries positive. -/
def Omega2pos : Set (Matrix (Fin 2) (Fin 2) ℝ) := {M | M ∈ Omega2 ∧ ∀ i j, 0 < M i j}

theorem permanent_fin_two (M : Matrix (Fin 2) (Fin 2) ℝ) :
    permanent M = M 0 0 * M 1 1 + M 1 0 * M 0 1 := by
  have huniv : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by decide
  rw [permanent, huniv, Finset.sum_pair (by decide)]
  simp [Fin.prod_univ_two, Equiv.swap_apply_left, Equiv.swap_apply_right]

/-- Every `M ∈ Ω₂` has the form `[[a, 1-a], [1-a, a]]` with `a = M 0 0` (the three entry
identities below; the bounds `0 ≤ a ≤ 1` are `Omega2_bounds`). -/
theorem Omega2_form {M : Matrix (Fin 2) (Fin 2) ℝ} (hM : M ∈ Omega2) :
    M 0 1 = 1 - M 0 0 ∧ M 1 0 = 1 - M 0 0 ∧ M 1 1 = M 0 0 := by
  rw [Omega2, SetLike.mem_coe, mem_doublyStochastic_iff_sum] at hM
  obtain ⟨-, hr, hc⟩ := hM
  have r0 := hr 0; have r1 := hr 1; have c0 := hc 0
  simp only [Fin.sum_univ_two] at r0 r1 c0
  refine ⟨by linarith, by linarith, by linarith⟩

/-- For `M ∈ Ω₂`, the parameter `a = M 0 0` satisfies `0 ≤ a ≤ 1`. -/
theorem Omega2_bounds {M : Matrix (Fin 2) (Fin 2) ℝ} (hM : M ∈ Omega2) :
    0 ≤ M 0 0 ∧ M 0 0 ≤ 1 := by
  have hnn := ((mem_doublyStochastic_iff_sum).1 hM).1
  obtain ⟨h01, -, -⟩ := Omega2_form hM
  have := hnn 0 1
  exact ⟨hnn 0 0, by linarith⟩

/-- On `Ω₂`, `perm M = a² + (1-a)²` with `a = M 0 0`. -/
theorem perm_eq {M : Matrix (Fin 2) (Fin 2) ℝ} (hM : M ∈ Omega2) :
    permanent M = M 0 0 ^ 2 + (1 - M 0 0) ^ 2 := by
  obtain ⟨h01, h10, h11⟩ := Omega2_form hM
  rw [permanent_fin_two, h01, h10, h11]
  ring

/-- On `Ω₂`, `perm M ≥ 1/2`. -/
theorem perm_ge_half {M : Matrix (Fin 2) (Fin 2) ℝ} (hM : M ∈ Omega2) : 1 / 2 ≤ permanent M := by
  rw [perm_eq hM]
  nlinarith [sq_nonneg (M 0 0 - 1 / 2)]

/-- On `Ω₂`, equality `perm M = 1/2` holds exactly when `M 0 0 = 1/2`. -/
theorem perm_eq_half_iff {M : Matrix (Fin 2) (Fin 2) ℝ} (hM : M ∈ Omega2) :
    permanent M = 1 / 2 ↔ M 0 0 = 1 / 2 := by
  rw [perm_eq hM]
  constructor
  · intro h
    have hsq : (M 0 0 - 1 / 2) ^ 2 = 0 := by nlinarith
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hsq
    linarith
  · intro h; rw [h]; norm_num

/-- `J₂/2`, the matrix with all entries `1/2`. -/
noncomputable def Jhalf : Matrix (Fin 2) (Fin 2) ℝ := fun _ _ => 1 / 2

theorem Jhalf_mem_pos : Jhalf ∈ Omega2pos := by
  refine ⟨?_, fun _ _ => by norm_num [Jhalf]⟩
  rw [Omega2, SetLike.mem_coe, mem_doublyStochastic_iff_sum]
  refine ⟨fun _ _ => by norm_num [Jhalf], fun _ => ?_, fun _ => ?_⟩ <;> simp [Jhalf]

theorem perm_Jhalf : permanent Jhalf = 1 / 2 := by
  rw [permanent_fin_two]; norm_num [Jhalf]

theorem Omega2pos_subset : Omega2pos ⊆ Omega2 := fun _ h => h.1

/-- `1/2` is the least permanent on `Ω₂` (optimal and attained lower bound). -/
theorem isLeast_Omega2 : IsLeast (permanent '' Omega2) (1 / 2) :=
  ⟨⟨Jhalf, Omega2pos_subset Jhalf_mem_pos, perm_Jhalf⟩, by
    rintro _ ⟨M, hM, rfl⟩; exact perm_ge_half hM⟩

/-- `1/2` is the least permanent on `Ω₂⁺` (optimal and attained lower bound). -/
theorem isLeast_Omega2pos : IsLeast (permanent '' Omega2pos) (1 / 2) :=
  ⟨⟨Jhalf, Jhalf_mem_pos, perm_Jhalf⟩, by
    rintro _ ⟨M, hM, rfl⟩; exact perm_ge_half hM.1⟩

theorem lbConst_Omega2 : lbConst Omega2 = 1 / 2 := isLeast_Omega2.csInf_eq

theorem lbConst_Omega2pos : lbConst Omega2pos = 1 / 2 := isLeast_Omega2pos.csInf_eq

/-- The diagonal and anti-diagonal supports. -/
def diagSupp : Set (Fin 2 × Fin 2) := {p | p.1 = p.2}
def antiSupp : Set (Fin 2 × Fin 2) := {p | p.1 ≠ p.2}

/-- The swap (anti-diagonal permutation) matrix. -/
def swapM : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

theorem one_mem : (1 : Matrix (Fin 2) (Fin 2) ℝ) ∈ Omega2 := (doublyStochastic ℝ (Fin 2)).one_mem

theorem swapM_mem : swapM ∈ Omega2 := by
  rw [Omega2, SetLike.mem_coe, mem_doublyStochastic_iff_sum]
  refine ⟨fun i j => ?_, fun i => ?_, fun j => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [swapM]
  · fin_cases i <;> simp [swapM, Fin.sum_univ_two]
  · fin_cases j <;> simp [swapM, Fin.sum_univ_two]

theorem supp_one : supp (1 : Matrix (Fin 2) (Fin 2) ℝ) = diagSupp := by
  ext ⟨i, j⟩; fin_cases i <;> fin_cases j <;> simp [supp, diagSupp]

theorem supp_swapM : supp swapM = antiSupp := by
  ext ⟨i, j⟩; fin_cases i <;> fin_cases j <;> simp [supp, antiSupp, swapM]

/-- Exact support family of `Ω₂⁺`: only the full support. -/
theorem suppFamily_Omega2pos : suppFamily Omega2pos = {Set.univ} := by
  ext S
  simp only [suppFamily, Set.mem_image, Set.mem_singleton_iff]
  constructor
  · rintro ⟨M, hM, rfl⟩
    ext p; simpa [supp] using (hM.2 p.1 p.2).ne'
  · rintro rfl
    exact ⟨Jhalf, Jhalf_mem_pos, by ext p; simp [supp, Jhalf]⟩

/-- Exact support family of `Ω₂`: diagonal, anti-diagonal, or full. -/
theorem suppFamily_Omega2 : suppFamily Omega2 = {diagSupp, antiSupp, Set.univ} := by
  ext S
  simp only [suppFamily, Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨M, hM, rfl⟩
    obtain ⟨h01, h10, h11⟩ := Omega2_form hM
    by_cases h0 : M 0 0 = 0
    · right; left
      ext ⟨i, j⟩; fin_cases i <;> fin_cases j <;> simp [supp, antiSupp, h01, h10, h11, h0]
    · by_cases h1 : M 0 0 = 1
      · left
        ext ⟨i, j⟩; fin_cases i <;> fin_cases j <;> simp [supp, diagSupp, h01, h10, h11, h1]
      · right; right
        have h1' : 1 - M 0 0 ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
        ext ⟨i, j⟩; fin_cases i <;> fin_cases j <;> simp [supp, h01, h10, h11, h0, h1']
  · rintro (rfl | rfl | rfl)
    · exact ⟨1, one_mem, supp_one⟩
    · exact ⟨swapM, swapM_mem, supp_swapM⟩
    · exact ⟨Jhalf, Omega2pos_subset Jhalf_mem_pos, by ext p; simp [supp, Jhalf]⟩

theorem diagSupp_ne_univ : diagSupp ≠ Set.univ := by
  intro h
  have : ((0 : Fin 2), (1 : Fin 2)) ∈ diagSupp := h ▸ Set.mem_univ _
  simp [diagSupp] at this

/-- **Main theorem.** The explicit pair of matrix classes `Ω₂` and `Ω₂⁺` has the same permanent
lower-bound constant `1/2 = 2!/2²` (optimal and attained in both classes) but different support
families; the identity matrix realizes a support (the diagonal) present in `Ω₂` and absent from
`Ω₂⁺`. -/
theorem separation :
    IsLeast (permanent '' Omega2) (1 / 2) ∧ IsLeast (permanent '' Omega2pos) (1 / 2) ∧
    lbConst Omega2 = lbConst Omega2pos ∧
    suppFamily Omega2 ≠ suppFamily Omega2pos ∧
    (1 : Matrix (Fin 2) (Fin 2) ℝ) ∈ Omega2 ∧ supp (1 : Matrix (Fin 2) (Fin 2) ℝ) ∈ suppFamily Omega2 ∧
      supp (1 : Matrix (Fin 2) (Fin 2) ℝ) ∉ suppFamily Omega2pos := by
  have hnot : supp (1 : Matrix (Fin 2) (Fin 2) ℝ) ∉ suppFamily Omega2pos := by
    rw [suppFamily_Omega2pos, supp_one, Set.mem_singleton_iff]; exact diagSupp_ne_univ
  refine ⟨isLeast_Omega2, isLeast_Omega2pos, by rw [lbConst_Omega2, lbConst_Omega2pos], ?_, one_mem,
    ⟨1, one_mem, rfl⟩, hnot⟩
  intro h
  exact hnot (h ▸ ⟨1, one_mem, rfl⟩)

/-- The common constant equals the van der Waerden value `n!/nⁿ` for `n = 2`. -/
theorem const_eq_vdW : lbConst Omega2 = (Nat.factorial 2 : ℝ) / 2 ^ 2 := by
  rw [lbConst_Omega2]; norm_num [Nat.factorial]

end Conjecture6320
