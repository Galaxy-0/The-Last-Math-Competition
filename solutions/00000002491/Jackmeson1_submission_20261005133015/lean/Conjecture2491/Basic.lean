import Mathlib

/-!
# Conjecture 00000002491 (disproof)

Conjecture (verbatim): "The Möbius function of the partition lattice is governed by squarefree
partitions: the inversion formula closes on partitions without repeated parts, and the Möbius
values vanish otherwise."

Reading refuted here: in the partition lattice `Π_n` of set partitions of an `n`-set (ordered by
refinement, `0̂` = partition into singletons), `μ(0̂, σ) = 0` whenever two distinct blocks of `σ`
have the same size.  We work in Mathlib's `Finpartition (univ : Finset (Fin 4))` with its
refinement order and Mathlib's Möbius function `IncidenceAlgebra.mu`, and show that
`σ = {01 | 23}` (two blocks of size 2) has `μ(0̂, σ) = 1 ≠ 0`.
-/

open Finset

namespace C2491

/-- The partition lattice `Π₄`: Mathlib's finite partitions of `Fin 4`, ordered by refinement
(`P ≤ Q` iff every block of `P` lies in a block of `Q`). -/
abbrev Pi4 := Finpartition (univ : Finset (Fin 4))

/-- `Π₄` is finite, hence locally finite (needed for the incidence algebra). -/
noncomputable instance : LocallyFiniteOrder Pi4 := by
  classical exact Fintype.toLocallyFiniteOrder

/-- The partition `{0,1 | 2,3}`. -/
def sigma : Pi4 where
  parts := {{0, 1}, {2, 3}}
  supIndep := by rw [Finset.supIndep_iff_disjoint_erase]; decide
  sup_parts := by decide
  bot_notMem := by decide

/-- The partition `{0,1 | 2 | 3}`. -/
def p1 : Pi4 where
  parts := {{0, 1}, {2}, {3}}
  supIndep := by rw [Finset.supIndep_iff_disjoint_erase]; decide
  sup_parts := by decide
  bot_notMem := by decide

/-- The partition `{0 | 1 | 2,3}`. -/
def p2 : Pi4 where
  parts := {{0}, {1}, {2, 3}}
  supIndep := by rw [Finset.supIndep_iff_disjoint_erase]; decide
  sup_parts := by decide
  bot_notMem := by decide

lemma bot_parts : (⊥ : Pi4).parts = {{0}, {1}, {2}, {3}} := by
  rw [Finpartition.parts_bot]; decide

/-! ### Blocks via `Finpartition.part` -/

/-- Every partition of `Fin 4` is determined by the blocks of its four points. -/
lemma parts_eq (x : Pi4) : x.parts = {x.part 0, x.part 1, x.part 2, x.part 3} := by
  ext t
  constructor
  · intro ht
    obtain ⟨a, ha⟩ := x.nonempty_of_mem_parts ht
    have h := x.part_eq_of_mem ht ha
    fin_cases a <;> simp_all
  · intro ht
    simp only [mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl <;> exact x.part_mem.2 (mem_univ _)

/-- Refinement in terms of blocks of points. -/
lemma le_iff (x y : Pi4) : x ≤ y ↔ ∀ a, x.part a ⊆ y.part a := by
  constructor
  · intro h a
    obtain ⟨c, hc, hxc⟩ := h (x.part_mem.2 (mem_univ a))
    rwa [y.part_eq_of_mem hc (hxc (x.mem_part (mem_univ a)))]
  · intro h b hb
    obtain ⟨a, ha⟩ := x.nonempty_of_mem_parts hb
    refine ⟨y.part a, y.part_mem.2 (mem_univ a), ?_⟩
    rw [← x.part_eq_of_mem hb ha]
    exact h a

lemma ext_part {x y : Pi4} (h : ∀ a, x.part a = y.part a) : x = y := by
  ext1; rw [parts_eq x, parts_eq y, h 0, h 1, h 2, h 3]

/-- Two points whose blocks both lie inside `{a, b}`: either both are singletons or both
blocks equal `{a, b}`. -/
lemma pair_cases (x : Pi4) {a b : Fin 4} (hab : a ≠ b) (ha : x.part a ⊆ {a, b})
    (hb : x.part b ⊆ {a, b}) :
    (x.part a = {a} ∧ x.part b = {b}) ∨ (x.part a = {a, b} ∧ x.part b = {a, b}) := by
  have ma : a ∈ x.part a := x.mem_part (mem_univ a)
  have mb : b ∈ x.part b := x.mem_part (mem_univ b)
  by_cases hba : b ∈ x.part a
  · have e : x.part b = x.part a := x.part_eq_of_mem (x.part_mem.2 (mem_univ a)) hba
    have ea : x.part a = {a, b} := by
      apply Subset.antisymm ha
      intro y hy
      simp only [mem_insert, mem_singleton] at hy
      rcases hy with rfl | rfl <;> assumption
    exact Or.inr ⟨ea, e.trans ea⟩
  · have hab' : a ∉ x.part b := by
      intro h
      have e : x.part a = x.part b := x.part_eq_of_mem (x.part_mem.2 (mem_univ b)) h
      exact hba (e ▸ mb)
    refine Or.inl ⟨?_, ?_⟩
    · ext y; constructor
      · intro hy
        have := ha hy
        simp only [mem_insert, mem_singleton] at this ⊢
        rcases this with rfl | rfl
        · rfl
        · exact absurd hy hba
      · intro hy; rw [mem_singleton] at hy; exact hy ▸ ma
    · ext y; constructor
      · intro hy
        have := hb hy
        simp only [mem_insert, mem_singleton] at this ⊢
        rcases this with rfl | rfl
        · exact absurd hy hab'
        · rfl
      · intro hy; rw [mem_singleton] at hy; exact hy ▸ mb

lemma part_of (x : Pi4) {t : Finset (Fin 4)} (ht : t ∈ x.parts) {a : Fin 4} (ha : a ∈ t) :
    x.part a = t := x.part_eq_of_mem ht ha

/-! ### The interval `[0̂, σ]` has exactly four elements -/

lemma sigma_part (a : Fin 4) : sigma.part a = if a.val < 2 then {0, 1} else {2, 3} := by
  fin_cases a <;> simp <;> apply part_of <;> decide

lemma le_sigma_cases (x : Pi4) (h : x ≤ sigma) : x = ⊥ ∨ x = p1 ∨ x = p2 ∨ x = sigma := by
  rw [le_iff] at h
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
  simp only [sigma_part] at h0 h1 h2 h3
  simp at h0 h1 h2 h3
  rcases pair_cases x (by decide : (0 : Fin 4) ≠ 1) h0 h1 with ⟨e0, e1⟩ | ⟨e0, e1⟩ <;>
  rcases pair_cases x (by decide : (2 : Fin 4) ≠ 3) h2 h3 with ⟨e2, e3⟩ | ⟨e2, e3⟩
  · left; ext1; rw [parts_eq x, e0, e1, e2, e3, bot_parts]
  · right; right; left; ext1; rw [parts_eq x, e0, e1, e2, e3]; decide
  · right; left; ext1; rw [parts_eq x, e0, e1, e2, e3]; decide
  · right; right; right; ext1; rw [parts_eq x, e0, e1, e2, e3]; decide

/-! ### Order relations among the four elements (decided on the explicit blocks) -/

lemma p1_le_sigma : p1 ≤ sigma := by
  show ∀ ⦃b⦄, b ∈ p1.parts → ∃ c ∈ sigma.parts, b ≤ c; decide
lemma p2_le_sigma : p2 ≤ sigma := by
  show ∀ ⦃b⦄, b ∈ p2.parts → ∃ c ∈ sigma.parts, b ≤ c; decide
lemma not_sigma_le_p1 : ¬ sigma ≤ p1 := by
  show ¬ ∀ ⦃b⦄, b ∈ sigma.parts → ∃ c ∈ p1.parts, b ≤ c; decide
lemma not_sigma_le_p2 : ¬ sigma ≤ p2 := by
  show ¬ ∀ ⦃b⦄, b ∈ sigma.parts → ∃ c ∈ p2.parts, b ≤ c; decide
lemma not_p2_le_p1 : ¬ p2 ≤ p1 := by
  show ¬ ∀ ⦃b⦄, b ∈ p2.parts → ∃ c ∈ p1.parts, b ≤ c; decide
lemma not_p1_le_p2 : ¬ p1 ≤ p2 := by
  show ¬ ∀ ⦃b⦄, b ∈ p1.parts → ∃ c ∈ p2.parts, b ≤ c; decide
lemma not_p1_le_bot : ¬ p1 ≤ ⊥ := by
  show ¬ ∀ ⦃b⦄, b ∈ p1.parts → ∃ c ∈ (⊥ : Pi4).parts, b ≤ c; rw [bot_parts]; decide
lemma not_p2_le_bot : ¬ p2 ≤ ⊥ := by
  show ¬ ∀ ⦃b⦄, b ∈ p2.parts → ∃ c ∈ (⊥ : Pi4).parts, b ≤ c; rw [bot_parts]; decide

lemma bot_ne_sigma : (⊥ : Pi4) ≠ sigma := fun h => not_sigma_le_p1 (h ▸ bot_le)
lemma bot_ne_p1 : (⊥ : Pi4) ≠ p1 := fun h => not_p1_le_bot (h ▸ le_rfl)
lemma bot_ne_p2 : (⊥ : Pi4) ≠ p2 := fun h => not_p2_le_bot (h ▸ le_rfl)
lemma p1_ne_p2 : p1 ≠ p2 := fun h => not_p1_le_p2 (h ▸ le_rfl)

/-- The interval `[0̂, σ)` is `{0̂, {01|2|3}, {0|1|23}}`. -/
lemma Ico_bot_sigma : Ico (⊥ : Pi4) sigma = {⊥, p1, p2} := by
  ext x
  simp only [mem_Ico, mem_insert, mem_singleton]
  constructor
  · rintro ⟨-, hx⟩
    rcases le_sigma_cases x hx.le with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact absurd h hx.ne
  · rintro (rfl | rfl | rfl)
    · exact ⟨le_rfl, bot_le.lt_of_ne bot_ne_sigma⟩
    · exact ⟨bot_le, p1_le_sigma.lt_of_ne fun h => not_sigma_le_p1 (h ▸ le_rfl)⟩
    · exact ⟨bot_le, p2_le_sigma.lt_of_ne fun h => not_sigma_le_p2 (h ▸ le_rfl)⟩

/-- The interval `[0̂, {01|2|3})` is `{0̂}`. -/
lemma Ico_bot_p1 : Ico (⊥ : Pi4) p1 = {⊥} := by
  ext x
  simp only [mem_Ico, mem_singleton]
  constructor
  · rintro ⟨-, hx⟩
    rcases le_sigma_cases x (hx.le.trans p1_le_sigma) with h | h | h | h
    · exact h
    · exact absurd h hx.ne
    · exact absurd (h ▸ hx.le) not_p2_le_p1
    · exact absurd (h ▸ hx.le) not_sigma_le_p1
  · rintro rfl; exact ⟨le_rfl, bot_le.lt_of_ne bot_ne_p1⟩

/-- The interval `[0̂, {0|1|23})` is `{0̂}`. -/
lemma Ico_bot_p2 : Ico (⊥ : Pi4) p2 = {⊥} := by
  ext x
  simp only [mem_Ico, mem_singleton]
  constructor
  · rintro ⟨-, hx⟩
    rcases le_sigma_cases x (hx.le.trans p2_le_sigma) with h | h | h | h
    · exact h
    · exact absurd (h ▸ hx.le) not_p1_le_p2
    · exact absurd h hx.ne
    · exact absurd (h ▸ hx.le) not_sigma_le_p2
  · rintro rfl; exact ⟨le_rfl, bot_le.lt_of_ne bot_ne_p2⟩

/-! ### The Möbius values -/

open IncidenceAlgebra

lemma mu_bot_p1 : mu ℤ (⊥ : Pi4) p1 = -1 := by
  rw [mu_eq_neg_sum_Ico_of_ne bot_ne_p1, Ico_bot_p1, sum_singleton, mu_self]

lemma mu_bot_p2 : mu ℤ (⊥ : Pi4) p2 = -1 := by
  rw [mu_eq_neg_sum_Ico_of_ne bot_ne_p2, Ico_bot_p2, sum_singleton, mu_self]

/-- **Main computation.** In the partition lattice `Π₄`, `μ(0̂, {01|23}) = 1`. -/
theorem mu_bot_sigma : mu ℤ (⊥ : Pi4) sigma = 1 := by
  rw [mu_eq_neg_sum_Ico_of_ne bot_ne_sigma, Ico_bot_sigma,
    sum_insert (by simp [bot_ne_p1, bot_ne_p2]), sum_insert (by simp [p1_ne_p2]),
    sum_singleton, mu_self, mu_bot_p1, mu_bot_p2]
  norm_num

/-- A set partition has a repeated block size if two distinct blocks have the same size
(equivalently, its type, the integer partition of block sizes, has a repeated part). -/
def HasRepeatedBlockSize {n : ℕ} (P : Finpartition (univ : Finset (Fin n))) : Prop :=
  ∃ B ∈ P.parts, ∃ C ∈ P.parts, B ≠ C ∧ B.card = C.card

lemma sigma_repeated : HasRepeatedBlockSize sigma :=
  ⟨{0, 1}, by decide, {2, 3}, by decide, by decide, by decide⟩

/-- **Disproof of 00000002491.** It is false that the Möbius function `μ(0̂, σ)` of the partition
lattice vanishes at every partition `σ` with a repeated block size: in `Π₄`, the partition
`σ = {01|23}` has two blocks of size 2 and `μ(0̂, σ) = 1`. -/
theorem conjecture_2491_false :
    ¬ ∀ σ : Pi4, HasRepeatedBlockSize σ → mu ℤ (⊥ : Pi4) σ = 0 := by
  intro h
  have := h sigma sigma_repeated
  rw [mu_bot_sigma] at this
  exact one_ne_zero this

theorem sigma_witness : HasRepeatedBlockSize sigma ∧ mu ℤ (⊥ : Pi4) sigma ≠ 0 :=
  ⟨sigma_repeated, by rw [mu_bot_sigma]; exact one_ne_zero⟩

/-! ### The dual reading: the interval `[σ, 1̂]` -/

lemma top_parts : (⊤ : Pi4).parts = {univ} := by
  apply Subset.antisymm (Finpartition.parts_top_subset _)
  rw [singleton_subset_iff]
  have h := (⊤ : Pi4).part_mem.2 (mem_univ (0 : Fin 4))
  have hu := (⊤ : Pi4).part_subset (0 : Fin 4)
  have h1 := Finpartition.parts_top_subset (univ : Finset (Fin 4)) h
  rw [mem_singleton] at h1
  rwa [h1] at h

lemma sigma_le_cases (x : Pi4) (h : sigma ≤ x) : x = sigma ∨ x = ⊤ := by
  rw [le_iff] at h
  have h0 := h 0; have h2 := h 2
  simp only [sigma_part] at h0 h2
  simp at h0 h2
  have m : ∀ a, a ∈ x.part a := fun a => x.mem_part (mem_univ a)
  have same : ∀ {a b : Fin 4}, b ∈ x.part a → x.part b = x.part a := fun hb =>
    x.part_eq_of_mem (x.part_mem.2 (mem_univ _)) hb
  have e1 : x.part 1 = x.part 0 := same (h0 (by decide))
  have e3 : x.part 3 = x.part 2 := same (h2 (by decide))
  by_cases h20 : (2 : Fin 4) ∈ x.part 0
  · right
    have e2 : x.part 2 = x.part 0 := same h20
    have hu : x.part 0 = univ := by
      apply eq_univ_of_forall
      intro a; fin_cases a
      · exact m 0
      · exact h0 (by decide)
      · exact h20
      · rw [← e2]; exact h2 (by decide)
    ext1; rw [parts_eq x, e1, e3, e2, hu, top_parts]; decide
  · left
    have h30 : (3 : Fin 4) ∉ x.part 0 := fun h3 => h20 (by rw [← same h3, e3]; exact m 2)
    have h02 : (0 : Fin 4) ∉ x.part 2 := fun h0' => h20 (by rw [same h0']; exact m 2)
    have h12 : (1 : Fin 4) ∉ x.part 2 := fun h1' => h20 (by rw [← e1, same h1']; exact m 2)
    have key : ∀ t : Finset (Fin 4), ∀ a b c d : Fin 4, a ∈ t → b ∈ t → c ∉ t → d ∉ t →
        a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → t = {a, b} := by decide
    have f0 : x.part 0 = {0, 1} :=
      key _ 0 1 2 3 (m 0) (h0 (by decide)) h20 h30 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    have f2 : x.part 2 = {2, 3} :=
      key _ 2 3 0 1 (m 2) (h2 (by decide)) h02 h12 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    ext1; rw [parts_eq x, e1, e3, f0, f2]; decide

lemma not_top_le_sigma : ¬ (⊤ : Pi4) ≤ sigma := by
  show ¬ ∀ ⦃b⦄, b ∈ (⊤ : Pi4).parts → ∃ c ∈ sigma.parts, b ≤ c; rw [top_parts]; decide

lemma sigma_ne_top : sigma ≠ ⊤ := fun h => not_top_le_sigma (h ▸ le_rfl)

/-- The interval `[σ, 1̂)` is `{σ}`. -/
lemma Ico_sigma_top : Ico sigma (⊤ : Pi4) = {sigma} := by
  ext x
  simp only [mem_Ico, mem_singleton]
  constructor
  · rintro ⟨hx, hx'⟩
    rcases sigma_le_cases x hx with h | h
    · exact h
    · exact absurd h hx'.ne
  · rintro rfl; exact ⟨le_rfl, le_top.lt_of_ne sigma_ne_top⟩

/-- In `Π₄`, `μ(σ, 1̂) = -1` for `σ = {01|23}`. -/
theorem mu_sigma_top : mu ℤ sigma (⊤ : Pi4) = -1 := by
  rw [mu_eq_neg_sum_Ico_of_ne sigma_ne_top, Ico_sigma_top, sum_singleton, mu_self]

/-- The dual reading (values `μ(σ, 1̂)`) is refuted by the same partition. -/
theorem conjecture_2491_false_dual :
    ¬ ∀ σ : Pi4, HasRepeatedBlockSize σ → mu ℤ σ (⊤ : Pi4) = 0 := by
  intro h
  have := h sigma sigma_repeated
  rw [mu_sigma_top] at this
  exact absurd this (by norm_num)

end C2491
