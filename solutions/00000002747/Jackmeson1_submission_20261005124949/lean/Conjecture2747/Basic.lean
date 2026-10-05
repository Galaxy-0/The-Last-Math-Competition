import Mathlib

/-!
# Conjecture 00000002747 (disproved)

*Definition.* The capacity of a matrix algebra is the maximal dimension of a linear subspace
on which the determinant vanishes identically.

*Conjecture.* The capacity of `M_m(M_n)` is `(m - 1) n^2 + n`, and the capacity spaces form a
single orbit.

We work over an arbitrary field `K`.  `M_m(M_n(K))` is `Matrix (Fin m) (Fin m) (Matrix (Fin n)
(Fin n) K)`, and its determinant is the determinant of the `mn x mn` matrix obtained by
forgetting the block structure (Mathlib's `Matrix.comp`).

* `capacity_one_one` : the capacity of `M_1(M_1(K))` is `0`, while the formula gives `1`.
* `formula_lt_capacity` : whenever `m, n >= 1` and `mn >= 3`, the subspace of block matrices whose
  first scalar row is zero is singular of dimension `mn(mn - 1)`, which exceeds `(m - 1) n^2 + n`.
* `conjecture_false` : the conjunction "capacity formula and (any) classification statement"
  fails, already for the formula clause.
-/

open Matrix Module

namespace C2747

variable (K : Type*) [Field K]

/-- The block matrix algebra `M_m(M_n(K))`. -/
abbrev BlockMat (m n : ℕ) := Matrix (Fin m) (Fin m) (Matrix (Fin n) (Fin n) K)

/-- The determinant on `M_m(M_n(K))`: the determinant of the underlying `mn x mn` matrix,
obtained by the canonical identification `Matrix.comp` (the block-matrix isomorphism). -/
noncomputable def blockDet {m n : ℕ} (A : BlockMat K m n) : K :=
  (Matrix.comp (Fin m) (Fin m) (Fin n) (Fin n) K A).det

/-- A linear subspace of `M_m(M_n(K))` on which the determinant vanishes identically. -/
def IsSingularSpace {m n : ℕ} (V : Submodule K (BlockMat K m n)) : Prop :=
  ∀ A ∈ V, blockDet K A = 0

/-- The capacity of `M_m(M_n(K))`: the maximal dimension of a linear subspace on which the
determinant vanishes identically. -/
noncomputable def capacity (m n : ℕ) : ℕ :=
  sSup {d | ∃ V : Submodule K (BlockMat K m n), IsSingularSpace K V ∧ finrank K V = d}

variable {K}

lemma capacity_set_bdd (m n : ℕ) :
    BddAbove {d | ∃ V : Submodule K (BlockMat K m n), IsSingularSpace K V ∧ finrank K V = d} := by
  refine ⟨finrank K (BlockMat K m n), ?_⟩
  rintro d ⟨V, -, rfl⟩
  exact Submodule.finrank_le V

/-- Every singular subspace has dimension at most the capacity. -/
lemma finrank_le_capacity {m n : ℕ} (V : Submodule K (BlockMat K m n))
    (hV : IsSingularSpace K V) : finrank K V ≤ capacity K m n :=
  le_csSup (capacity_set_bdd m n) ⟨V, hV, rfl⟩

/-- If every singular subspace has dimension `≤ c`, then the capacity is `≤ c`. -/
lemma capacity_le {m n c : ℕ}
    (h : ∀ V : Submodule K (BlockMat K m n), IsSingularSpace K V → finrank K V ≤ c) :
    capacity K m n ≤ c := by
  refine csSup_le' ?_
  rintro d ⟨V, hV, rfl⟩
  exact h V hV

/-! ### `m = n = 1`: the capacity is `0`, the formula gives `1` -/

/-- On `M_1(M_1(K))` the determinant is the unique entry, so the only singular subspace is `0`. -/
theorem capacity_one_one : capacity K 1 1 = 0 := by
  refine Nat.le_zero.1 (capacity_le fun V hV => ?_)
  have hbot : V = ⊥ := by
    refine (Submodule.eq_bot_iff V).2 fun A hA => ?_
    let _ : Unique (Fin 1 × Fin 1) :=
      { default := (0, 0)
        uniq := fun x => Prod.ext (Fin.fin_one_eq_zero _) (Fin.fin_one_eq_zero _) }
    have h0 := hV A hA
    rw [blockDet, Matrix.det_unique] at h0
    ext i j k l
    rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j, Fin.fin_one_eq_zero k,
      Fin.fin_one_eq_zero l]
    exact h0
  rw [hbot, finrank_bot]

/-! ### The zero-row subspace -/

section RowZero

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Taking the `i₀`-th row of a scalar matrix, as a linear map. -/
def rowMap (i₀ : ι) : Matrix ι ι K →ₗ[K] (ι → K) where
  toFun A := A i₀
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype ι] in
lemma rowMap_surjective (i₀ : ι) : Function.Surjective (rowMap (K := K) i₀) := by
  intro v
  refine ⟨Matrix.of fun i j => if i = i₀ then v j else 0, ?_⟩
  funext j
  change (Matrix.of fun i j => if i = i₀ then v j else 0) i₀ j = v j
  simp

/-- The space of matrices whose `i₀`-th row vanishes has dimension `N^2 - N`, `N = |ι|`. -/
lemma finrank_ker_rowMap (i₀ : ι) :
    finrank K (LinearMap.ker (rowMap (K := K) i₀)) =
      Fintype.card ι * Fintype.card ι - Fintype.card ι := by
  have h := LinearMap.finrank_range_add_finrank_ker (rowMap (K := K) i₀)
  rw [LinearMap.range_eq_top.2 (rowMap_surjective i₀), finrank_top,
    Module.finrank_fintype_fun_eq_card, Module.finrank_matrix, Module.finrank_self,
    mul_one] at h
  omega

end RowZero

/-- The subspace of `M_m(M_n(K))` whose block matrices have zero first scalar row
(row `(i₀, k₀)` of the underlying `mn x mn` matrix). -/
noncomputable def rowZeroSpace {m n : ℕ} (i₀ : Fin m) (k₀ : Fin n) :
    Submodule K (BlockMat K m n) :=
  (LinearMap.ker (rowMap (K := K) (i₀, k₀))).map
    (Matrix.compLinearEquiv (Fin m) (Fin m) (Fin n) (Fin n) K K).symm.toLinearMap

/-- The zero-row subspace is singular: every member has a zero row, hence determinant `0`. -/
lemma rowZeroSpace_singular {m n : ℕ} (i₀ : Fin m) (k₀ : Fin n) :
    IsSingularSpace K (rowZeroSpace (K := K) i₀ k₀) := by
  rintro A ⟨B, hB, rfl⟩
  have hrow : ∀ j, B (i₀, k₀) j = 0 := fun j => congrFun hB j
  simp only [blockDet, LinearEquiv.coe_coe, Matrix.compLinearEquiv_symm_apply,
    Equiv.apply_symm_apply]
  exact Matrix.det_eq_zero_of_row_eq_zero (i₀, k₀) hrow

/-- The zero-row subspace has dimension `mn(mn) - mn`. -/
lemma finrank_rowZeroSpace {m n : ℕ} (i₀ : Fin m) (k₀ : Fin n) :
    finrank K (rowZeroSpace (K := K) i₀ k₀) = (m * n) * (m * n) - m * n := by
  rw [rowZeroSpace, LinearEquiv.finrank_map_eq, finrank_ker_rowMap]
  simp [Fintype.card_prod]

/-- Lower bound: for `m, n ≥ 1` the capacity of `M_m(M_n(K))` is at least `mn(mn) - mn`. -/
theorem capacity_ge {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (m * n) * (m * n) - m * n ≤ capacity K m n := by
  have i₀ : Fin m := ⟨0, hm⟩
  have k₀ : Fin n := ⟨0, hn⟩
  rw [← finrank_rowZeroSpace (K := K) i₀ k₀]
  exact finrank_le_capacity _ (rowZeroSpace_singular i₀ k₀)

/-- Arithmetic: `(m - 1) n^2 + n < mn(mn) - mn` once `m, n ≥ 1` and `mn ≥ 3`. -/
lemma formula_lt {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (h3 : 3 ≤ m * n) :
    (m - 1) * n ^ 2 + n < (m * n) * (m * n) - m * n := by
  obtain ⟨a, rfl⟩ : ∃ a, m = a + 1 := ⟨m - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, n = b + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have key : a * (b + 1) ^ 2 + (b + 1) + (a + 1) * (b + 1) <
      (a + 1) * (b + 1) * ((a + 1) * (b + 1)) := by
    have hab : 2 ≤ a * b + a + b := by nlinarith
    rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha; nlinarith
    · rcases Nat.eq_zero_or_pos b with hb | hb
      · subst hb; nlinarith
      · nlinarith [Nat.mul_pos ha hb, Nat.mul_pos (Nat.mul_pos ha ha) hb]
  omega

/-- For every `m, n ≥ 1` with `mn ≥ 3`, the capacity of `M_m(M_n(K))` strictly exceeds the
conjectured value `(m - 1) n^2 + n`. -/
theorem formula_lt_capacity {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (h3 : 3 ≤ m * n) :
    (m - 1) * n ^ 2 + n < capacity K m n :=
  lt_of_lt_of_le (formula_lt hm hn h3) (capacity_ge hm hn)

/-- `m = n = 2`: capacity of `M_2(M_2(K)) = M_4(K)` is at least `12 > 6`. -/
theorem capacity_two_two : 12 ≤ capacity K 2 2 ∧ (2 - 1) * 2 ^ 2 + 2 = 6 :=
  ⟨by simpa using capacity_ge (K := K) (m := 2) (n := 2) (by norm_num) (by norm_num), rfl⟩

/-- **Disproof of conjecture 00000002747.**  For every field `K` and every proposition
`Classif m n` (whatever formalization of the orbit-classification clause is chosen), the
conjunction "capacity of `M_m(M_n(K))` is `(m - 1) n^2 + n` and `Classif m n`" fails for some
`m, n ≥ 1`; in fact the capacity clause alone fails at `m = n = 1` and at every `m, n ≥ 1`
with `mn ≥ 3`. -/
theorem conjecture_false (Classif : ℕ → ℕ → Prop) :
    ¬ ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
      (capacity K m n = (m - 1) * n ^ 2 + n ∧ Classif m n) := by
  intro h
  have := (h 1 1 le_rfl le_rfl).1
  rw [capacity_one_one] at this
  norm_num at this

end C2747
