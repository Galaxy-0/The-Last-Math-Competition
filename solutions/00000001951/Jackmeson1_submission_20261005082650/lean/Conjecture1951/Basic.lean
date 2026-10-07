import Mathlib

/-!
# Conjecture 00000001951: the smallest index of a proper subgroup of `Out(F_n)` is not `2^n·C(n,2)`

The conjecture asserts (among other things) that for `n ≥ 3` the smallest index of a proper
subgroup of `Out(F_n)` is `2^n · C(n,2)`.

We show that for every `n ≥ 1`, `Out(F_n)` has a proper normal subgroup of index exactly `2`:
the kernel of the determinant of the induced action on the abelianization `F_n^ab ≅ ℤⁿ`.
Inner automorphisms act trivially on `ℤⁿ`, and inverting one free generator has determinant
`-1`. Hence the smallest index of a proper finite-index subgroup of `Out(F_n)` is `2`, which is
different from `2^n · C(n,2)` for every `n ≥ 2` (in particular for every `n ≥ 3`).

Conventions.
* `F_n = FreeGroup (Fin n)`, `Aut(F_n) = MulAut (F n)`, `Inn(F_n)` is the range of
  `MulAut.conj`, and `Out(F_n) = Aut(F_n) ⧸ Inn(F_n)`.
* The abelianization is realised concretely as the exponent-sum homomorphism
  `F_n → ℤⁿ`, `x_i ↦ e_i`; `mat φ` is the integer matrix whose `j`-th column is the
  exponent-sum vector of `φ(x_j)`.
* `Subgroup.index` is `0` for infinite-index subgroups (Mathlib); the subgroup we exhibit has
  finite index `2`, and all statements below about proper subgroups require finite index.
-/

open Matrix

namespace C1951

variable {n : ℕ}

/-- The free group of rank `n`. -/
abbrev F (n : ℕ) := FreeGroup (Fin n)

/-- Inner automorphisms of `F_n`. -/
def Inn (n : ℕ) : Subgroup (MulAut (F n)) := (MulAut.conj : F n →* MulAut (F n)).range

instance Inn.normal : (Inn n).Normal :=
  ⟨by
    rintro _ ⟨g, rfl⟩ ψ
    refine ⟨ψ g, ?_⟩
    ext x
    simp [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply]⟩

/-- `Out(F_n) = Aut(F_n) / Inn(F_n)`. -/
abbrev Out (n : ℕ) := MulAut (F n) ⧸ Inn n

/-- The exponent-sum (abelianization) homomorphism `F_n → ℤⁿ`, `x_i ↦ e_i`. -/
def ab : F n →* Multiplicative (Fin n → ℤ) :=
  FreeGroup.lift fun i => Multiplicative.ofAdd (Pi.single i 1)

/-- Exponent-sum vector of `w`. -/
def vec (w : F n) : Fin n → ℤ := Multiplicative.toAdd (ab w)

@[simp] theorem vec_one : vec (1 : F n) = 0 := by simp [vec]
@[simp] theorem vec_mul (x y : F n) : vec (x * y) = vec x + vec y := by simp [vec]
@[simp] theorem vec_inv (x : F n) : vec x⁻¹ = -vec x := by simp [vec]
@[simp] theorem vec_of (i : Fin n) : vec (FreeGroup.of i) = Pi.single i 1 := by
  simp [vec, ab]

/-- The matrix of the action of `φ` on `F_n^ab = ℤⁿ` (column `j` = `vec (φ x_j)`). -/
def mat (φ : MulAut (F n)) : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j => vec (φ (.of j)) i

theorem vec_apply (φ : MulAut (F n)) (w : F n) : vec (φ w) = mat φ *ᵥ vec w := by
  induction w using FreeGroup.induction_on with
  | C1 => simp
  | of j => rw [vec_of, mulVec_single_one]; ext i; rfl
  | inv_of j h => rw [map_inv, vec_inv, h, vec_inv, mulVec_neg]
  | mul x y hx hy => rw [map_mul, vec_mul, hx, hy, vec_mul, mulVec_add]

theorem mat_one : mat (1 : MulAut (F n)) = 1 := by
  ext i j
  simp [mat, one_apply, Pi.single_apply]

theorem mat_mul (φ ψ : MulAut (F n)) : mat (φ * ψ) = mat φ * mat ψ := by
  ext i j
  have h := congrFun (vec_apply φ (ψ (.of j))) i
  simp only [mat, of_apply, MulAut.mul_apply] at h ⊢
  rw [h, mul_apply, mulVec, dotProduct]
  rfl

/-- `φ ↦ mat φ` as a monoid homomorphism `Aut(F_n) → M_n(ℤ)`. -/
def matHom (n : ℕ) : MulAut (F n) →* Matrix (Fin n) (Fin n) ℤ where
  toFun := mat
  map_one' := mat_one
  map_mul' := mat_mul

/-- `φ ↦ det (φ_ab) ∈ ℤˣ`. -/
def detHom (n : ℕ) : MulAut (F n) →* ℤˣ := (detMonoidHom.comp (matHom n)).toHomUnits

theorem detHom_val (φ : MulAut (F n)) : ((detHom n φ : ℤˣ) : ℤ) = (mat φ).det := rfl

/-- Inner automorphisms act trivially on `F_n^ab`. -/
theorem mat_conj (g : F n) : mat (MulAut.conj g) = 1 := by
  ext i j
  have h : vec (MulAut.conj g (FreeGroup.of j)) = Pi.single j 1 := by
    rw [MulAut.conj_apply, vec_mul, vec_mul, vec_inv, vec_of]; abel
  simp only [mat, of_apply, h, one_apply, Pi.single_apply]

theorem Inn_le_ker : Inn n ≤ (detHom n).ker := by
  rintro _ ⟨g, rfl⟩
  rw [MonoidHom.mem_ker]
  ext
  rw [detHom_val, mat_conj, det_one, Units.val_one]

/-- The determinant character `Out(F_n) → ℤˣ = {±1}`. -/
def outDet (n : ℕ) : Out n →* ℤˣ := QuotientGroup.lift (Inn n) (detHom n) Inn_le_ker

/-- The automorphism of `F_n` inverting the generator `x_{i₀}` and fixing the others
(as an endomorphism; it is an involution). -/
def flipHom (i₀ : Fin n) : F n →* F n :=
  FreeGroup.lift fun i => if i = i₀ then (FreeGroup.of i)⁻¹ else FreeGroup.of i

theorem flipHom_flipHom (i₀ : Fin n) : (flipHom i₀).comp (flipHom i₀) = MonoidHom.id _ := by
  ext i
  by_cases h : i = i₀ <;> simp [flipHom, h]

/-- `x_{i₀} ↦ x_{i₀}⁻¹`, `x_i ↦ x_i` (`i ≠ i₀`), as an automorphism of `F_n`. -/
def flip (i₀ : Fin n) : MulAut (F n) :=
  MonoidHom.toMulEquiv (flipHom i₀) (flipHom i₀) (flipHom_flipHom i₀) (flipHom_flipHom i₀)

theorem mat_flip (i₀ : Fin n) : mat (flip i₀) = diagonal fun i => if i = i₀ then -1 else 1 := by
  ext i j
  by_cases hj : j = i₀
  · subst hj; by_cases hi : i = j <;> simp [mat, flip, flipHom, diagonal, hi]
  · by_cases hi : i = j
    · subst hi; simp [mat, flip, flipHom, diagonal, hj]
    · simp [mat, flip, flipHom, diagonal, hi, hj]

theorem det_flip (i₀ : Fin n) : (mat (flip i₀)).det = -1 := by
  rw [mat_flip, det_diagonal, Finset.prod_ite_eq' Finset.univ i₀ (fun _ => (-1 : ℤ))]
  simp

/-- For `n ≥ 1` the determinant character of `Out(F_n)` is surjective onto `{±1}`. -/
theorem outDet_surjective (hn : 1 ≤ n) : Function.Surjective (outDet n) := by
  intro u
  rcases Int.units_eq_one_or u with rfl | rfl
  · exact ⟨1, map_one _⟩
  · refine ⟨QuotientGroup.mk (flip ⟨0, hn⟩), ?_⟩
    ext
    simp only [outDet, QuotientGroup.lift_mk, detHom_val, det_flip, Units.val_neg,
      Units.val_one]

/-- The kernel of the determinant character: a proper normal subgroup of index `2`. -/
def K (n : ℕ) : Subgroup (Out n) := (outDet n).ker

theorem K_index (hn : 1 ≤ n) : (K n).index = 2 := by
  rw [K, Subgroup.index_ker, MonoidHom.range_eq_top.mpr (outDet_surjective hn),
    Subgroup.card_top, Nat.card_eq_fintype_card, Fintype.card_units_int]

/-- Main theorem: for every `n ≥ 1`, `Out(F_n)` has a proper normal subgroup of index `2`. -/
theorem exists_normal_index_two (hn : 1 ≤ n) :
    ∃ H : Subgroup (Out n), H.Normal ∧ H ≠ ⊤ ∧ H.index = 2 := by
  refine ⟨K n, MonoidHom.normal_ker _, fun h => ?_, K_index hn⟩
  have := K_index hn
  rw [h, Subgroup.index_top] at this
  omega

/-- The indices of the proper finite-index subgroups of `Out(F_n)`. -/
def properIndices (n : ℕ) : Set ℕ :=
  {k | ∃ H : Subgroup (Out n), H ≠ ⊤ ∧ H.FiniteIndex ∧ H.index = k}

/-- For every `n ≥ 1` the smallest index of a proper (finite-index) subgroup of `Out(F_n)`
is `2`. -/
theorem sInf_properIndices (hn : 1 ≤ n) : sInf (properIndices n) = 2 := by
  obtain ⟨H, -, hH, h2⟩ := exists_normal_index_two hn
  refine le_antisymm (Nat.sInf_le ⟨H, hH, ⟨by omega⟩, h2⟩) (le_csInf ⟨2, H, hH, ⟨by omega⟩, h2⟩ ?_)
  rintro k ⟨H', hne, hfin, rfl⟩
  have h0 := hfin.index_ne_zero
  have h1 : H'.index ≠ 1 := fun h => hne (Subgroup.index_eq_one.mp h)
  omega

theorem two_lt (hn : 2 ≤ n) : 2 < 2 ^ n * n.choose 2 := by
  have h1 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h2 : 1 ≤ n.choose 2 := Nat.choose_pos hn
  nlinarith

/-- The conjecture's clause "the smallest index of a proper subgroup of `Out(F_n)` is
`2^n · C(n,2)`" fails for every `n ≥ 3` (indeed for every `n ≥ 2`). -/
theorem smallest_index_ne (hn : 3 ≤ n) : sInf (properIndices n) ≠ 2 ^ n * n.choose 2 := by
  rw [sInf_properIndices (by omega)]
  exact (two_lt (by omega)).ne

/-- Equivalently, for `n ≥ 3` not every proper finite-index subgroup of `Out(F_n)` has index
at least `2^n · C(n,2)`. -/
theorem not_all_index_ge (hn : 3 ≤ n) :
    ¬ ∀ H : Subgroup (Out n), H ≠ ⊤ → H.FiniteIndex → 2 ^ n * n.choose 2 ≤ H.index := by
  intro h
  obtain ⟨H, -, hH, h2⟩ := exists_normal_index_two (n := n) (by omega)
  have := h H hH ⟨by omega⟩
  have := two_lt (n := n) (by omega)
  omega

end C1951
