import Mathlib

/-!
# Conjecture 00000000269 is false

Conjecture 00000000269 asserts that for all sufficiently large `n` the Galois
group of `xⁿ + x + 1` over `ℚ` is the symmetric group `Sₙ`.

It fails for every `n ≡ 2 (mod 3)` with `n ≥ 5`. For such `n` the cube roots of
unity are roots, so `x² + x + 1` divides `xⁿ + x + 1`:

  `xⁿ + x + 1 = x² · (x^(3(k+1)) - 1) + (x² + x + 1)`   for `n = 3k + 5`,

and `x² + x + 1 ∣ x³ - 1 ∣ x^(3(k+1)) - 1`. Writing `xⁿ + x + 1 = (x² + x + 1) · g`
with `deg g = n - 2`, the Galois group of the product embeds into the product of
the Galois groups (`Polynomial.Gal.restrictProd_injective`), and the Galois group
of a polynomial of degree `d` embeds into the permutations of its at most `d`
roots (`Polynomial.Gal.galActionHom_injective`). Hence

  `|Gal(xⁿ + x + 1)| ≤ 2! · (n - 2)! < n!`,

so the group is not even abstractly isomorphic to `Sₙ`. Since `n = 3k + 5` is
unbounded, no threshold works.
-/

namespace Submission00000000269

open Polynomial

/-- The trinomial `xⁿ + x + 1 ∈ ℚ[x]`. -/
noncomputable def trinomial (n : ℕ) : ℚ[X] := X ^ n + X + 1

/-- "The Galois group of `xⁿ + x + 1` over `ℚ` is `Sₙ`", in its weakest reading:
the Galois group is isomorphic, as an abstract group, to the symmetric group on
`n` letters. (Any stronger reading, such as the Galois group acting as the full
symmetric group on the `n` roots, implies this one.) -/
def GalIsSymmetric (n : ℕ) : Prop :=
  Nonempty ((trinomial n).Gal ≃* Equiv.Perm (Fin n))

/-- Conjecture 00000000269: for all sufficiently large `n`, the Galois group of
`xⁿ + x + 1` is `Sₙ`. -/
def ConjectureHolds : Prop :=
  ∃ N : ℕ, ∀ n, N ≤ n → GalIsSymmetric n

/-- The Galois group of a polynomial of degree `d` has at most `d!` elements: it
acts faithfully on the at most `d` roots in a splitting field. -/
theorem card_gal_le (p : ℚ[X]) : Nat.card p.Gal ≤ Nat.factorial p.natDegree := by
  have : Fact ((p.map (algebraMap ℚ p.SplittingField)).Splits) :=
    ⟨SplittingField.splits p⟩
  calc Nat.card p.Gal
      ≤ Nat.card (Equiv.Perm (p.rootSet p.SplittingField)) :=
        Nat.card_le_card_of_injective _ (Gal.galActionHom_injective p p.SplittingField)
    _ = Nat.factorial (Nat.card (p.rootSet p.SplittingField)) := Nat.card_perm
    _ ≤ Nat.factorial p.natDegree := by
        apply Nat.factorial_le
        rw [Nat.card_coe_set_eq]
        exact ncard_rootSet_le p p.SplittingField

/-- The Galois group of a product embeds into the product of the Galois groups. -/
theorem card_gal_mul_le (p q : ℚ[X]) :
    Nat.card (p * q).Gal ≤ Nat.card p.Gal * Nat.card q.Gal := by
  rw [← Nat.card_prod]
  exact Nat.card_le_card_of_injective _ (Gal.restrictProd_injective p q)

/-- For `n = 3k + 5`, the cyclotomic factor `x² + x + 1` divides `xⁿ + x + 1`. -/
theorem cyclotomic_dvd_trinomial (k : ℕ) :
    (X ^ 2 + X + 1 : ℚ[X]) ∣ trinomial (3 * k + 5) := by
  have h₁ : (X ^ 2 + X + 1 : ℚ[X]) ∣ X ^ 3 - 1 := ⟨X - 1, by ring⟩
  have h₂ : (X ^ 3 - 1 : ℚ[X]) ∣ (X ^ 3) ^ (k + 1) - 1 := by
    simpa using sub_dvd_pow_sub_pow (X ^ 3 : ℚ[X]) 1 (k + 1)
  have h : trinomial (3 * k + 5) = X ^ 2 * ((X ^ 3) ^ (k + 1) - 1) + (X ^ 2 + X + 1) := by
    unfold trinomial
    ring
  rw [h]
  exact dvd_add (dvd_mul_of_dvd_right (h₁.trans h₂) _) dvd_rfl

theorem natDegree_cyclotomic : (X ^ 2 + X + 1 : ℚ[X]).natDegree = 2 := by
  compute_degree!

theorem natDegree_trinomial {n : ℕ} (hn : 2 ≤ n) : (trinomial n).natDegree = n := by
  unfold trinomial
  have hX : (X : ℚ[X]).natDegree < (X ^ n : ℚ[X]).natDegree := by
    rw [natDegree_X, natDegree_X_pow]
    omega
  rw [natDegree_add_eq_left_of_natDegree_lt (by
        rw [natDegree_add_eq_left_of_natDegree_lt hX, natDegree_one, natDegree_X_pow]
        omega),
    natDegree_add_eq_left_of_natDegree_lt hX, natDegree_X_pow]

/-- For `n = 3k + 5`, the Galois group of `xⁿ + x + 1` has at most `2 · (n - 2)!`
elements. -/
theorem card_gal_trinomial_le (k : ℕ) :
    Nat.card (trinomial (3 * k + 5)).Gal ≤ 2 * Nat.factorial (3 * k + 3) := by
  obtain ⟨g, hg⟩ := cyclotomic_dvd_trinomial k
  have hf : trinomial (3 * k + 5) ≠ 0 := by
    intro h0
    have := natDegree_trinomial (n := 3 * k + 5) (by omega)
    rw [h0, natDegree_zero] at this
    omega
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hg
    exact hf hg
  have hc0 : (X ^ 2 + X + 1 : ℚ[X]) ≠ 0 := by
    intro h0
    have := natDegree_cyclotomic
    rw [h0, natDegree_zero] at this
    omega
  have hdeg : g.natDegree = 3 * k + 3 := by
    have := congrArg natDegree hg
    rw [natDegree_mul hc0 hg0, natDegree_cyclotomic,
      natDegree_trinomial (by omega)] at this
    omega
  calc Nat.card (trinomial (3 * k + 5)).Gal
      = Nat.card ((X ^ 2 + X + 1 : ℚ[X]) * g).Gal := by rw [← hg]
    _ ≤ Nat.card (X ^ 2 + X + 1 : ℚ[X]).Gal * Nat.card g.Gal := card_gal_mul_le _ _
    _ ≤ Nat.factorial 2 * Nat.factorial (3 * k + 3) := by
        apply Nat.mul_le_mul
        · have h := card_gal_le (X ^ 2 + X + 1 : ℚ[X])
          rwa [natDegree_cyclotomic] at h
        · have h := card_gal_le g
          rwa [hdeg] at h
    _ = 2 * Nat.factorial (3 * k + 3) := by rw [Nat.factorial_two]

/-- For `n = 3k + 5`, the Galois group of `xⁿ + x + 1` is not `Sₙ`. -/
theorem not_galIsSymmetric (k : ℕ) : ¬ GalIsSymmetric (3 * k + 5) := by
  rintro ⟨e⟩
  have hcard : Nat.card (trinomial (3 * k + 5)).Gal = Nat.factorial (3 * k + 5) := by
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  have hle := card_gal_trinomial_le k
  rw [hcard] at hle
  have hfac : Nat.factorial (3 * k + 5) =
      (3 * k + 5) * (3 * k + 4) * Nat.factorial (3 * k + 3) := by
    rw [show 3 * k + 5 = (3 * k + 3) + 1 + 1 by ring, Nat.factorial_succ,
      Nat.factorial_succ]
    ring
  rw [hfac] at hle
  have h20 : 2 < (3 * k + 5) * (3 * k + 4) := by nlinarith
  exact absurd hle (not_le.mpr (Nat.mul_lt_mul_of_pos_right h20 (Nat.factorial_pos _)))

/-- Conjecture 00000000269 is false: for any threshold `N`, the exponent
`n = 3N + 5 ≥ N` has `n ≡ 2 (mod 3)`, and the Galois group of `xⁿ + x + 1` is not
`Sₙ`. -/
theorem conjecture_00000000269_false : ¬ ConjectureHolds := by
  rintro ⟨N, hN⟩
  exact not_galIsSymmetric N (hN (3 * N + 5) (by omega))

end Submission00000000269

#print axioms Submission00000000269.conjecture_00000000269_false
