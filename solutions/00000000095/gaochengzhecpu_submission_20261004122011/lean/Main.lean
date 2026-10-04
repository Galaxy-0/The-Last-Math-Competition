import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! An unbounded family of genuine polynomial Galois groups of order below d!. -/
namespace Conjecture95

noncomputable section
open Polynomial

/-- The polynomial in the source, over the rational field. -/
def trinomial (p d : ℕ) : ℚ[X] := X ^ d - X - C (p : ℚ)

/-- The assertion of an abstract group isomorphism, independent of root labeling. -/
def FullSymmetricGalois (p d : ℕ) : Prop :=
  Nonempty ((trinomial p d).Gal ≃* Equiv.Perm (Fin d))

theorem trinomial_natDegree (p d : ℕ) (hd : 2 ≤ d) :
    (trinomial p d).natDegree = d := by
  rw [trinomial, natDegree_sub_C, natDegree_sub_eq_left_of_natDegree_lt]
  · simp
  · simp only [natDegree_X, natDegree_X_pow]
    omega

theorem minus_one_is_root (d : ℕ) (hd : Even d) :
    (trinomial 2 d).IsRoot (-1) := by
  simp only [IsRoot, trinomial, eval_sub, eval_pow, eval_X, eval_C]
  rw [hd.neg_one_pow]
  norm_num

/-- The automorphism group of a splitting field acts faithfully on its actual roots. -/
theorem gal_card_le_factorial_degree (q : ℚ[X]) :
    Fintype.card q.Gal ≤ q.natDegree.factorial := by
  classical
  letI : Fact (q.Splits (algebraMap ℚ q.SplittingField)) :=
    ⟨SplittingField.splits q⟩
  have hinj := Gal.galActionHom_injective q q.SplittingField
  have hcard := Fintype.card_le_of_injective (Gal.galActionHom q q.SplittingField) hinj
  rw [Fintype.card_perm] at hcard
  have hroots : Fintype.card (q.rootSet q.SplittingField) ≤ q.natDegree := by
    simp only [rootSet_def, Finset.coe_sort_coe, Fintype.card_coe]
    exact (Multiset.toFinset_card_le _).trans ((card_roots' _).trans natDegree_map_le)
  exact hcard.trans (Nat.factorial_le hroots)

/-- A rational linear factor contributes no nontrivial splitting-field automorphism. -/
theorem gal_card_linear_mul_le (r : ℚ) (q : ℚ[X]) :
    Fintype.card ((X - C r) * q).Gal ≤ Fintype.card q.Gal := by
  have h := Fintype.card_le_of_injective (Gal.restrictProd (X - C r) q)
    (Gal.restrictProd_injective (X - C r) q)
  simpa only [Fintype.card_prod, Fintype.card_unique, one_mul] using h

theorem even_degree_gal_card_bound (d : ℕ) (hsize : 2 ≤ d) (heven : Even d) :
    Fintype.card (trinomial 2 d).Gal ≤ (d - 1).factorial := by
  have hdegree := trinomial_natDegree 2 d hsize
  have hnonzero : trinomial 2 d ≠ 0 := by
    intro hz
    simp only [hz, natDegree_zero] at hdegree
    omega
  have hdiv : X - C (-1 : ℚ) ∣ trinomial 2 d :=
    dvd_iff_isRoot.mpr (minus_one_is_root d heven)
  obtain ⟨q, hq⟩ := hdiv
  have hqnonzero : q ≠ 0 := by
    intro hz
    apply hnonzero
    simp only [hq, hz, mul_zero]
  have hqdegree : q.natDegree = d - 1 := by
    rw [hq, natDegree_mul (X_sub_C_ne_zero _) hqnonzero, natDegree_X_sub_C] at hdegree
    omega
  rw [hq]
  exact (gal_card_linear_mul_le (-1) q).trans
    ((gal_card_le_factorial_degree q).trans_eq (congrArg Nat.factorial hqdegree))

/-- The order is strictly smaller than that of S_d, so even an abstract isomorphism is impossible. -/
theorem even_degree_not_full_symmetric (d : ℕ) (hsize : 2 ≤ d) (heven : Even d) :
    ¬ FullSymmetricGalois 2 d := by
  rintro ⟨e⟩
  have hbound := even_degree_gal_card_bound d hsize heven
  have heq := Fintype.card_congr e.toEquiv
  simp only [Fintype.card_perm, Fintype.card_fin] at heq
  have hstrict : (d - 1).factorial < d.factorial :=
    Nat.factorial_lt_of_lt (by omega) (by omega)
  omega

theorem arbitrarily_large_counterexamples (N : ℕ) :
    ∃ d : ℕ, N ≤ d ∧ 2 ≤ d ∧ Even d ∧ ¬ FullSymmetricGalois 2 d := by
  let d := 2 * (N + 1)
  have hd : 2 ≤ d := by dsimp [d]; omega
  have heven : Even d := ⟨N + 1, by dsimp [d]; omega⟩
  exact ⟨d, by dsimp [d]; omega, hd, heven, even_degree_not_full_symmetric d hd heven⟩

/-- The usual eventual reading of the claim for each fixed prime. -/
def EventualFullSymmetricForEveryPrime : Prop :=
  ∀ p : ℕ, p.Prime → ∃ N : ℕ, ∀ d : ℕ, N ≤ d → FullSymmetricGalois p d

theorem conjecture95_false : ¬ EventualFullSymmetricForEveryPrime := by
  intro h
  obtain ⟨N, hN⟩ := h 2 Nat.prime_two
  obtain ⟨d, hNd, _, _, hnot⟩ := arbitrarily_large_counterexamples N
  exact hnot (hN d hNd)

#print axioms trinomial_natDegree
#print axioms minus_one_is_root
#print axioms gal_card_le_factorial_degree
#print axioms gal_card_linear_mul_le
#print axioms even_degree_gal_card_bound
#print axioms even_degree_not_full_symmetric
#print axioms arbitrarily_large_counterexamples
#print axioms conjecture95_false

end
end Conjecture95
