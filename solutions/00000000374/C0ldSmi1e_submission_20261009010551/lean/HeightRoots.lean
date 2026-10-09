import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Multiset
import Mathlib.Tactic

open Polynomial

namespace HeightRoots

noncomputable def complexPolynomial (p : Polynomial ℤ) : Polynomial ℂ :=
  p.map (Int.castRingHom ℂ)

noncomputable def mahler (p : Polynomial ℤ) : ℝ :=
  |(p.leadingCoeff : ℝ)| *
    ((complexPolynomial p).roots.map fun z : ℂ => max 1 ‖z‖).prod

noncomputable def weil (p : Polynomial ℤ) : ℝ :=
  mahler p ^ (1 / (p.natDegree : ℝ))

lemma mahler_neg (p : Polynomial ℤ) : mahler (-p) = mahler p := by
  simp only [mahler, complexPolynomial, Polynomial.leadingCoeff_neg, Int.cast_neg,
    abs_neg, Polynomial.map_neg, Polynomial.roots_neg]

lemma weil_neg (p : Polynomial ℤ) : weil (-p) = weil p := by
  simp only [weil, mahler_neg, Polynomial.natDegree_neg]

lemma one_le_int_abs {a : ℤ} (ha : a ≠ 0) : 1 ≤ |(a : ℝ)| := by
  exact_mod_cast Int.one_le_abs ha

lemma one_le_max_prod (s : Multiset ℂ) :
    1 ≤ (s.map fun z : ℂ => max 1 ‖z‖).prod := by
  apply Multiset.one_le_prod
  intro a ha
  obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp ha
  exact le_max_left _ _

lemma norm_prod_le_max_prod (s : Multiset ℂ) :
    (s.map fun z : ℂ => ‖z‖).prod ≤ (s.map fun z : ℂ => max 1 ‖z‖).prod := by
  exact Multiset.prod_map_le_prod_map₀ _ _ (fun z _ => norm_nonneg z)
    (fun z _ => le_max_right _ _)

lemma norm_prod_zero_sub (s : Multiset ℂ) :
    ‖(s.map fun z : ℂ => 0 - z).prod‖ = (s.map fun z : ℂ => ‖z‖).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons z s ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons, norm_mul]
      rw [ih]
      simp

lemma constant_term_product (p : Polynomial ℤ) :
    |(p.coeff 0 : ℝ)| = |(p.leadingCoeff : ℝ)| *
      ((complexPolynomial p).roots.map fun z : ℂ => ‖z‖).prod := by
  have h := Polynomial.eval_eq_prod_roots_sub_of_splits_id
    (IsAlgClosed.splits (complexPolynomial p)) (0 : ℂ)
  have hn := congrArg (fun z : ℂ => ‖z‖) h
  dsimp only at hn
  rw [norm_mul, norm_prod_zero_sub] at hn
  have hinj : Function.Injective (Int.castRingHom ℂ) := Int.cast_injective
  simp only [complexPolynomial, ← Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.coeff_map, Polynomial.leadingCoeff_map' hinj] at hn
  change ‖(p.coeff 0 : ℂ)‖ = ‖(p.leadingCoeff : ℂ)‖ *
    ((complexPolynomial p).roots.map fun z : ℂ => ‖z‖).prod at hn
  simpa only [Complex.norm_intCast] using hn

lemma mahler_ge_one {p : Polynomial ℤ} (hp : p ≠ 0) : 1 ≤ mahler p := by
  have ha := one_le_int_abs (Polynomial.leadingCoeff_ne_zero.mpr hp)
  have hb := one_le_max_prod (complexPolynomial p).roots
  exact le_trans (by norm_num : (1 : ℝ) ≤ 1 * 1)
    (mul_le_mul ha hb zero_le_one (le_trans zero_le_one ha))

lemma root_mem {p : Polynomial ℤ} (hp : p ≠ 0) {α : ℂ}
    (hα : aeval α p = 0) : α ∈ (complexPolynomial p).roots := by
  apply (Polynomial.mem_roots ((Polynomial.map_ne_zero_iff Int.cast_injective).mpr hp)).mpr
  simpa only [Polynomial.IsRoot, complexPolynomial, Polynomial.eval_map,
    Polynomial.aeval_def] using hα

lemma root_mul_mahler_ge_one {p : Polynomial ℤ} (hp : p ≠ 0)
    (hc : p.coeff 0 ≠ 0) {α : ℂ} (hα : aeval α p = 0) :
    1 ≤ ‖α‖ * mahler p := by
  obtain ⟨s, hs⟩ := Multiset.exists_cons_of_mem (root_mem hp hα)
  have heq := constant_term_product p
  rw [hs] at heq
  simp only [Multiset.map_cons, Multiset.prod_cons] at heq
  have hs_le := norm_prod_le_max_prod s
  have hs_nonneg : 0 ≤ (s.map fun z : ℂ => max 1 ‖z‖).prod :=
    le_trans zero_le_one (one_le_max_prod s)
  have hm : (s.map fun z : ℂ => max 1 ‖z‖).prod ≤
      max 1 ‖α‖ * (s.map fun z : ℂ => max 1 ‖z‖).prod := by
    simpa using mul_le_mul_of_nonneg_right (le_max_left 1 ‖α‖) hs_nonneg
  calc
    1 ≤ |(p.coeff 0 : ℝ)| := one_le_int_abs hc
    _ = |(p.leadingCoeff : ℝ)| *
      (‖α‖ * (s.map fun z : ℂ => ‖z‖).prod) := heq
    _ ≤ |(p.leadingCoeff : ℝ)| *
      (‖α‖ * (s.map fun z : ℂ => max 1 ‖z‖).prod) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs_le (norm_nonneg α))
        (abs_nonneg _)
    _ = ‖α‖ * (|(p.leadingCoeff : ℝ)| *
      (s.map fun z : ℂ => max 1 ‖z‖).prod) := by ring
    _ ≤ ‖α‖ * (|(p.leadingCoeff : ℝ)| *
      (max 1 ‖α‖ * (s.map fun z : ℂ => max 1 ‖z‖).prod)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hm (abs_nonneg _))
        (norm_nonneg α)
    _ = ‖α‖ * mahler p := by simp [mahler, hs]

lemma weil_ge_one {p : Polynomial ℤ} (hp : p ≠ 0) : 1 ≤ weil p := by
  exact Real.one_le_rpow (mahler_ge_one hp) (by positivity)

lemma weil_pow_degree {p : Polynomial ℤ} (hp : p ≠ 0) (hd : p.natDegree ≠ 0) :
    weil p ^ p.natDegree = mahler p := by
  simpa only [weil, one_div] using
    Real.rpow_inv_natCast_pow (le_trans zero_le_one (mahler_ge_one hp)) hd

lemma mahler_le_weil_sq {p : Polynomial ℤ} (hp : p ≠ 0)
    (hd1 : 1 ≤ p.natDegree) (hd2 : p.natDegree ≤ 2) :
    mahler p ≤ weil p ^ 2 := by
  have hw := weil_ge_one hp
  have heq := weil_pow_degree hp (by omega)
  have cases : p.natDegree = 1 ∨ p.natDegree = 2 := by omega
  rcases cases with hd | hd
  · rw [hd, pow_one] at heq
    rw [← heq]
    nlinarith
  · rw [hd] at heq
    exact heq.ge

lemma root_mul_weil_sq_ge_one {p : Polynomial ℤ} (hp : p ≠ 0)
    (hc : p.coeff 0 ≠ 0) (hd1 : 1 ≤ p.natDegree) (hd2 : p.natDegree ≤ 2)
    {α : ℂ} (hα : aeval α p = 0) : 1 ≤ ‖α‖ * weil p ^ 2 := by
  exact (root_mul_mahler_ge_one hp hc hα).trans
    (mul_le_mul_of_nonneg_left (mahler_le_weil_sq hp hd1 hd2) (norm_nonneg α))

lemma root_norm_ge_weil_inv_sq {p : Polynomial ℤ} (hp : p ≠ 0)
    (hc : p.coeff 0 ≠ 0) (hd1 : 1 ≤ p.natDegree) (hd2 : p.natDegree ≤ 2)
    {α : ℂ} (hα : aeval α p = 0) : (weil p ^ 2)⁻¹ ≤ ‖α‖ := by
  have hw : 0 < weil p := lt_of_lt_of_le zero_lt_one (weil_ge_one hp)
  have h := root_mul_weil_sq_ge_one hp hc hd1 hd2 hα
  have hdiv : 1 / weil p ^ 2 ≤ ‖α‖ :=
    (div_le_iff₀ (sq_pos_of_pos hw)).mpr h
  simpa only [one_div] using hdiv

lemma root_norm_ge_weil_neg_two {p : Polynomial ℤ} (hp : p ≠ 0)
    (hc : p.coeff 0 ≠ 0) (hd1 : 1 ≤ p.natDegree) (hd2 : p.natDegree ≤ 2)
    {α : ℂ} (hα : aeval α p = 0) : weil p ^ (-2 : ℝ) ≤ ‖α‖ := by
  have hw : 0 ≤ weil p := le_trans zero_le_one (weil_ge_one hp)
  rw [Real.rpow_neg hw, Real.rpow_two]
  exact root_norm_ge_weil_inv_sq hp hc hd1 hd2 hα

end HeightRoots
