import Mathlib

/-!
# Conjecture 00000008228: the Ehrhart function of a Weyl-orbit polytope is not monic

Clause 4 of conjecture 00000008228 ("semisimple rank law") asserts that the Ehrhart function of the
weight polytope `conv(W . lam)` is a monic polynomial whose degree is the semisimple rank.

We build the two rank-one root data on the lattice `X = Z` (roots `+-a`, coroots `+-b`, `a * b = 2`;
`(a, b) = (2, 1)` is the root datum of `SL_2`, `(a, b) = (1, 2)` that of `PGL_2`) as genuine Mathlib
`RootDatum`s, take the convex hull in `X (x) R = R` of the orbit of `lam` under Mathlib's
`RootPairing.weylGroup`, and count lattice points of its dilates.  For every `lam != 0` and every
lattice `Lam <= X` containing `lam` (the weight lattice `X` itself, the root lattice when it contains
`lam`, ...) the Ehrhart function is `t |-> 2 c t + 1` with `c = |lam / d| >= 1`, so no real polynomial
that agrees with it at the positive integers is monic.

In geometric Satake the polytope lives in the cocharacter lattice of `G`, i.e. the character lattice
of the dual group `G^vee`; for `G = PGL_2` (resp. `SL_2`) this is the `SL_2` (resp. `PGL_2`) datum
below.  Since both data are covered, the result does not depend on that choice.
-/

open Polynomial Set Pointwise

namespace C8228

/-! ## The rank-one root data on `Z` -/

lemma mul_bijective : Function.Bijective (LinearMap.mul ℤ ℤ) := by
  constructor
  · intro x y h
    simpa using LinearMap.congr_fun h 1
  · intro f
    exact ⟨f 1, LinearMap.ext_ring (by simp)⟩

lemma mul_flip_bijective : Function.Bijective (LinearMap.mul ℤ ℤ).flip := by
  constructor
  · intro x y h
    simpa using LinearMap.congr_fun h 1
  · intro f
    exact ⟨f 1, LinearMap.ext_ring (by simp)⟩

instance : (LinearMap.mul ℤ ℤ).IsPerfPair := ⟨mul_bijective, mul_flip_bijective⟩

lemma ne_zero_left {a b : ℤ} (hab : a * b = 2) : a ≠ 0 := by rintro rfl; simp at hab

lemma ne_zero_right {a b : ℤ} (hab : a * b = 2) : b ≠ 0 := by rintro rfl; simp at hab

lemma pm_injective {a : ℤ} (ha : a ≠ 0) : Function.Injective ![a, -a] := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega

/-- The rank-one root datum on `X = Z` with roots `a, -a` and coroots `b, -b`, where `a * b = 2`;
the pairing `X x X^vee -> Z` is multiplication. -/
def rk1 (a b : ℤ) (hab : a * b = 2) : RootDatum (Fin 2) ℤ ℤ where
  toLinearMap := LinearMap.mul ℤ ℤ
  root := ⟨![a, -a], pm_injective (ne_zero_left hab)⟩
  coroot := ⟨![b, -b], pm_injective (ne_zero_right hab)⟩
  root_coroot_two i := by fin_cases i <;> simp [hab]
  reflectionPerm _ := Equiv.swap 0 1
  reflectionPerm_root i j := by
    fin_cases i <;> fin_cases j <;> simp <;>
      first | linear_combination (-a) * hab | linear_combination a * hab
  reflectionPerm_coroot i j := by
    fin_cases i <;> fin_cases j <;> simp <;>
      first | linear_combination (-b) * hab | linear_combination b * hab

/-- The root datum of `SL_2`: character lattice `Z`, roots `+-2`, coroots `+-1`. -/
abbrev rootDatumSL2 : RootDatum (Fin 2) ℤ ℤ := rk1 2 1 (by norm_num)

/-- The root datum of `PGL_2`: character lattice `Z`, roots `+-1`, coroots `+-2`. -/
abbrev rootDatumPGL2 : RootDatum (Fin 2) ℤ ℤ := rk1 1 2 (by norm_num)

variable {a b : ℤ} (hab : a * b = 2)

lemma reflection_eq_neg (i : Fin 2) (x : ℤ) : (rk1 a b hab).reflection i x = -x := by
  rw [RootPairing.reflection_apply]
  fin_cases i <;> simp [rk1, RootPairing.coroot'] <;> linear_combination (-x) * hab

/-- Every element of the Weyl group acts on `X = Z` as `+1` or as `-1`. -/
lemma weyl_smul (g : (rk1 a b hab).Aut) (hg : g ∈ (rk1 a b hab).weylGroup) :
    (∀ x : ℤ, g • x = x) ∨ (∀ x : ℤ, g • x = -x) := by
  induction hg using RootPairing.weylGroup.induction with
  | mem i => exact Or.inr fun x => by simp [reflection_eq_neg]
  | one => exact Or.inl fun x => by simp
  | mul g h _ _ ihg ihh =>
    rcases ihg with ihg | ihg <;> rcases ihh with ihh | ihh
    · exact Or.inl fun x => by rw [mul_smul, ihh, ihg]
    · exact Or.inr fun x => by rw [mul_smul, ihh, ihg]
    · exact Or.inr fun x => by rw [mul_smul, ihh, ihg]
    · exact Or.inl fun x => by rw [mul_smul, ihh, ihg, neg_neg]

/-- The Weyl-group orbit of `lam` is `{lam, -lam}`. -/
lemma orbit_eq (lam : ℤ) : MulAction.orbit (rk1 a b hab).weylGroup lam = {lam, -lam} := by
  ext x
  constructor
  · rintro ⟨⟨g, hg⟩, rfl⟩
    rcases weyl_smul hab g hg with h | h
    · exact Or.inl (h lam)
    · exact Or.inr (h lam)
  · rintro (rfl | rfl)
    · exact MulAction.mem_orbit_self _
    · refine ⟨RootPairing.weylGroup.ofIdx _ 0, ?_⟩
      simp [reflection_eq_neg]

/-! ## The weight polytope, the Ehrhart function and the semisimple rank -/

/-- The weight polytope `conv(W . lam)` of `lam` in `X (x) R = R`, for a root datum on `X = Z`:
the real convex hull of the orbit of `lam` under Mathlib's Weyl group `RootPairing.weylGroup`. -/
def weightPolytope {ι N : Type*} [AddCommGroup N] (P : RootDatum ι ℤ N) (lam : ℤ) : Set ℝ :=
  convexHull ℝ ((Int.cast : ℤ → ℝ) '' MulAction.orbit P.weylGroup lam)

/-- The Ehrhart function of `Q ⊆ R` with respect to a lattice `Lam ≤ Z`: `t ↦ #(t Q ∩ Lam)`. -/
noncomputable def ehrhart (Lam : AddSubgroup ℤ) (Q : Set ℝ) (t : ℕ) : ℕ :=
  {x : ℤ | x ∈ Lam ∧ (x : ℝ) ∈ (t : ℝ) • Q}.ncard

/-- The semisimple rank of a root datum on `X`: the rank of its root lattice `Z Phi ≤ X`. -/
noncomputable def semisimpleRank {ι N : Type*} [AddCommGroup N] (P : RootDatum ι ℤ N) : ℕ :=
  Module.finrank ℤ (P.rootSpan ℤ)

lemma range_root : range (rk1 a b hab).root = {a, -a} := by
  ext x
  simp [rk1, eq_comm]
  exact or_comm

theorem semisimpleRank_rk1 : semisimpleRank (rk1 a b hab) = 1 := by
  have ha : -a ≠ 0 := neg_ne_zero.2 (ne_zero_left hab)
  unfold semisimpleRank RootPairing.rootSpan
  rw [range_root, Submodule.span_insert_eq_span
    (Submodule.mem_span_singleton.2 ⟨-1, by simp⟩)]
  rw [← (LinearEquiv.toSpanNonzeroSingleton ℤ ℤ (-a) ha).finrank_eq, Module.finrank_self]

lemma weightPolytope_eq (lam : ℤ) :
    weightPolytope (rk1 a b hab) lam = Icc (-|(lam : ℝ)|) |(lam : ℝ)| := by
  rw [weightPolytope, orbit_eq, Set.image_pair, Int.cast_neg, convexHull_pair, segment_eq_uIcc]
  rcases le_total 0 (lam : ℝ) with h | h
  · rw [uIcc_of_ge (by linarith), abs_of_nonneg h]
  · rw [uIcc_of_le (by linarith), abs_of_nonpos h, neg_neg]

lemma smul_Icc_abs (t : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    (t : ℝ) • Icc (-c) c = Icc (-(t * c)) (t * c) := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · rw [Nat.cast_zero, zero_smul_set (nonempty_Icc.2 (by linarith))]
    simp only [zero_mul, neg_zero, Icc_self]
    rfl
  · rw [LinearOrderedField.smul_Icc (by positivity), mul_neg]

lemma ehrhart_weightPolytope (Lam : AddSubgroup ℤ) (lam : ℤ) (t : ℕ) :
    ehrhart Lam (weightPolytope (rk1 a b hab) lam) t =
      {x : ℤ | x ∈ Lam ∧ |x| ≤ t * |lam|}.ncard := by
  rw [ehrhart, weightPolytope_eq, smul_Icc_abs _ _ (abs_nonneg _)]
  congr 1
  ext x
  simp only [mem_ofPred_eq, mem_Icc, ← abs_le]
  constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1, ?_⟩ <;> exact_mod_cast h2

/-- Every lattice `Lam ≤ Z` is `d Z` for some `d`. -/
lemma lattice_dvd (Lam : AddSubgroup ℤ) : ∃ d : ℤ, ∀ x, x ∈ Lam ↔ d ∣ x := by
  let I : Ideal ℤ := AddSubgroup.toIntSubmodule Lam
  refine ⟨Submodule.IsPrincipal.generator I, fun x => ?_⟩
  rw [← Ideal.mem_span_singleton, Ideal.span_singleton_generator]
  rfl

/-- `#{x ∈ d Z : |x| ≤ t |d m|} = 2 |m| t + 1`. -/
lemma count (d m : ℤ) (hd : d ≠ 0) (t : ℕ) :
    {x : ℤ | d ∣ x ∧ |x| ≤ t * |d * m|}.ncard = 2 * m.natAbs * t + 1 := by
  have hd' : 0 < |d| := abs_pos.2 hd
  have hS : {x : ℤ | d ∣ x ∧ |x| ≤ t * |d * m|} =
      (fun k => d * k) '' Icc (-(t * |m|)) (t * |m|) := by
    ext x
    simp only [mem_ofPred_eq, mem_image, mem_Icc, ← abs_le]
    constructor
    · rintro ⟨⟨k, rfl⟩, hk⟩
      refine ⟨k, ?_, rfl⟩
      rw [abs_mul, abs_mul] at hk
      have : |d| * |k| ≤ |d| * (t * |m|) := by linarith
      exact le_of_mul_le_mul_left this hd'
    · rintro ⟨k, hk, rfl⟩
      refine ⟨dvd_mul_right d k, ?_⟩
      rw [abs_mul, abs_mul]
      have := mul_le_mul_of_nonneg_left hk hd'.le
      linarith
  rw [hS, ncard_image_of_injective _ (mul_right_injective₀ hd), ← Finset.coe_Icc,
    ncard_coe_finset, Int.card_Icc, Int.abs_eq_natAbs m,
    show ((t : ℤ) * (m.natAbs : ℤ)) = ((t * m.natAbs : ℕ) : ℤ) by push_cast; ring,
    show 2 * m.natAbs * t + 1 = 2 * (t * m.natAbs) + 1 by ring]
  generalize t * m.natAbs = N
  omega

/-! ## Main results -/

/-- **Ehrhart function in the weight lattice.** For the rank-one root datum `rk1 a b` and any
weight `lam ∈ X = Z`, the Ehrhart function of `conv(W . lam)` with respect to `X` is
`t ↦ 2 |lam| t + 1`. -/
theorem ehrhart_top (lam : ℤ) (t : ℕ) :
    ehrhart ⊤ (weightPolytope (rk1 a b hab) lam) t = 2 * lam.natAbs * t + 1 := by
  rw [ehrhart_weightPolytope]
  have := count 1 lam one_ne_zero t
  simp only [one_dvd, true_and, one_mul] at this
  simpa only [AddSubgroup.mem_top, true_and] using this

/-- **Ehrhart function in an arbitrary lattice.** For every nonzero weight `lam` and every lattice
`Lam ≤ X` containing `lam`, the Ehrhart function of `conv(W . lam)` with respect to `Lam` is
`t ↦ 2 c t + 1` for some integer `c ≥ 1` (namely `c = |lam| / [X : Lam]`). -/
theorem ehrhart_formula (lam : ℤ) (hlam : lam ≠ 0) (Lam : AddSubgroup ℤ) (hmem : lam ∈ Lam) :
    ∃ c : ℕ, 0 < c ∧ ∀ t, ehrhart Lam (weightPolytope (rk1 a b hab) lam) t = 2 * c * t + 1 := by
  obtain ⟨d, hd⟩ := lattice_dvd Lam
  obtain ⟨m, rfl⟩ := (hd _).1 hmem
  have hd0 : d ≠ 0 := by rintro rfl; simp at hlam
  have hm0 : m ≠ 0 := by rintro rfl; simp at hlam
  refine ⟨m.natAbs, Int.natAbs_pos.2 hm0, fun t => ?_⟩
  rw [ehrhart_weightPolytope]
  simp_rw [hd]
  exact count d m hd0 t

/-- A function `t ↦ 2 c t + 1` with `c ≥ 1` agrees at the positive integers with no monic real
polynomial (of any degree). -/
theorem not_monic_of_linear (c : ℕ) (hc : 0 < c) (L : ℕ → ℕ) (hL : ∀ t, L t = 2 * c * t + 1)
    (p : ℝ[X]) (hp : ∀ t : ℕ, 0 < t → p.eval (t : ℝ) = L t) : ¬ p.Monic := by
  have hpq : p = C (2 * c : ℝ) * X + C 1 := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine Set.Infinite.mono (s := Set.range (fun n : ℕ => ((n + 1 : ℕ) : ℝ))) ?_ ?_
    · rintro _ ⟨n, rfl⟩
      simp only [mem_ofPred_eq, hp _ n.succ_pos, hL, eval_add, eval_mul, eval_C, eval_X]
      push_cast
      ring
    · exact Set.infinite_range_of_injective (fun i j h => by simpa using h)
  intro hm
  have h1 := hm.leadingCoeff
  rw [hpq, leadingCoeff_linear (by positivity)] at h1
  have h2 : ((2 * c : ℕ) : ℝ) = ((1 : ℕ) : ℝ) := by push_cast; exact h1
  have := Nat.cast_injective h2
  omega

/-- **Main theorem (clause 4 fails).** For each rank-one root datum `rk1 a b` (in particular
those of `SL_2` and `PGL_2`), every nonzero weight `lam ∈ X = Z` and every lattice `Lam ≤ X`
containing `lam`, no real polynomial that agrees with the Ehrhart function
`t ↦ #(t . conv(W . lam) ∩ Lam)` at all positive integers `t` is monic. -/
theorem ehrhart_not_monic (lam : ℤ) (hlam : lam ≠ 0) (Lam : AddSubgroup ℤ) (hmem : lam ∈ Lam) :
    ¬ ∃ p : ℝ[X], p.Monic ∧
      ∀ t : ℕ, 0 < t → p.eval (t : ℝ) = ehrhart Lam (weightPolytope (rk1 a b hab) lam) t := by
  rintro ⟨p, hm, hp⟩
  obtain ⟨c, hc, hL⟩ := ehrhart_formula hab lam hlam Lam hmem
  exact not_monic_of_linear c hc _ hL p hp hm

/-- **Clause 4 as stated fails**: no monic polynomial of degree the semisimple rank
(`= 1`, `semisimpleRank_rk1`) agrees with the Ehrhart function at the positive integers, for any
nonzero weight `lam` and any lattice `Lam ≤ X` containing `lam`; in particular for `Lam = X` (`⊤`)
and, when `lam ∈ Z Phi`, for the root lattice `Lam = Z Phi`. -/
theorem semisimple_rank_law_fails (lam : ℤ) (hlam : lam ≠ 0) (Lam : AddSubgroup ℤ)
    (hmem : lam ∈ Lam) :
    ¬ ∃ p : ℝ[X], p.Monic ∧ p.natDegree = semisimpleRank (rk1 a b hab) ∧
      ∀ t : ℕ, 0 < t → p.eval (t : ℝ) = ehrhart Lam (weightPolytope (rk1 a b hab) lam) t :=
  fun ⟨p, hm, _, hp⟩ => ehrhart_not_monic hab lam hlam Lam hmem ⟨p, hm, hp⟩

/-- The root-lattice convention: `Lam = Z Phi`, for a nonzero `lam ∈ Z Phi`. -/
theorem semisimple_rank_law_fails_rootLattice (lam : ℤ) (hlam : lam ≠ 0)
    (hmem : lam ∈ (rk1 a b hab).rootSpan ℤ) :
    ¬ ∃ p : ℝ[X], p.Monic ∧ p.natDegree = semisimpleRank (rk1 a b hab) ∧
      ∀ t : ℕ, 0 < t → p.eval (t : ℝ) =
        ehrhart ((rk1 a b hab).rootSpan ℤ).toAddSubgroup (weightPolytope (rk1 a b hab) lam) t :=
  semisimple_rank_law_fails hab lam hlam _ hmem

/-- Concrete instance: `SL_2`, `lam = 1` (the fundamental weight), weight lattice `X`:
the Ehrhart function is `2 t + 1`. -/
example (t : ℕ) : ehrhart ⊤ (weightPolytope rootDatumSL2 1) t = 2 * t + 1 := by
  rw [ehrhart_top]; simp

end C8228
