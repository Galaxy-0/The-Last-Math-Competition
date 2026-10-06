import Mathlib

/-!
# Conjecture 00000007794 is false

`L(P, k) = #(kP ∩ ℤᵈ)` are the coefficients of the Ehrhart series `∑_{k ≥ 0} L(P, k) tᵏ` of a
lattice polytope `P`. The conjecture's first clause: there is a universal constant `c` with
`L(P, k)² ≥ L(P, k - 1) L(P, k + 1) (1 + c / k²)` for all lattice polytopes `P` and all `k ≥ 1`
("log-concavity with an explicit stability margin").

We refute this for every `c > -1` (in particular for every positive margin and for plain
log-concavity `c = 0`) with the Reeve tetrahedra
`T_r = conv{(0,0,0), (1,0,0), (0,1,0), (1,1,r)} ⊂ ℝ³` at `k = 1`:
`L(T_r, 0) = 1`, `L(T_r, 1) ≤ 4` (the only lattice points are the vertices) and
`L(T_r, 2) ≥ r + 1` (the points `(1,1,z)`, `0 ≤ z ≤ r`), so `L(1)² ≤ 16 < (r + 1)(1 + c)` for `r`
large.
-/

open Set Pointwise

namespace C7794

/-- Ambient space `ℝ³`. -/
abbrev E3 := Fin 3 → ℝ

/-- The integer lattice `ℤ³ ⊂ ℝ³`. -/
def toR (p : Fin 3 → ℤ) : E3 := fun i => (p i : ℝ)

/-- A lattice polytope: the convex hull of a nonempty finite set of lattice points. -/
def IsLatticePolytope (P : Set E3) : Prop :=
  ∃ V : Finset (Fin 3 → ℤ), V.Nonempty ∧ P = convexHull ℝ (toR '' (V : Set (Fin 3 → ℤ)))

/-- Lattice points of a set. -/
def latticePts (S : Set E3) : Set (Fin 3 → ℤ) := toR ⁻¹' S

/-- Ehrhart counting function `L(P, k) = #(kP ∩ ℤ³)`. -/
noncomputable def ehrhart (P : Set E3) (k : ℕ) : ℕ := (latticePts ((k : ℝ) • P)).ncard

/-- The vertex list of the Reeve tetrahedron `T_r`. -/
def vZ (r : ℕ) : Fin 4 → Fin 3 → ℤ := ![![0, 0, 0], ![1, 0, 0], ![0, 1, 0], ![1, 1, (r : ℤ)]]

/-- The vertex set of `T_r`. -/
def V (r : ℕ) : Finset (Fin 3 → ℤ) := Finset.univ.image (vZ r)

/-- The Reeve tetrahedron `T_r = conv{(0,0,0), (1,0,0), (0,1,0), (1,1,r)}`. -/
def reeve (r : ℕ) : Set E3 := convexHull ℝ (toR '' (V r : Set (Fin 3 → ℤ)))

lemma reeve_isLatticePolytope (r : ℕ) : IsLatticePolytope (reeve r) :=
  ⟨V r, Finset.univ_nonempty.image _, rfl⟩

lemma reeve_nonempty (r : ℕ) : (reeve r).Nonempty :=
  ⟨_, subset_convexHull ℝ _ ⟨vZ r 0, by simp [V], rfl⟩⟩

/-- Facet inequalities of `s • T_r`. -/
def H (r : ℕ) (s : ℝ) : Set E3 :=
  {y | 0 ≤ y 2 ∧ y 2 ≤ r * y 0 ∧ y 2 ≤ r * y 1 ∧ r * (y 0 + y 1) ≤ s * r + y 2}

lemma convex_H (r : ℕ) : Convex ℝ (H r 1) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
  obtain ⟨hy1, hy2, hy3, hy4⟩ := hy
  simp only [H, mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  refine ⟨by nlinarith [mul_nonneg ha hx1, mul_nonneg hb hy1], ?_, ?_, ?_⟩
  · nlinarith [mul_nonneg ha (sub_nonneg.2 hx2), mul_nonneg hb (sub_nonneg.2 hy2)]
  · nlinarith [mul_nonneg ha (sub_nonneg.2 hx3), mul_nonneg hb (sub_nonneg.2 hy3)]
  · nlinarith [mul_nonneg ha (sub_nonneg.2 hx4), mul_nonneg hb (sub_nonneg.2 hy4)]

lemma reeve_subset_H (r : ℕ) : reeve r ⊆ H r 1 := by
  refine convexHull_min ?_ (convex_H r)
  rintro _ ⟨p, hp, rfl⟩
  simp only [V, Finset.coe_image, Finset.coe_univ, image_univ, mem_range] at hp
  obtain ⟨i, rfl⟩ := hp
  fin_cases i <;> simp [H, toR, vZ]
  linarith

/-- Every point of `k • T_r` satisfies the facet inequalities of `k • T_r`. -/
lemma smul_reeve_subset (r : ℕ) (k : ℝ) (hk : 0 ≤ k) : k • reeve r ⊆ H r k := by
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨h1, h2, h3, h4⟩ := reeve_subset_H r hy
  simp only [H, mem_ofPred_eq, Pi.smul_apply, smul_eq_mul]
  refine ⟨mul_nonneg hk h1, ?_, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left h2 hk]
  · nlinarith [mul_le_mul_of_nonneg_left h3 hk]
  · nlinarith [mul_le_mul_of_nonneg_left h4 hk]

lemma le_of_mul_le' {r a b : ℤ} (hr : 1 ≤ r) (h : r * a ≤ r * b) : a ≤ b :=
  le_of_mul_le_mul_left h (by omega)

/-- Integer form of the facet inequalities. -/
lemma int_ineqs {r : ℕ} {s : ℕ} {p : Fin 3 → ℤ} (h : toR p ∈ H r s) :
    0 ≤ p 2 ∧ p 2 ≤ r * p 0 ∧ p 2 ≤ r * p 1 ∧ r * (p 0 + p 1) ≤ s * r + p 2 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [toR] at h1 h2 h3 h4
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3, by exact_mod_cast h4⟩

/-- `L(T_r, 0) = 1`. -/
lemma ehrhart_zero (r : ℕ) : ehrhart (reeve r) 0 = 1 := by
  have h0 : ((0 : ℕ) : ℝ) • reeve r = 0 := by
    rw [Nat.cast_zero]; exact zero_smul_set (reeve_nonempty r)
  have : latticePts (((0 : ℕ) : ℝ) • reeve r) = {0} := by
    rw [h0]; ext p
    simp only [latticePts, mem_preimage, Set.mem_zero, mem_singleton_iff]
    constructor
    · intro hp; funext i; have := congrFun hp i; simpa [toR] using this
    · rintro rfl; funext i; simp [toR]
  rw [ehrhart, this, ncard_singleton]

/-- Every lattice point of `1 • T_r` is one of the four vertices (`r ≥ 1`). -/
lemma latticePts_one (r : ℕ) (hr : 1 ≤ r) :
    latticePts (((1 : ℕ) : ℝ) • reeve r) ⊆ (V r : Set (Fin 3 → ℤ)) := by
  intro p hp
  have hH := smul_reeve_subset r 1 zero_le_one (by simpa [latticePts] using hp)
  obtain ⟨h1, h2, h3, h4⟩ := int_ineqs (s := 1) (by exact_mod_cast hH)
  have hr' : (1 : ℤ) ≤ r := by exact_mod_cast hr
  push_cast at h4
  have e : (r : ℤ) * (p 0 + p 1) = r * p 0 + r * p 1 := by ring
  simp only [V, Finset.coe_image, Finset.coe_univ, image_univ, mem_range]
  rcases eq_or_lt_of_le h1 with hz | hz
  · -- `z = 0`: `x, y ≥ 0`, `x + y ≤ 1`
    rw [← hz] at h2 h3 h4
    have hx : 0 ≤ p 0 := le_of_mul_le' hr' (by simpa using h2)
    have hy : 0 ≤ p 1 := le_of_mul_le' hr' (by simpa using h3)
    have hxy : p 0 + p 1 ≤ 1 := le_of_mul_le' hr' (by simpa using h4)
    have hp0 : p 0 = 0 ∨ p 0 = 1 := by omega
    rcases hp0 with h0 | h0
    · have h1' : p 1 = 0 ∨ p 1 = 1 := by omega
      rcases h1' with h1' | h1'
      · exact ⟨0, by funext i; fin_cases i <;> simp [vZ, h0, h1', hz]⟩
      · exact ⟨2, by funext i; fin_cases i <;> simp [vZ, h0, h1', hz]⟩
    · have h1' : p 1 = 0 := by omega
      exact ⟨1, by funext i; fin_cases i <;> simp [vZ, h0, h1', hz]⟩
  · -- `z > 0`: `x, y ≥ 1`, which forces `z = r` and `x = y = 1`
    have hx : 1 ≤ p 0 := by
      by_contra hc
      have : (r : ℤ) * p 0 ≤ r * 0 := mul_le_mul_of_nonneg_left (by omega) (by omega)
      linarith
    have hy : 1 ≤ p 1 := by
      by_contra hc
      have : (r : ℤ) * p 1 ≤ r * 0 := mul_le_mul_of_nonneg_left (by omega) (by omega)
      linarith
    have h2r : (r : ℤ) * 2 ≤ r * (p 0 + p 1) := mul_le_mul_of_nonneg_left (by omega) (by omega)
    have hzr : p 2 = r := by linarith
    have hxy : p 0 + p 1 ≤ 2 := le_of_mul_le' hr' (by linarith)
    have h0 : p 0 = 1 := by omega
    have h1' : p 1 = 1 := by omega
    exact ⟨3, by funext i; fin_cases i <;> simp [vZ, h0, h1', hzr]⟩

/-- `L(T_r, 1) ≤ 4`. -/
lemma ehrhart_one_le (r : ℕ) (hr : 1 ≤ r) : ehrhart (reeve r) 1 ≤ 4 := by
  calc ehrhart (reeve r) 1 ≤ ((V r : Set (Fin 3 → ℤ))).ncard :=
        ncard_le_ncard (latticePts_one r hr) (Finset.finite_toSet _)
    _ = (V r).card := ncard_coe_finset _
    _ ≤ 4 := by
        exact (Finset.card_image_le).trans (by simp)

/-- The lattice points of `2 • T_r` form a finite set (the proof puts them in the box
`[0,4] × [0,4] × [0,2r]`). -/
lemma latticePts_two_finite (r : ℕ) (hr : 1 ≤ r) :
    (latticePts (((2 : ℕ) : ℝ) • reeve r)).Finite := by
  refine (finite_Icc (![0, 0, 0] : Fin 3 → ℤ) ![4, 4, 2 * r]).subset ?_
  intro p hp
  have hH := smul_reeve_subset r 2 zero_le_two (by simpa [latticePts] using hp)
  obtain ⟨h1, h2, h3, h4⟩ := int_ineqs (s := 2) (by exact_mod_cast hH)
  have hr' : (1 : ℤ) ≤ r := by exact_mod_cast hr
  push_cast at h4
  have e : (r : ℤ) * (p 0 + p 1) = r * p 0 + r * p 1 := by ring
  have hx : 0 ≤ p 0 := le_of_mul_le' hr' (by linarith)
  have hy : 0 ≤ p 1 := le_of_mul_le' hr' (by linarith)
  have hz : p 2 ≤ 2 * r := by linarith
  have hxy : p 0 + p 1 ≤ 4 := le_of_mul_le' hr' (by linarith)
  constructor <;> intro i <;> fin_cases i <;> simp <;> omega

/-- `(1, 1, z) ∈ 2 • T_r` for `0 ≤ z ≤ r`. -/
lemma mem_two_reeve (r : ℕ) (hr : 1 ≤ r) (z : ℕ) (hz : z ≤ r) :
    toR ![1, 1, (z : ℤ)] ∈ ((2 : ℕ) : ℝ) • reeve r := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hzr : (z : ℝ) ≤ r := by exact_mod_cast hz
  set w : Fin 4 → ℝ := ![z / (2 * r), 1 / 2 - z / (2 * r), 1 / 2 - z / (2 * r), z / (2 * r)]
  have hq : (z : ℝ) / (2 * r) ≤ 1 / 2 := by rw [div_le_iff₀ (by positivity)]; linarith
  have hmem : ∑ i, w i • toR (vZ r i) ∈ reeve r := by
    refine (convex_convexHull ℝ _).sum_mem (fun i _ => ?_) ?_
      (fun i _ => subset_convexHull ℝ _ ⟨vZ r i, by simp [V], rfl⟩)
    · fin_cases i <;> simp [w] <;> first | positivity | linarith
    · simp [w, Fin.sum_univ_four]; ring
  refine ⟨_, hmem, ?_⟩
  funext i
  fin_cases i <;> simp [w, toR, vZ, Fin.sum_univ_four]
  field_simp

/-- `L(T_r, 2) ≥ r + 1`. -/
lemma ehrhart_two_ge (r : ℕ) (hr : 1 ≤ r) : r + 1 ≤ ehrhart (reeve r) 2 := by
  set S : Finset (Fin 3 → ℤ) := (Finset.range (r + 1)).image fun z : ℕ => ![1, 1, (z : ℤ)]
  have hS : S.card = r + 1 := by
    rw [Finset.card_image_of_injective _ (fun a b h => by
      have := congrFun h 2; simpa using this), Finset.card_range]
  have hsub : (S : Set (Fin 3 → ℤ)) ⊆ latticePts (((2 : ℕ) : ℝ) • reeve r) := by
    intro p hp
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hp
    exact mem_two_reeve r hr z (by simpa [Nat.lt_succ_iff] using hz)
  have := ncard_le_ncard hsub (latticePts_two_finite r hr)
  rw [ncard_coe_finset, hS] at this
  exact this

/-- At `k = 1`, `T_r` violates `L(1)² ≥ L(0) L(2) (1 + c)` as soon as `(r + 1)(1 + c) > 16`. -/
theorem reeve_violates (r : ℕ) (hr : 1 ≤ r) (c : ℝ) (hc : -1 < c)
    (hbig : 16 < ((r : ℝ) + 1) * (1 + c)) :
    (ehrhart (reeve r) 1 : ℝ) ^ 2 <
      (ehrhart (reeve r) (1 - 1) : ℝ) * ehrhart (reeve r) (1 + 1) * (1 + c / ((1 : ℕ) : ℝ) ^ 2) := by
  have h1 : (ehrhart (reeve r) 1 : ℝ) ≤ 4 := by exact_mod_cast ehrhart_one_le r hr
  have h2 : (r : ℝ) + 1 ≤ ehrhart (reeve r) 2 := by exact_mod_cast ehrhart_two_ge r hr
  have h0 : ehrhart (reeve r) (1 - 1) = 1 := ehrhart_zero r
  rw [h0]
  norm_num
  have hpos : (0 : ℝ) ≤ ehrhart (reeve r) 1 := Nat.cast_nonneg _
  nlinarith

/-- **Conjecture 00000007794 is false** (its first clause). There is no constant `c > -1` (in
particular no `c ≥ 0`) such that `L(P, k)² ≥ L(P, k - 1) L(P, k + 1) (1 + c / k²)` for every
lattice polytope `P ⊂ ℝ³` and every `k ≥ 1`: for each such `c` a Reeve tetrahedron violates it at
`k = 1`. Also `T_16` violates plain log-concavity `L(1)² ≥ L(0) L(2)`. -/
theorem conjecture_7794_false :
    ¬ (∃ c : ℝ, -1 < c ∧ ∀ P : Set E3, IsLatticePolytope P → ∀ k : ℕ, 1 ≤ k →
        (ehrhart P (k - 1) : ℝ) * ehrhart P (k + 1) * (1 + c / (k : ℝ) ^ 2) ≤ (ehrhart P k : ℝ) ^ 2) ∧
    (∀ c : ℝ, -1 < c → ∃ r : ℕ, 1 ≤ r ∧ IsLatticePolytope (reeve r) ∧
        (ehrhart (reeve r) 1 : ℝ) ^ 2 <
          (ehrhart (reeve r) 0 : ℝ) * ehrhart (reeve r) 2 * (1 + c / ((1 : ℕ) : ℝ) ^ 2)) ∧
    (ehrhart (reeve 16) 1) ^ 2 < ehrhart (reeve 16) 0 * ehrhart (reeve 16) 2 := by
  have key : ∀ c : ℝ, -1 < c → ∃ r : ℕ, 1 ≤ r ∧ IsLatticePolytope (reeve r) ∧
      (ehrhart (reeve r) 1 : ℝ) ^ 2 <
        (ehrhart (reeve r) 0 : ℝ) * ehrhart (reeve r) 2 * (1 + c / ((1 : ℕ) : ℝ) ^ 2) := by
    intro c hc
    have hc1 : 0 < 1 + c := by linarith
    refine ⟨⌈16 / (1 + c)⌉₊ + 1, by omega, reeve_isLatticePolytope _, ?_⟩
    have := reeve_violates (⌈16 / (1 + c)⌉₊ + 1) (by omega) c hc ?_
    · simpa using this
    · have h := Nat.le_ceil (16 / (1 + c))
      have h' : 16 < (16 / (1 + c) + 1) * (1 + c) := by
        rw [add_mul, div_mul_cancel₀ _ hc1.ne']; linarith
      push_cast
      nlinarith
  refine ⟨fun ⟨c, hc, H⟩ => ?_, key, ?_⟩
  · obtain ⟨r, -, hP, hv⟩ := key c hc
    have := H _ hP 1 le_rfl
    simp only [Nat.sub_self] at this
    linarith
  · have h1 := ehrhart_one_le 16 (by norm_num)
    have h2 := ehrhart_two_ge 16 (by norm_num)
    rw [ehrhart_zero]
    nlinarith

end C7794
