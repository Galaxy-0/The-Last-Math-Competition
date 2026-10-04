import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.Group.Pointwise.Set.Scalar
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open scoped Pointwise
noncomputable section
namespace LatticeSeparation
abbrev Z3 := ℤ × (ℤ × ℤ)
abbrev R3 := ℝ × (ℝ × ℝ)
def box (m n p : ℕ) : Finset Z3 :=
  (Finset.Icc 0 (m : ℤ)).product
    ((Finset.Icc 0 (n : ℤ)).product (Finset.Icc 0 (p : ℤ)))
def K (m n p : ℕ) : Set R3 :=
  Set.Icc 0 (m : ℝ) ×ˢ (Set.Icc 0 (n : ℝ) ×ˢ Set.Icc 0 (p : ℝ))
def embed (x : Z3) : R3 := (x.1, (x.2.1, x.2.2))

theorem mem_box (m n p : ℕ) (x : Z3) : x ∈ box m n p ↔
    (0 ≤ x.1 ∧ x.1 ≤ m) ∧ (0 ≤ x.2.1 ∧ x.2.1 ≤ n) ∧
      (0 ≤ x.2.2 ∧ x.2.2 ≤ p) := by simp [box]
theorem actual_card (m n p : ℕ) : (box m n p).card = (m+1)*(n+1)*(p+1) := by
  simp [box, Finset.card_product, Int.card_Icc, mul_assoc]
theorem actual_compact (m n p : ℕ) : IsCompact (K m n p) :=
  isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
theorem actual_convex (m n p : ℕ) : Convex ℝ (K m n p) :=
  (convex_Icc 0 (m : ℝ)).prod ((convex_Icc 0 (n : ℝ)).prod (convex_Icc 0 (p : ℝ)))

theorem split_coordinate (m : ℕ) (x : ℤ) (hx : 0 ≤ x) (hm : x ≤ 2*(m : ℤ)) :
    ∃ a b : ℤ, (0 ≤ a ∧ a ≤ m) ∧ (0 ≤ b ∧ b ≤ m) ∧ a+b=x := by
  by_cases h : x ≤ m
  · exact ⟨x, 0, ⟨hx,h⟩, ⟨by omega, by omega⟩, by omega⟩
  · exact ⟨m, x-m, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, by omega⟩

theorem actual_sumset (m n p : ℕ) : box m n p + box m n p = box (2*m) (2*n) (2*p) := by
  ext x
  rw [Finset.mem_add, mem_box]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    rw [mem_box] at ha hb
    dsimp
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    omega
  · intro hx
    norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hx
    obtain ⟨a0,b0,ha0,hb0,he0⟩ := split_coordinate m x.1 hx.1.1 hx.1.2
    obtain ⟨a1,b1,ha1,hb1,he1⟩ := split_coordinate n x.2.1 hx.2.1.1 hx.2.1.2
    obtain ⟨a2,b2,ha2,hb2,he2⟩ := split_coordinate p x.2.2 hx.2.2.1 hx.2.2.2
    refine ⟨(a0,(a1,a2)), (mem_box _ _ _ _).mpr ⟨ha0,ha1,ha2⟩,
      (b0,(b1,b2)), (mem_box _ _ _ _).mpr ⟨hb0,hb1,hb2⟩, ?_⟩
    exact Prod.ext he0 (Prod.ext he1 he2)

theorem dilation_bounds (m n p t : ℕ) (ht : 0 < t) (u : R3) :
    u ∈ (t : ℝ) • K m n p ↔
    (0 ≤ u.1 ∧ u.1 ≤ (t*m : ℕ)) ∧
    (0 ≤ u.2.1 ∧ u.2.1 ≤ (t*n : ℕ)) ∧
    (0 ≤ u.2.2 ∧ u.2.2 ≤ (t*p : ℕ)) := by
  have htr : 0 < (t : ℝ) := by exact_mod_cast ht
  rw [Set.mem_smul_set]
  constructor
  · rintro ⟨v,hv,rfl⟩
    rcases hv with ⟨⟨hv0,hv0'⟩,⟨hv1,hv1'⟩,⟨hv2,hv2'⟩⟩
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Nat.cast_mul]
    exact ⟨⟨mul_nonneg htr.le hv0, mul_le_mul_of_nonneg_left hv0' htr.le⟩,
      ⟨mul_nonneg htr.le hv1, mul_le_mul_of_nonneg_left hv1' htr.le⟩,
      ⟨mul_nonneg htr.le hv2, mul_le_mul_of_nonneg_left hv2' htr.le⟩⟩
  · rintro ⟨⟨hu0,hu0'⟩,⟨hu1,hu1'⟩,⟨hu2,hu2'⟩⟩
    refine ⟨(u.1/t,(u.2.1/t,u.2.2/t)), ?_, ?_⟩
    · change (0 ≤ u.1/t ∧ u.1/t ≤ (m : ℝ)) ∧
        (0 ≤ u.2.1/t ∧ u.2.1/t ≤ (n : ℝ)) ∧
        (0 ≤ u.2.2/t ∧ u.2.2/t ≤ (p : ℝ))
      simp only [Nat.cast_mul] at hu0' hu1' hu2'
      refine ⟨⟨div_nonneg hu0 htr.le, (div_le_iff₀ htr).mpr ?_⟩,
        ⟨div_nonneg hu1 htr.le, (div_le_iff₀ htr).mpr ?_⟩,
        ⟨div_nonneg hu2 htr.le, (div_le_iff₀ htr).mpr ?_⟩⟩ <;> nlinarith
    · ext <;> simp [smul_eq_mul, mul_div_cancel₀, ne_of_gt htr]

theorem actual_lattice_points (m n p t : ℕ) (x : Z3) :
    x ∈ box (t*m) (t*n) (t*p) ↔ embed x ∈ (t : ℝ) • K m n p := by
  by_cases ht : t = 0
  · subst t
    simp only [Nat.zero_mul, Nat.cast_zero, mem_box, Set.mem_smul_set]
    constructor
    · intro hx
      have hz : x = 0 := by
        apply Prod.ext
        · dsimp; omega
        · apply Prod.ext <;> dsimp <;> omega
      subst x
      refine ⟨0, ?_, by simp [embed]⟩
      simp only [K, Set.mem_prod, Set.mem_Icc, Prod.fst_zero, Prod.snd_zero, le_refl, true_and]
      exact ⟨Nat.cast_nonneg m, Nat.cast_nonneg n, Nat.cast_nonneg p⟩
    · rintro ⟨v,hv,h⟩
      have hc : x.1 = 0 ∧ x.2.1 = 0 ∧ x.2.2 = 0 := by simpa [embed] using h.symm
      have hz : x = 0 := Prod.ext hc.1 (Prod.ext hc.2.1 hc.2.2)
      subst x
      simp
  · rw [dilation_bounds _ _ _ _ (Nat.pos_of_ne_zero ht), mem_box]
    dsimp [embed]
    norm_cast

def ehrhart (m n p : ℕ) : Polynomial ℚ :=
  (Polynomial.C (m : ℚ) * Polynomial.X + 1) * (Polynomial.C (n : ℚ) * Polynomial.X + 1) *
    (Polynomial.C (p : ℚ) * Polynomial.X + 1)
theorem actual_ehrhart (m n p t : ℕ) :
    (ehrhart m n p).eval (t : ℚ) = ((box (t*m) (t*n) (t*p)).card : ℚ) := by
  rw [actual_card]
  simp [ehrhart]
  ring

def A : Finset Z3 := box 1 8 12
def B : Finset Z3 := box 2 2 25
def countData (F : Finset Z3) : ℕ × (ℕ × ℕ) := (F.card, ((F.product F).card, (F+F).card))
theorem concrete_counts : A.card = 234 ∧ B.card = 234 ∧
    (A.product A).card = 54756 ∧ (B.product B).card = 54756 ∧
    (A+A).card = 1275 ∧ (B+B).card = 1275 := by
  simp [A,B,actual_sumset,actual_card,Finset.card_product]
theorem identical_count_data : countData A = countData B := by
  simp [countData, concrete_counts.1, concrete_counts.2.1,
    concrete_counts.2.2.1, concrete_counts.2.2.2.1,
    concrete_counts.2.2.2.2.1, concrete_counts.2.2.2.2.2]
theorem every_count_conversion {T : Type*} (conversion : (ℕ × (ℕ × ℕ)) → T) :
    conversion (countData A) = conversion (countData B) := by rw [identical_count_data]
theorem identical_normalized_doubling :
    ((A+A).card : ℚ) / A.card = ((B+B).card : ℚ) / B.card := by
  rw [concrete_counts.1, concrete_counts.2.1,
    concrete_counts.2.2.2.2.1, concrete_counts.2.2.2.2.2]

theorem polynomial_A : ehrhart 1 8 12 = 96*Polynomial.X^3 + 116*Polynomial.X^2 +
    21*Polynomial.X + 1 := by
  unfold ehrhart
  simp only [Polynomial.C_eq_natCast]
  norm_num
  ring
theorem polynomial_B : ehrhart 2 2 25 = 100*Polynomial.X^3 + 104*Polynomial.X^2 +
    29*Polynomial.X + 1 := by
  unfold ehrhart
  simp only [Polynomial.C_eq_natCast]
  norm_num
  ring
theorem different_polynomials : ehrhart 1 8 12 ≠ ehrhart 2 2 25 := by
  intro h
  have he := congrArg (fun P : Polynomial ℚ => P.eval 3) h
  norm_num [ehrhart] at he
theorem different_leading_coefficients :
    (ehrhart 1 8 12).coeff 3 = 96 ∧ (ehrhart 2 2 25).coeff 3 = 100 := by
  rw [polynomial_A, polynomial_B]
  norm_num [Polynomial.coeff_add, Polynomial.coeff_mul_X, Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_one]

theorem separation : countData A = countData B ∧ ehrhart 1 8 12 ≠ ehrhart 2 2 25 :=
  ⟨identical_count_data,different_polynomials⟩

#print axioms actual_card
#print axioms actual_compact
#print axioms actual_convex
#print axioms actual_sumset
#print axioms actual_lattice_points
#print axioms actual_ehrhart
#print axioms concrete_counts
#print axioms every_count_conversion
#print axioms identical_normalized_doubling
#print axioms different_leading_coefficients
#print axioms separation
end LatticeSeparation
