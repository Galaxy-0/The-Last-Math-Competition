import Mathlib

/-!
# Conjecture 00000008197 is false

The conjecture (Weierstrass gap symmetry concentration formula) is a conjunction of five clauses about
`wgap(g)`, the distribution of Weierstrass gap sequences (equivalently, of the semigroups of
non-gaps `H(P)`, which are numerical semigroups of genus `g`). Two of the clauses are:

* (2) "the minimal genus of symmetry breaking of gaps (nonsymmetric semigroups) is `g = 3`";
* (4) "the realization density ... concentrates on symmetric semigroups, with concentration
  `1 - 2^{-g}`".

We refute clause (2) for numerical semigroups: `<3,4,5> = ℕ \ {1,2}` is a nonsymmetric numerical
semigroup of genus 2, and every numerical semigroup of genus `0` or `1` is symmetric, so the least
genus carrying a nonsymmetric numerical semigroup is `2`, not `3` (`least_nonsymmetric_genus`).

For the narrower reading in which only Weierstrass points proper are recorded (points whose
semigroup is not the ordinary one `ℕ \ {1, ..., g}`), we refute clause (4) at `g = 2`: every
non-ordinary numerical semigroup of genus 2 is `<2,5> = ℕ \ {1,3}`, which is symmetric, so every
probability distribution on them gives the symmetric semigroups mass `1 ≠ 1 - 2^{-2}`
(`no_distribution_with_concentration_formula`).

Definitions (Rosales--Garcia-Sanchez, *Numerical Semigroups*, Springer 2009, Ch. 1 and 3;
Wikipedia "Numerical semigroup"):
* a numerical semigroup is an additive submonoid of `ℕ` with finite complement;
* its gaps are `ℕ \ S`, its genus is the number of gaps, its Frobenius number the largest gap;
* `S` is symmetric if `S = ℕ` (Frobenius number `-1`) or `F - x ∈ S` for every gap `x`
  (Rosales--Garcia-Sanchez, Cor. 4.5); we also check the characterization `g = (F + 1) / 2`.
-/

namespace Conjecture8197

/-- A numerical semigroup: an additive submonoid of `ℕ` whose complement is finite. -/
structure NumericalSemigroup where
  carrier : AddSubmonoid ℕ
  finite_gaps : ((carrier : Set ℕ)ᶜ).Finite

namespace NumericalSemigroup

/-- The set of gaps `ℕ \ S`. -/
def gaps (S : NumericalSemigroup) : Set ℕ := ((S.carrier : Set ℕ))ᶜ

/-- The genus: the number of gaps. -/
noncomputable def genus (S : NumericalSemigroup) : ℕ := S.gaps.ncard

/-- `F` is the Frobenius number of `S`: the largest gap. -/
def IsFrobenius (S : NumericalSemigroup) (F : ℕ) : Prop := IsGreatest S.gaps F

/-- `S` is symmetric: either `S = ℕ` (no gaps, Frobenius number `-1`), or for the Frobenius number
`F`, every gap `x` (necessarily `x ≤ F`) has `F - x ∈ S`. -/
def IsSymmetric (S : NumericalSemigroup) : Prop :=
  S.gaps = ∅ ∨ ∃ F, S.IsFrobenius F ∧ ∀ x ∈ S.gaps, F - x ∈ S.carrier

/-- The ordinary semigroup of genus `g` is `{0} ∪ [g + 1, ∞)`, with gaps `{1, ..., g}`. A point of a
curve of genus `g` is a Weierstrass point exactly when its semigroup is not the ordinary one. -/
def IsOrdinary (S : NumericalSemigroup) : Prop := S.gaps = Set.Icc 1 S.genus

lemma mem_gaps {S : NumericalSemigroup} {n : ℕ} : n ∈ S.gaps ↔ n ∉ S.carrier := Iff.rfl

/-- If `1 ∈ S` then `S = ℕ`. -/
lemma gaps_eq_empty_of_one_mem {S : NumericalSemigroup} (h : 1 ∈ S.carrier) : S.gaps = ∅ := by
  ext n
  simp only [mem_gaps, Set.mem_empty_iff_false, iff_false, not_not]
  simpa using S.carrier.nsmul_mem h n

/-- In a semigroup of positive genus, `1` is a gap. -/
lemma one_mem_gaps {S : NumericalSemigroup} (h : S.genus ≠ 0) : 1 ∈ S.gaps := by
  intro h1
  apply h
  simp [genus, gaps_eq_empty_of_one_mem h1]

/-- If `2, 3 ∈ S` then every `n ≥ 2` lies in `S`. -/
lemma mem_of_two_three {S : NumericalSemigroup} (h2 : 2 ∈ S.carrier) (h3 : 3 ∈ S.carrier) :
    ∀ n, 2 ≤ n → n ∈ S.carrier := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases (show n = 2 ∨ n = 3 ∨ 4 ≤ n by omega) with rfl | rfl | h4
    · exact h2
    · exact h3
    · have := S.carrier.add_mem (ih (n - 2) (by omega) (by omega)) h2
      rwa [Nat.sub_add_cancel (by omega)] at this

/-- Classification of genus 2: the gap set is `{1, 2}` or `{1, 3}`. -/
theorem gaps_of_genus_two {S : NumericalSemigroup} (hg : S.genus = 2) :
    S.gaps = {1, 2} ∨ S.gaps = {1, 3} := by
  have h1 : 1 ∈ S.gaps := one_mem_gaps (by omega)
  have hfin : S.gaps.Finite := S.finite_gaps
  have key : 2 ∈ S.gaps ∨ 3 ∈ S.gaps := by
    by_contra hcon
    rw [not_or] at hcon
    have hsub : S.gaps ⊆ {1} := by
      intro n hn
      by_cases h0 : n = 0
      · exact absurd (h0 ▸ S.carrier.zero_mem) hn
      by_cases h1' : n = 1
      · simp [h1']
      · exact absurd (mem_of_two_three (not_not.mp hcon.1) (not_not.mp hcon.2) n (by omega)) hn
    have := Set.ncard_le_ncard hsub (Set.finite_singleton 1)
    simp [genus] at hg
    rw [hg, Set.ncard_singleton] at this
    omega
  rcases key with h2 | h3
  · left
    symm
    apply Set.eq_of_subset_of_ncard_le _ _ hfin
    · intro n hn
      rcases hn with rfl | rfl <;> assumption
    · rw [Set.ncard_pair (by norm_num)]
      exact hg.le
  · right
    symm
    apply Set.eq_of_subset_of_ncard_le _ _ hfin
    · intro n hn
      rcases hn with rfl | rfl <;> assumption
    · rw [Set.ncard_pair (by norm_num)]
      exact hg.le

/-- Genus `0` or `1` forces symmetry. -/
theorem isSymmetric_of_genus_lt_two {S : NumericalSemigroup} (hg : S.genus < 2) :
    S.IsSymmetric := by
  rcases (show S.genus = 0 ∨ S.genus = 1 by omega) with h0 | h1
  · left
    exact (Set.ncard_eq_zero S.finite_gaps).mp h0
  · right
    have hone : 1 ∈ S.gaps := one_mem_gaps (by omega)
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp h1
    have ha1 : S.gaps = {1} := by
      rw [ha] at hone ⊢
      rw [Set.mem_singleton_iff.mp hone]
    refine ⟨1, ⟨by simp [ha1], fun n hn => by rw [ha1] at hn; exact (Set.mem_singleton_iff.mp hn).le⟩, ?_⟩
    intro x hx
    rw [ha1, Set.mem_singleton_iff] at hx
    subst hx
    rw [Nat.sub_self]
    exact S.carrier.zero_mem

end NumericalSemigroup

open NumericalSemigroup

/-! ## The two witnesses -/

/-- `<3,4,5> = {0} ∪ [3, ∞)`, gaps `{1, 2}`. -/
def S345 : NumericalSemigroup where
  carrier :=
    { carrier := {n | n = 0 ∨ 3 ≤ n}
      zero_mem' := Or.inl rfl
      add_mem' := by
        intro a b (ha : a = 0 ∨ 3 ≤ a) (hb : b = 0 ∨ 3 ≤ b)
        show a + b = 0 ∨ 3 ≤ a + b
        omega }
  finite_gaps := by
    apply (Set.finite_Icc 1 2).subset
    intro n hn
    have hn' : ¬ (n = 0 ∨ 3 ≤ n) := hn
    simp only [Set.mem_Icc]
    omega

/-- `<2,5> = ℕ \ {1, 3}`. -/
def S25 : NumericalSemigroup where
  carrier :=
    { carrier := {n | n ≠ 1 ∧ n ≠ 3}
      zero_mem' := by simp
      add_mem' := by
        intro a b (ha : a ≠ 1 ∧ a ≠ 3) (hb : b ≠ 1 ∧ b ≠ 3)
        show a + b ≠ 1 ∧ a + b ≠ 3
        omega }
  finite_gaps := by
    apply (Set.finite_Icc 1 3).subset
    intro n hn
    have hn' : ¬ (n ≠ 1 ∧ n ≠ 3) := hn
    simp only [Set.mem_Icc]
    omega

lemma S345_gaps : S345.gaps = {1, 2} := by
  ext n
  simp only [gaps, S345, Set.mem_compl_iff, AddSubmonoid.coe_set_mk, AddSubsemigroup.coe_set_mk,
    Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

lemma S345_genus : S345.genus = 2 := by
  rw [genus, S345_gaps, Set.ncard_pair (by norm_num)]

lemma S345_frobenius : S345.IsFrobenius 2 := by
  rw [IsFrobenius, S345_gaps]
  refine ⟨by simp, fun n hn => ?_⟩
  rcases hn with rfl | rfl <;> norm_num

/-- `<3,4,5>` is not symmetric: the gap `1` has `F - 1 = 1` again a gap. -/
theorem S345_not_symmetric : ¬ S345.IsSymmetric := by
  rintro (h | ⟨F, hF, hsym⟩)
  · rw [S345_gaps] at h
    exact (Set.insert_nonempty 1 {2}).ne_empty h
  · have hF2 : F = 2 := le_antisymm (S345_frobenius.2 hF.1)
      (hF.2 (show (2 : ℕ) ∈ S345.gaps by rw [S345_gaps]; simp))
    subst hF2
    have h1 : (1 : ℕ) ∈ S345.gaps := by rw [S345_gaps]; simp
    exact (show (2 - 1 : ℕ) ∈ S345.gaps by rw [S345_gaps]; simp) (hsym 1 h1)

/-- The characterization `g = (F + 1) / 2` also fails for `<3,4,5>`: `2 g = 4 ≠ 3 = F + 1`. -/
theorem S345_genus_ne : 2 * S345.genus ≠ 2 + 1 := by
  rw [S345_genus]; norm_num

/-- `<3,4,5>` is the ordinary semigroup of genus 2 (gaps `{1, 2} = [1, 2]`): the semigroup of
non-gaps at every non-Weierstrass point of a genus-2 curve. -/
theorem S345_isOrdinary : S345.IsOrdinary := by
  rw [IsOrdinary, S345_gaps, S345_genus]
  ext n; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_Icc]; omega

lemma S25_gaps : S25.gaps = {1, 3} := by
  ext n
  simp only [gaps, S25, Set.mem_compl_iff, AddSubmonoid.coe_set_mk, AddSubsemigroup.coe_set_mk,
    Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

/-- Every numerical semigroup with gap set `{1, 3}` is symmetric (`F = 3`, `3 - 1 = 2 ∈ S`,
`3 - 3 = 0 ∈ S`). -/
theorem isSymmetric_of_gaps_eq_one_three {S : NumericalSemigroup} (h : S.gaps = {1, 3}) :
    S.IsSymmetric := by
  right
  refine ⟨3, ⟨by rw [h]; simp, fun n hn => ?_⟩, fun x hx => ?_⟩
  · rw [h] at hn; rcases hn with rfl | rfl <;> norm_num
  · rw [h] at hx
    by_contra hc
    have hc' : 3 - x ∈ S.gaps := hc
    rw [h] at hc'
    rcases hx with rfl | rfl <;> simp at hc'

/-! ## Clause (2): the least genus of a nonsymmetric numerical semigroup -/

/-- The set of genera carrying a nonsymmetric numerical semigroup. -/
def nonsymmetricGenera : Set ℕ := {g | ∃ S : NumericalSemigroup, S.genus = g ∧ ¬ S.IsSymmetric}

/-- Clause (2) of the conjecture, "the minimal genus of symmetry breaking (nonsymmetric
semigroups) is `g = 3`", for numerical semigroups. -/
def ThirdGenusBreaking : Prop := IsLeast nonsymmetricGenera 3

/-- The least genus of a nonsymmetric numerical semigroup is `2`. -/
theorem least_nonsymmetric_genus : IsLeast nonsymmetricGenera 2 :=
  ⟨⟨S345, S345_genus, S345_not_symmetric⟩, fun g ⟨S, hS, hns⟩ => by
    by_contra hlt
    exact hns (isSymmetric_of_genus_lt_two (by omega))⟩

theorem not_thirdGenusBreaking : ¬ ThirdGenusBreaking := fun h =>
  absurd (least_nonsymmetric_genus.unique h) (by norm_num)

/-! ## Clause (4) at `g = 2`, Weierstrass-point reading -/

/-- Non-ordinary numerical semigroups of genus `g`. Every semigroup occurring at a Weierstrass point
(proper) of a genus-`g` curve is non-ordinary, so this class *contains* all such semigroups; it is a
class of candidates, and geometric realizability of each member is not claimed. -/
def WeierstrassType (g : ℕ) : Type := {S : NumericalSemigroup // S.genus = g ∧ ¬ S.IsOrdinary}

/-- Every non-ordinary numerical semigroup of genus 2 is `<2,5>`, hence symmetric. -/
theorem isSymmetric_of_weierstrassType_two (S : WeierstrassType 2) : S.1.IsSymmetric := by
  obtain ⟨S, hg, hno⟩ := S
  rcases gaps_of_genus_two hg with h | h
  · exfalso
    apply hno
    rw [IsOrdinary, h, hg]
    ext n; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_Icc]; omega
  · exact isSymmetric_of_gaps_eq_one_three h

/-- `<2,5>` is a non-ordinary genus-2 semigroup, so `WeierstrassType 2` is nonempty. -/
def S25_weierstrass : WeierstrassType 2 :=
  ⟨S25, by rw [genus, S25_gaps, Set.ncard_pair (by norm_num)], fun h => by
    have h' := h
    rw [IsOrdinary, S25_gaps] at h'
    have : (2 : ℕ) ∈ ({1, 3} : Set ℕ) := by
      rw [h']
      simp only [Set.mem_Icc]
      constructor
      · norm_num
      · rw [genus, S25_gaps, Set.ncard_pair (by norm_num)]
    simp at this⟩

/-- Clause (4) at genus `g` (Weierstrass-point reading): some probability distribution on the
semigroups at Weierstrass points of genus-`g` curves gives the symmetric ones mass `1 - 2^{-g}`. -/
def ConcentrationFormula (g : ℕ) : Prop :=
  ∃ μ : PMF (WeierstrassType g), μ.toOuterMeasure {S | S.1.IsSymmetric} = 1 - (2⁻¹ : ENNReal) ^ g

/-- Every distribution on genus-2 Weierstrass semigroups puts mass `1` on symmetric ones. -/
theorem symmetric_mass_eq_one (μ : PMF (WeierstrassType 2)) :
    μ.toOuterMeasure {S | S.1.IsSymmetric} = 1 := by
  rw [PMF.toOuterMeasure_apply_eq_one_iff]
  intro S _
  exact isSymmetric_of_weierstrassType_two S

theorem no_distribution_with_concentration_formula : ¬ ConcentrationFormula 2 := by
  rintro ⟨μ, hμ⟩
  rw [symmetric_mass_eq_one μ] at hμ
  have hpos : (2⁻¹ : ENNReal) ^ 2 ≠ 0 := pow_ne_zero _ (ENNReal.inv_ne_zero.mpr ENNReal.ofNat_ne_top)
  have := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hpos
  rw [← hμ] at this
  exact lt_irrefl _ this

/-! ## Main theorem -/

/-- **Conjecture 00000008197 is false.** For every formalization `P` of the remaining clauses, the
conjunction of the third-genus-breaking clause with `P` fails; and under the Weierstrass-point
reading the concentration formula fails at `g = 2`. Concretely: `<3,4,5>` is a nonsymmetric
numerical semigroup of genus 2 and the least such genus is 2; and every distribution on the
semigroups at Weierstrass points of genus-2 curves is concentrated on the symmetric `<2,5>`. -/
theorem conjecture_00000008197_false (P Q : Prop) :
    ¬ (ThirdGenusBreaking ∧ P) ∧ ¬ (ConcentrationFormula 2 ∧ Q) ∧
    (S345.genus = 2 ∧ ¬ S345.IsSymmetric) ∧ IsLeast nonsymmetricGenera 2 ∧
    Nonempty (WeierstrassType 2) ∧
    (∀ μ : PMF (WeierstrassType 2), μ.toOuterMeasure {S | S.1.IsSymmetric} = 1) :=
  ⟨fun h => not_thirdGenusBreaking h.1, fun h => no_distribution_with_concentration_formula h.1,
    ⟨S345_genus, S345_not_symmetric⟩, least_nonsymmetric_genus, ⟨S25_weierstrass⟩,
    symmetric_mass_eq_one⟩

end Conjecture8197
