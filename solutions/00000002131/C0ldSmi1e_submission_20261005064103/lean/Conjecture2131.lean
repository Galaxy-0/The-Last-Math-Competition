import Mathlib.Data.Fin.Rev
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# A counterexample to Stanley-Wilf direct-sum multiplicativity

Patterns and tested objects are genuine finite permutations. Containment selects
arbitrary strictly increasing positions and preserves all strict value comparisons.
The count is the cardinality of the full subtype of avoiding permutations.
-/

namespace Conjecture2131

open Filter

abbrev Permutation (n : ℕ) := Equiv.Perm (Fin n)

/-- Classical (not necessarily consecutive) permutation-pattern containment. -/
def Contains {k n : ℕ} (p : Permutation k) (s : Permutation n) : Prop :=
  ∃ e : Fin k → Fin n, StrictMono e ∧
    ∀ i j, s (e i) < s (e j) ↔ p i < p j

/-- Avoidance is precisely the negation of classical containment. -/
def Avoids {k n : ℕ} (p : Permutation k) (s : Permutation n) : Prop :=
  ¬ Contains p s

/-- Exact number of all size-`n` permutations avoiding `p`. -/
noncomputable def avoidanceCount {k : ℕ} (p : Permutation k) (n : ℕ) : ℕ := by
  classical
  exact Fintype.card {s : Permutation n // Avoids p s}

/-- Transport the blockwise bijection through the ordered index decomposition. -/
def directSum {k l : ℕ} (p : Permutation k) (q : Permutation l) :
    Permutation (k + l) :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr p q).trans finSumFinEquiv)

theorem directSum_left {k l : ℕ} (p : Permutation k) (q : Permutation l)
    (i : Fin k) : directSum p q (Fin.castAdd l i) = Fin.castAdd l (p i) := by
  simp [directSum]

theorem directSum_right {k l : ℕ} (p : Permutation k) (q : Permutation l)
    (j : Fin l) : directSum p q (Fin.natAdd k j) = Fin.natAdd k (q j) := by
  simp [directSum]

theorem directSum_left_value {k l : ℕ} (p : Permutation k) (q : Permutation l)
    (i : Fin k) : (directSum p q (Fin.castAdd l i)).val = (p i).val := by
  rw [directSum_left]
  rfl

theorem directSum_right_value {k l : ℕ} (p : Permutation k) (q : Permutation l)
    (j : Fin l) : (directSum p q (Fin.natAdd k j)).val = k + (q j).val := by
  rw [directSum_right]
  rfl

theorem directSum_block_positions {k l : ℕ} (i : Fin k) (j : Fin l) :
    Fin.castAdd l i < Fin.natAdd k j := by
  change i.val < k + j.val
  omega

theorem directSum_block_values {k l : ℕ} (p : Permutation k) (q : Permutation l)
    (i : Fin k) (j : Fin l) :
    directSum p q (Fin.castAdd l i) < directSum p q (Fin.natAdd k j) := by
  rw [directSum_left, directSum_right]
  exact directSum_block_positions (p i) (q j)

/-- Increasing permutation, including the one-point pattern. -/
def increasing (k : ℕ) : Permutation k := Equiv.refl _

/-- Decreasing permutation, including the unique empty permutation at size zero. -/
def decreasing (n : ℕ) : Permutation n := Fin.revPerm

theorem increasing_sum_increasing (k l : ℕ) :
    directSum (increasing k) (increasing l) = increasing (k + l) := by
  ext i
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  cases i <;> simp [directSum, increasing]

theorem contains_one (n : ℕ) (s : Permutation (n + 1)) :
    Contains (increasing 1) s := by
  refine ⟨fun _ => 0, ?_, ?_⟩
  · intro i j hij
    exact False.elim ((not_lt_of_ge (Subsingleton.elim i j).ge) hij)
  · intro i j
    have hij : i = j := Subsingleton.elim i j
    subst j
    simp

theorem avoidanceCount_one (n : ℕ) : avoidanceCount (increasing 1) (n + 1) = 0 := by
  classical
  apply Fintype.card_eq_zero_iff.mpr
  exact ⟨fun s => s.property (contains_one n s.val)⟩

theorem contains_two_iff {n : ℕ} (s : Permutation n) :
    Contains (increasing 2) s ↔ ∃ i j : Fin n, i < j ∧ s i < s j := by
  constructor
  · rintro ⟨e, he, hv⟩
    exact ⟨e 0, e 1, he (by decide), (hv 0 1).mpr (by decide)⟩
  · rintro ⟨i, j, hij, hs⟩
    refine ⟨![i, j], ?_, ?_⟩
    · rw [Fin.strictMono_iff_lt_succ]
      intro a
      fin_cases a
      exact hij
    · intro a b
      fin_cases a <;> fin_cases b <;> simp [increasing, hs, not_lt_of_gt hs]

theorem avoids_two_iff_strictAnti {n : ℕ} (s : Permutation n) :
    Avoids (increasing 2) s ↔ StrictAnti s := by
  rw [Avoids, contains_two_iff]
  constructor
  · intro h i j hij
    have hne : s i ≠ s j := s.injective.ne hij.ne
    exact lt_of_le_of_ne (not_lt.mp (fun hlt => h ⟨i, j, hij, hlt⟩)) hne.symm
  · intro h hpair
    obtain ⟨i, j, hij, hs⟩ := hpair
    exact (not_lt_of_gt (h hij)) hs

theorem decreasing_strictAnti (n : ℕ) : StrictAnti (decreasing n) := by
  intro i j hij
  exact Fin.rev_lt_rev.mpr hij

theorem avoids_two_iff_decreasing {n : ℕ} (s : Permutation n) :
    Avoids (increasing 2) s ↔ s = decreasing n := by
  rw [avoids_two_iff_strictAnti]
  constructor
  · intro hs
    apply Equiv.ext
    have hfun := (hs.range_inj (decreasing_strictAnti n)).mp
      (by rw [s.surjective.range_eq, (decreasing n).surjective.range_eq])
    exact congrFun hfun
  · rintro rfl
    exact decreasing_strictAnti n

theorem avoidanceCount_two (n : ℕ) : avoidanceCount (increasing 2) n = 1 := by
  classical
  apply Fintype.card_eq_one_iff.mpr
  refine ⟨⟨decreasing n, (avoids_two_iff_decreasing _).mpr rfl⟩, ?_⟩
  intro s
  exact Subtype.ext ((avoids_two_iff_decreasing s.val).mp s.property)

/-- The genuine real nth root; index zero is irrelevant to limits at infinity. -/
noncomputable def rootCount {k : ℕ} (p : Permutation k) (n : ℕ) : ℝ :=
  (avoidanceCount p n : ℝ) ^ (1 / (n : ℝ))

/-- A positive-index root sequence, using the explicit bijective shift `n ↦ n+1`. -/
noncomputable def rootSequence {k : ℕ} (p : Permutation k) (n : ℕ) : ℝ :=
  rootCount p (n + 1)

/-- Genuine Stanley-Wilf convergence, without assuming any numerical limit value. -/
def SW {k : ℕ} (p : Permutation k) (x : ℝ) : Prop :=
  Tendsto (rootSequence p) atTop (nhds x)

/-- At zero the totalized auxiliary sequence is 1; this index is never used by `SW`. -/
theorem rootCount_zero {k : ℕ} (p : Permutation k) : rootCount p 0 = 1 := by
  simp [rootCount]

/-- Every positive source index is represented by the shifted sequence. -/
theorem rootSequence_at_positive_index {k n : ℕ} (p : Permutation k) (hn : 0 < n) :
    rootSequence p (n - 1) = rootCount p n := by
  unfold rootSequence
  congr 1
  omega

/-- Dropping the single artificial index zero preserves the genuine real limit. -/
theorem sw_iff_unshifted {k : ℕ} (p : Permutation k) (x : ℝ) :
    SW p x ↔ Tendsto (rootCount p) atTop (nhds x) := by
  exact tendsto_add_atTop_iff_nat 1

theorem sw_unique {k : ℕ} {p : Permutation k} {x y : ℝ}
    (hx : SW p x) (hy : SW p y) : x = y :=
  tendsto_nhds_unique hx hy

theorem rootSequence_one (n : ℕ) : rootSequence (increasing 1) n = 0 := by
  simp only [rootSequence, rootCount, avoidanceCount_one, Nat.cast_zero]
  apply Real.zero_rpow
  positivity

theorem rootSequence_two (n : ℕ) : rootSequence (increasing 2) n = 1 := by
  simp [rootSequence, rootCount, avoidanceCount_two]

theorem sw_one : SW (increasing 1) 0 := by
  unfold SW
  rw [show rootSequence (increasing 1) = fun _ => 0 from funext rootSequence_one]
  exact
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))

theorem sw_two : SW (increasing 2) 1 := by
  unfold SW
  rw [show rootSequence (increasing 2) = fun _ => 1 from funext rootSequence_two]
  exact
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1))

theorem sw_one_directSum_one :
    SW (directSum (increasing 1) (increasing 1)) 1 := by
  rw [increasing_sum_increasing]
  exact sw_two

/-- The three actual growth limits exist and explicitly violate the equality. -/
theorem nonmultiplicative_witness :
    SW (increasing 1) 0 ∧ SW (increasing 1) 0 ∧
    SW (directSum (increasing 1) (increasing 1)) 1 ∧
    (1 : ℝ) ≠ 0 * 0 := by
  exact ⟨sw_one, sw_one, sw_one_directSum_one, by norm_num⟩

/-- Exactly the displayed universal equality, with the real limits made explicit. -/
def UniversalMultiplicativity : Prop :=
  ∀ k l : ℕ, 0 < k → 0 < l → ∀ (p : Permutation k) (q : Permutation l),
    ∃ x y z : ℝ, SW p x ∧ SW q y ∧ SW (directSum p q) z ∧ z = x * y

theorem not_universalMultiplicativity : ¬ UniversalMultiplicativity := by
  intro h
  obtain ⟨x, y, z, hx, hy, hz, heq⟩ :=
    h 1 1 (by decide) (by decide) (increasing 1) (increasing 1)
  have hx0 : x = 0 := sw_unique hx sw_one
  have hy0 : y = 0 := sw_unique hy sw_one
  have hz1 : z = 1 := by
    rw [increasing_sum_increasing] at hz
    exact sw_unique hz sw_two
  norm_num [hx0, hy0, hz1] at heq

/-- The displayed equality in function notation, for a real-valued limit assignment. -/
def NumericalMultiplicativity (L : ∀ k : ℕ, Permutation k → ℝ) : Prop :=
  ∀ k l : ℕ, 0 < k → 0 < l → ∀ (p : Permutation k) (q : Permutation l),
    L (k + l) (directSum p q) = L k p * L l q

/-- Function notation agrees with the relational formulation when its values are
verified genuine limits on every permitted nonempty pattern. No existence of
such a global assignment is assumed by the counterexample. -/
theorem universal_iff_numerical_of_verified_limits
    (L : ∀ k : ℕ, Permutation k → ℝ)
    (hL : ∀ k : ℕ, 0 < k → ∀ p : Permutation k, SW p (L k p)) :
    UniversalMultiplicativity ↔ NumericalMultiplicativity L := by
  constructor
  · intro h k l hk hl p q
    obtain ⟨x, y, z, hx, hy, hz, heq⟩ := h k l hk hl p q
    have hxL := sw_unique hx (hL k hk p)
    have hyL := sw_unique hy (hL l hl q)
    have hzL := sw_unique hz (hL (k + l) (by omega) (directSum p q))
    simpa only [hxL, hyL, hzL] using heq
  · intro h k l hk hl p q
    exact ⟨L k p, L l q, L (k + l) (directSum p q),
      hL k hk p, hL l hl q, hL (k + l) (by omega) (directSum p q), h k l hk hl p q⟩

theorem not_numericalMultiplicativity_of_verified_limits
    (L : ∀ k : ℕ, Permutation k → ℝ)
    (hL : ∀ k : ℕ, 0 < k → ∀ p : Permutation k, SW p (L k p)) :
    ¬ NumericalMultiplicativity L := by
  intro h
  exact not_universalMultiplicativity
    ((universal_iff_numerical_of_verified_limits L hL).mpr h)

/-- Any additional characterization clause cannot rescue a conjunction containing
an already false displayed universal equality. Its content is not invented here. -/
theorem not_source_conjunction (Extension : Prop) :
    ¬ (UniversalMultiplicativity ∧ Extension) := by
  intro h
  exact not_universalMultiplicativity h.1

end Conjecture2131
