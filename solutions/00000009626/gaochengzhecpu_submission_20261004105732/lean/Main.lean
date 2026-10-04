import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-! A three-symbol, two-dimensional SFT whose spatial entropy is log 3. -/

namespace Conjecture9626

open Filter Topology

abbrev Alphabet := Fin 3
abbrev Configuration := (ℤ × ℤ) → Alphabet
abbrev Square (n : ℕ) := Fin n × Fin n
abbrev Pattern (n : ℕ) := Square n → Alphabet

def site {n : ℕ} (i : Square n) : ℤ × ℤ := (i.1.val, i.2.val)

theorem site_injective (n : ℕ) : Function.Injective (@site n) := by
  intro i j h
  have e₁ : (i.1.val : ℤ) = (j.1.val : ℤ) := congrArg Prod.fst h
  have e₂ : (i.2.val : ℤ) = (j.2.val : ℤ) := congrArg Prod.snd h
  have h₁ : i.1.val = j.1.val := by exact_mod_cast e₁
  have h₂ : i.2.val = j.2.val := by exact_mod_cast e₂
  exact Prod.ext (Fin.ext h₁) (Fin.ext h₂)

def fullShift : Set Configuration := Set.univ

/-- Avoid a finite list of forbidden square patterns at every lattice translate. -/
def sft (forbidden : Finset (Σ n : ℕ, Pattern n)) : Set Configuration :=
  {x | ∀ f ∈ forbidden, ∀ v : ℤ × ℤ,
    ∃ i : Square f.1, x (v + site i) ≠ f.2 i}

def IsSFT (X : Set Configuration) : Prop := ∃ F, X = sft F

theorem fullShift_isSFT : IsSFT fullShift := by
  refine ⟨∅, ?_⟩
  ext x
  simp [fullShift, sft]

def Occurs (X : Set Configuration) {n : ℕ} (p : Pattern n) : Prop :=
  ∃ x ∈ X, ∀ i, x (site i) = p i

theorem every_pattern_occurs (n : ℕ) (p : Pattern n) : Occurs fullShift p := by
  classical
  refine ⟨Function.extend site p (fun _ => 0), Set.mem_univ _, ?_⟩
  intro i
  exact (site_injective n).extend_apply p (fun _ => 0) i

noncomputable def fullPatternEquiv (n : ℕ) :
    {p : Pattern n // Occurs fullShift p} ≃ Pattern n where
  toFun := Subtype.val
  invFun p := ⟨p, every_pattern_occurs n p⟩
  left_inv p := by cases p; rfl
  right_inv _ := rfl

noncomputable def patternCount (X : Set Configuration) (n : ℕ) : ℕ :=
  Nat.card {p : Pattern n // Occurs X p}

theorem full_pattern_count (n : ℕ) : patternCount fullShift n = 3 ^ (n * n) := by
  rw [patternCount, Nat.card_congr (fullPatternEquiv n), Nat.card_eq_fintype_card]
  simp [Fintype.card_fun]

/-- The usual spatial-entropy sequence along nonempty square boxes. -/
noncomputable def normalizedLogCount (X : Set Configuration) (n : ℕ) : ℝ :=
  Real.log (patternCount X (n + 1)) / ((n + 1 : ℕ) : ℝ) ^ 2

def HasSpatialEntropy (X : Set Configuration) (h : ℝ) : Prop :=
  Tendsto (normalizedLogCount X) atTop (𝓝 h)

theorem full_normalized_log_count (n : ℕ) :
    normalizedLogCount fullShift n = Real.log 3 := by
  unfold normalizedLogCount
  rw [full_pattern_count, Nat.cast_pow, Real.log_pow]
  push_cast
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hn]
  ring

theorem fullShift_entropy : HasSpatialEntropy fullShift (Real.log 3) := by
  unfold HasSpatialEntropy
  have heq : normalizedLogCount fullShift = fun _ => Real.log 3 :=
    funext full_normalized_log_count
  rw [heq]
  exact tendsto_const_nhds

theorem entropy_above_claimed_bound : Real.log (2 : ℝ) < Real.log 3 := by
  exact Real.log_lt_log (by norm_num) (by norm_num)

/-- The claimed interval bound fails for an actual SFT and its actual entropy limit. -/
theorem counterexample :
    ∃ (X : Set Configuration) (h : ℝ),
      IsSFT X ∧ HasSpatialEntropy X h ∧ Real.log 2 < h :=
  ⟨fullShift, Real.log 3, fullShift_isSFT, fullShift_entropy,
    entropy_above_claimed_bound⟩

theorem not_universal_entropy_bound :
    ¬ (∀ (X : Set Configuration) (h : ℝ),
      IsSFT X → HasSpatialEntropy X h → h ≤ Real.log 2) := by
  intro h
  exact (not_le_of_gt entropy_above_claimed_bound)
    (h fullShift (Real.log 3) fullShift_isSFT fullShift_entropy)

#print axioms fullShift_isSFT
#print axioms every_pattern_occurs
#print axioms full_pattern_count
#print axioms fullShift_entropy
#print axioms counterexample
#print axioms not_universal_entropy_bound

end Conjecture9626
