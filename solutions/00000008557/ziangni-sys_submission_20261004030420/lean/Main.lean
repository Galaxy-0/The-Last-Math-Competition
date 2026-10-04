import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace CongruenceAtoms
abbrev Chain := Fin 3
abbrev Relation := Chain → Chain → Bool
example : Lattice Chain := inferInstance

def IsCongruence (r : Relation) : Prop :=
  (∀ x, r x x = true) ∧
  (∀ x y, r x y = true → r y x = true) ∧
  (∀ x y z, r x y = true → r y z = true → r x z = true) ∧
  (∀ x x' y y', r x x' = true → r y y' = true →
    r (min x y) (min x' y') = true) ∧
  (∀ x x' y y', r x x' = true → r y y' = true →
    r (max x y) (max x' y') = true)
instance (r : Relation) : Decidable (IsCongruence r) := by unfold IsCongruence; infer_instance

def bottom : Relation := fun x y => decide (x = y)
def alpha : Relation := fun x y => decide ((x.val ≤ 1 ∧ y.val ≤ 1) ∨ x = y)
def beta : Relation := fun x y => decide ((1 ≤ x.val ∧ 1 ≤ y.val) ∨ x = y)
def top : Relation := fun _ _ => true

theorem congruences_classified : ∀ r : Relation, IsCongruence r →
    r = bottom ∨ r = alpha ∨ r = beta ∨ r = top := by decide
theorem bottom_congruence : IsCongruence bottom := by decide
theorem alpha_congruence : IsCongruence alpha := by decide
theorem beta_congruence : IsCongruence beta := by decide
theorem top_congruence : IsCongruence top := by decide

def Below (r s : Relation) : Prop := ∀ x y, r x y = true → s x y = true
instance (r s : Relation) : Decidable (Below r s) := by unfold Below; infer_instance

theorem bottom_below (r : Relation) (h : IsCongruence r) : Below bottom r := by
  intro x y he
  have hxy : x = y := of_decide_eq_true he
  subst y; exact h.1 x

-- Minimal non-bottom element of the actual congruence inclusion order.
def IsAtom (r : Relation) : Prop := IsCongruence r ∧ r ≠ bottom ∧
  ∀ s, IsCongruence s → Below s r → s = bottom ∨ s = r

theorem alpha_ne_bottom : alpha ≠ bottom := by decide
theorem beta_ne_bottom : beta ≠ bottom := by decide
theorem alpha_ne_beta : alpha ≠ beta := by decide

theorem alpha_atom : IsAtom alpha := by
  refine ⟨alpha_congruence,alpha_ne_bottom,?_⟩
  intro s hs hle
  rcases congruences_classified s hs with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact False.elim ((by decide : ¬ Below beta alpha) hle)
  · exact False.elim ((by decide : ¬ Below top alpha) hle)

theorem beta_atom : IsAtom beta := by
  refine ⟨beta_congruence,beta_ne_bottom,?_⟩
  intro s hs hle
  rcases congruences_classified s hs with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact False.elim ((by decide : ¬ Below alpha beta) hle)
  · exact Or.inr rfl
  · exact False.elim ((by decide : ¬ Below top beta) hle)

theorem top_not_atom : ¬ IsAtom top := by
  intro h
  have ha := h.2.2 alpha alpha_congruence (by decide)
  rcases ha with ha | ha
  · exact alpha_ne_bottom ha
  · exact (by decide : alpha ≠ top) ha

theorem atoms_classified (r : Relation) : IsAtom r ↔ r = alpha ∨ r = beta := by
  constructor
  · intro h
    rcases congruences_classified r h.1 with hb | ha | hbe | ht
    · exact False.elim (h.2.1 hb)
    · exact Or.inl ha
    · exact Or.inr hbe
    · subst r; exact False.elim (top_not_atom h)
  · rintro (rfl | rfl)
    · exact alpha_atom
    · exact beta_atom

noncomputable def atoms : Finset Relation := by
  classical
  exact Finset.univ.filter IsAtom

theorem actual_atom_count : atoms.card = 2 := by
  classical
  have he : atoms = {alpha,beta} := by
    ext r
    simp [atoms, atoms_classified]
  rw [he]
  simp [alpha_ne_beta]

noncomputable def logTwo (x : ℝ) : ℝ := Real.log x / Real.log 2

theorem logTwo_three_lt_two : logTwo 3 < 2 := by
  have hp : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlt : Real.log 3 < Real.log ((2 : ℝ)^2) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  rw [Real.log_pow] at hlt
  apply (div_lt_iff₀ hp).2
  simpa using hlt

theorem conjecture_00000008557_false :
    ¬ ((atoms.card : ℝ) ≤ logTwo (Fintype.card Chain)) := by
  rw [actual_atom_count]
  norm_num only [Fintype.card_fin, Nat.cast_ofNat]
  exact not_le_of_gt logTwo_three_lt_two

#print axioms congruences_classified
#print axioms actual_atom_count
#print axioms conjecture_00000008557_false
end CongruenceAtoms
