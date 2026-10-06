import Mathlib

/-!
# Conjecture 00000006630: same correlation inequalities, different equilibria

Conjecture 00000006630 reads:

> Definition: Correlation inequalities and equilibria are two layers. Conjecture: There exist two
> lattice-gas models with identical inequalities but different equilibria, and the separation is
> realized by an explicit violation with the same inequalities but different configuration
> counting.

Reading. A (hard-core) lattice-gas model on a finite site set `V` is an exclusion graph `G` on `V`
together with an activity `λ > 0`. Its configurations are the sets `η ⊆ V` of occupied sites; `η`
is allowed iff no two occupied sites are adjacent. The *equilibrium* is the Gibbs (grand-canonical)
state `μ(η) = λ^|η| / Z` on allowed configurations, where the *configuration count* (partition
function) is `Z = ∑_{η allowed} λ^|η|`. For a set of sites `B` let `n_B(η) = [B ⊆ η]` be the
occupation monomial. The *correlation inequalities* of the model are recorded by its profile

  `profile(B, C) = sign(⟨n_B n_C⟩ - ⟨n_B⟩⟨n_C⟩)`   for all `B, C ⊆ V`,

which says, for every pair of occupation monomials, which of `≥`, `=`, `≤` holds (FKG / Harris /
Griffiths-type correlation inequalities).

Main result (`conjecture6630`). On two adjacent sites (`V = Fin 2`, `G = ⊤`), the models with
activities `λ = 1` and `λ = 2`:

* have identical profiles — in fact every positive activity gives the same profile
  (`profile_K2_eq`);
* have different equilibria: `μ({0}) = 1/3` versus `2/5`;
* both exhibit the same explicit violation of the positive-correlation (FKG/Harris) inequality,
  `⟨n_0 n_1⟩ < ⟨n_0⟩⟨n_1⟩`;
* have different configuration counts `Z = 3` and `Z = 5`. For an integer activity `q`, `Z` is the
  number of configurations when each particle carries one of `q` internal states; for `q = 1, 2`
  this literal count is proved by `card_internal_one` and `card_internal_two`, and the equilibrium
  is the occupation marginal of the uniform distribution on these configurations
  (`gibbs_eq_count_one`, `gibbs_eq_count_two`).
-/

namespace Submission00000006630

open Finset

/-- A hard-core lattice-gas model on the sites `V`: exclusion graph and positive activity. -/
structure LatticeGas (V : Type) [Fintype V] [DecidableEq V] where
  G : SimpleGraph V
  [decAdj : DecidableRel G.Adj]
  act : ℝ
  act_pos : 0 < act

attribute [instance] LatticeGas.decAdj

variable {V : Type} [Fintype V] [DecidableEq V]

/-- A configuration (set of occupied sites) is allowed iff no two occupied sites are adjacent. -/
def Allowed (M : LatticeGas V) (η : Finset V) : Prop := ∀ x ∈ η, ∀ y ∈ η, ¬ M.G.Adj x y

instance (M : LatticeGas V) : DecidablePred (Allowed M) := by
  intro η; unfold Allowed; infer_instance

/-- Boltzmann weight `λ^|η|` of an allowed configuration, `0` otherwise. -/
noncomputable def weight (M : LatticeGas V) (η : Finset V) : ℝ :=
  if Allowed M η then M.act ^ η.card else 0

/-- The configuration count (partition function) `Z = ∑_η weight η`. -/
noncomputable def Z (M : LatticeGas V) : ℝ := ∑ η : Finset V, weight M η

/-- The equilibrium (Gibbs) state. -/
noncomputable def gibbs (M : LatticeGas V) (η : Finset V) : ℝ := weight M η / Z M

/-- Expectation in the equilibrium state. -/
noncomputable def expect (M : LatticeGas V) (f : Finset V → ℝ) : ℝ :=
  ∑ η : Finset V, f η * gibbs M η

/-- Occupation monomial `n_B(η) = [B ⊆ η]`. -/
def occ (B : Finset V) (η : Finset V) : ℝ := if B ⊆ η then 1 else 0

/-- Truncated correlation `⟨n_B n_C⟩ - ⟨n_B⟩⟨n_C⟩`. -/
noncomputable def cov (M : LatticeGas V) (B C : Finset V) : ℝ :=
  expect M (fun η => occ B η * occ C η) - expect M (occ B) * expect M (occ C)

/-- The correlation-inequality profile: which of `>`, `=`, `<` holds for every pair. -/
noncomputable def profile (M : LatticeGas V) (B C : Finset V) : SignType :=
  SignType.sign (cov M B C)

/-- Unnormalized moment `W(B) = ∑_η n_B(η) weight(η)`. -/
noncomputable def W (M : LatticeGas V) (B : Finset V) : ℝ := ∑ η : Finset V, occ B η * weight M η

omit [Fintype V] in
lemma occ_mul (B C η : Finset V) : occ B η * occ C η = occ (B ∪ C) η := by
  unfold occ
  by_cases hB : B ⊆ η <;> by_cases hC : C ⊆ η <;> simp [hB, hC, Finset.union_subset_iff]

lemma weight_nonneg (M : LatticeGas V) (η : Finset V) : 0 ≤ weight M η := by
  unfold weight
  split_ifs
  · exact pow_nonneg M.act_pos.le _
  · exact le_refl 0

lemma Z_pos (M : LatticeGas V) : 0 < Z M := by
  have h0 : weight M ∅ = 1 := by simp [weight, Allowed]
  have : weight M ∅ ≤ Z M :=
    Finset.single_le_sum (fun η _ => weight_nonneg M η) (Finset.mem_univ _)
  linarith

lemma expect_occ (M : LatticeGas V) (B : Finset V) : expect M (occ B) = W M B / Z M := by
  simp only [expect, gibbs, W, Finset.sum_div, mul_div_assoc]

/-- The profile is the sign of `Z·W(B ∪ C) - W(B)·W(C)`. -/
lemma profile_eq (M : LatticeGas V) (B C : Finset V) :
    profile M B C = SignType.sign (Z M * W M (B ∪ C) - W M B * W M C) := by
  have hZ := Z_pos M
  have hc : cov M B C = (Z M * W M (B ∪ C) - W M B * W M C) / (Z M) ^ 2 := by
    have : expect M (fun η => occ B η * occ C η) = W M (B ∪ C) / Z M := by
      simp only [occ_mul]; exact expect_occ M (B ∪ C)
    rw [cov, this, expect_occ, expect_occ]
    field_simp
  rw [profile, hc, div_eq_mul_inv, sign_mul, sign_pos (inv_pos.mpr (pow_pos hZ 2)), mul_one]

/-! ## Two adjacent sites -/

/-- The hard-core gas on two adjacent sites with activity `λ`. -/
noncomputable def K2 (l : ℝ) (hl : 0 < l) : LatticeGas (Fin 2) where
  G := ⊤
  act := l
  act_pos := hl

lemma univ_fin2 : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide

lemma weight_K2 (l : ℝ) (hl : 0 < l) :
    weight (K2 l hl) ∅ = 1 ∧ weight (K2 l hl) {0} = l ∧ weight (K2 l hl) {1} = l ∧
      weight (K2 l hl) {0, 1} = 0 := by
  refine ⟨by simp [weight, Allowed], by simp [weight, Allowed, K2], by simp [weight, Allowed, K2],
    ?_⟩
  have : ¬ Allowed (K2 l hl) {0, 1} := by
    intro h
    exact h 0 (by simp) 1 (by simp) (by simp [K2])
  simp [weight, this]

lemma sum_fin2 (f : Finset (Fin 2) → ℝ) :
    ∑ η : Finset (Fin 2), f η = f ∅ + f {0} + f {1} + f {0, 1} := by
  rw [univ_fin2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

lemma Z_K2 (l : ℝ) (hl : 0 < l) : Z (K2 l hl) = 1 + 2 * l := by
  obtain ⟨h0, h1, h2, h3⟩ := weight_K2 l hl
  rw [Z, sum_fin2, h0, h1, h2, h3]; ring

lemma W_K2 (l : ℝ) (hl : 0 < l) (B : Finset (Fin 2)) :
    W (K2 l hl) B = occ B ∅ + occ B {0} * l + occ B {1} * l := by
  obtain ⟨h0, h1, h2, h3⟩ := weight_K2 l hl
  rw [W, sum_fin2, h0, h1, h2, h3]; ring

/-- The profile of the two-site gas, which does not depend on the activity. -/
def table (B C : Finset (Fin 2)) : SignType :=
  if B = ∅ ∨ C = ∅ ∨ B = {0, 1} ∨ C = {0, 1} then 0 else if B = C then 1 else -1

lemma profile_K2 (l : ℝ) (hl : 0 < l) (B C : Finset (Fin 2)) :
    profile (K2 l hl) B C = table B C := by
  have hB : B ∈ (Finset.univ : Finset (Finset (Fin 2))) := Finset.mem_univ B
  have hC : C ∈ (Finset.univ : Finset (Finset (Fin 2))) := Finset.mem_univ C
  rw [univ_fin2] at hB hC
  simp only [Finset.mem_insert, Finset.mem_singleton] at hB hC
  rw [profile_eq, Z_K2, W_K2, W_K2, W_K2]
  rcases hB with rfl | rfl | rfl | rfl <;> rcases hC with rfl | rfl | rfl | rfl <;>
    simp (config := { decide := true }) [occ, table] <;>
    first
    | ring1
    | (rw [sign_pos]; nlinarith)
    | (rw [sign_neg]; nlinarith)

/-- Every positive activity gives the same correlation-inequality profile. -/
theorem profile_K2_eq (l m : ℝ) (hl : 0 < l) (hm : 0 < m) :
    profile (K2 l hl) = profile (K2 m hm) := by
  funext B C
  rw [profile_K2, profile_K2]

/-- The explicit violation of the positive-correlation (FKG/Harris) inequality at the adjacent
pair: `⟨n_0 n_1⟩ < ⟨n_0⟩⟨n_1⟩`, for every positive activity. -/
theorem violation_K2 (l : ℝ) (hl : 0 < l) :
    expect (K2 l hl) (fun η => occ {0} η * occ {1} η) <
      expect (K2 l hl) (occ {0}) * expect (K2 l hl) (occ {1}) := by
  have h := profile_K2 l hl {0} {1}
  simp (config := { decide := true }) only [table] at h
  rw [profile] at h
  have : cov (K2 l hl) {0} {1} < 0 := by
    rcases lt_trichotomy (cov (K2 l hl) {0} {1}) 0 with h' | h' | h'
    · exact h'
    · rw [h'] at h; simp at h
    · rw [sign_pos h'] at h; simp at h
  unfold cov at this
  linarith

lemma gibbs_K2_zero (l : ℝ) (hl : 0 < l) : gibbs (K2 l hl) {0} = l / (1 + 2 * l) := by
  rw [gibbs, Z_K2, (weight_K2 l hl).2.1]

/-! ## Literal configuration counts with internal particle states -/

/-- Configurations of the two-site gas whose particles carry one of `q` internal states: each site
is empty (`none`) or holds a particle in state `s`, and the two sites are not both occupied. -/
def InternalConfig (q : ℕ) := {ω : Fin 2 → Option (Fin q) // ω 0 = none ∨ ω 1 = none}

instance (q : ℕ) : Fintype (InternalConfig q) := by unfold InternalConfig; infer_instance

lemma card_internal_one : Fintype.card (InternalConfig 1) = 3 := by
  unfold InternalConfig; decide

lemma card_internal_two : Fintype.card (InternalConfig 2) = 5 := by
  unfold InternalConfig; decide

/-- The set of occupied sites of an internal-state configuration. -/
def occSet {q : ℕ} (ω : InternalConfig q) : Finset (Fin 2) :=
  Finset.univ.filter (fun x => ω.1 x ≠ none)

/-- Number of internal-state configurations with occupied set `η`. -/
def countOcc (q : ℕ) (η : Finset (Fin 2)) : ℕ :=
  (Finset.univ.filter (fun ω : InternalConfig q => occSet ω = η)).card

lemma countOcc_one :
    countOcc 1 ∅ = 1 ∧ countOcc 1 {0} = 1 ∧ countOcc 1 {1} = 1 ∧ countOcc 1 {0, 1} = 0 := by
  unfold countOcc occSet InternalConfig; decide

lemma countOcc_two :
    countOcc 2 ∅ = 1 ∧ countOcc 2 {0} = 2 ∧ countOcc 2 {1} = 2 ∧ countOcc 2 {0, 1} = 0 := by
  unfold countOcc occSet InternalConfig; decide

/-- The equilibrium of the activity-`q` model is the occupation marginal of the uniform
distribution on the `q`-internal-state configurations (`q = 1`). -/
theorem gibbs_eq_count_one (η : Finset (Fin 2)) :
    gibbs (K2 1 one_pos) η = (countOcc 1 η : ℝ) / Fintype.card (InternalConfig 1) := by
  have hη : η ∈ (Finset.univ : Finset (Finset (Fin 2))) := Finset.mem_univ η
  rw [univ_fin2] at hη
  simp only [Finset.mem_insert, Finset.mem_singleton] at hη
  obtain ⟨c0, c1, c2, c3⟩ := countOcc_one
  obtain ⟨w0, w1, w2, w3⟩ := weight_K2 1 one_pos
  rw [gibbs, Z_K2, card_internal_one]
  rcases hη with rfl | rfl | rfl | rfl
  · rw [w0, c0]; norm_num
  · rw [w1, c1]; norm_num
  · rw [w2, c2]; norm_num
  · rw [w3, c3]; norm_num

/-- Same statement for `q = 2`. -/
theorem gibbs_eq_count_two (η : Finset (Fin 2)) :
    gibbs (K2 2 two_pos) η = (countOcc 2 η : ℝ) / Fintype.card (InternalConfig 2) := by
  have hη : η ∈ (Finset.univ : Finset (Finset (Fin 2))) := Finset.mem_univ η
  rw [univ_fin2] at hη
  simp only [Finset.mem_insert, Finset.mem_singleton] at hη
  obtain ⟨c0, c1, c2, c3⟩ := countOcc_two
  obtain ⟨w0, w1, w2, w3⟩ := weight_K2 2 two_pos
  rw [gibbs, Z_K2, card_internal_two]
  rcases hη with rfl | rfl | rfl | rfl
  · rw [w0, c0]; norm_num
  · rw [w1, c1]; norm_num
  · rw [w2, c2]; norm_num
  · rw [w3, c3]; norm_num

/-- **Conjecture 00000006630 (hard-core lattice-gas reading).** Two lattice-gas models with
identical correlation-inequality profiles but different equilibria; both show the same explicit
violation of the positive-correlation inequality, and their configuration counts differ (`Z = 3`
versus `Z = 5`; these are the literal numbers of internal-state configurations, whose uniform
distribution has the equilibrium as occupation marginal). -/
theorem conjecture6630 :
    ∃ M₁ M₂ : LatticeGas (Fin 2),
      profile M₁ = profile M₂ ∧
      gibbs M₁ ≠ gibbs M₂ ∧
      (expect M₁ (fun η => occ {0} η * occ {1} η) < expect M₁ (occ {0}) * expect M₁ (occ {1})) ∧
      (expect M₂ (fun η => occ {0} η * occ {1} η) < expect M₂ (occ {0}) * expect M₂ (occ {1})) ∧
      Z M₁ = 3 ∧ Z M₂ = 5 ∧
      Fintype.card (InternalConfig 1) = 3 ∧ Fintype.card (InternalConfig 2) = 5 ∧
      (∀ η, gibbs M₁ η = (countOcc 1 η : ℝ) / Fintype.card (InternalConfig 1)) ∧
      (∀ η, gibbs M₂ η = (countOcc 2 η : ℝ) / Fintype.card (InternalConfig 2)) := by
  refine ⟨K2 1 one_pos, K2 2 two_pos, profile_K2_eq _ _ _ _, ?_, violation_K2 _ _,
    violation_K2 _ _, ?_, ?_, card_internal_one, card_internal_two, gibbs_eq_count_one,
    gibbs_eq_count_two⟩
  · intro h
    have := congrFun h {0}
    rw [gibbs_K2_zero, gibbs_K2_zero] at this
    norm_num at this
  · rw [Z_K2]; norm_num
  · rw [Z_K2]; norm_num

end Submission00000006630
