import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Group.Action.Prod
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Rat.Cast.Order
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! In a finite transitive permutation group of degree `n ≥ 2` at least `|G| / n` elements are
fixed-point-free (Cameron–Cohen). Hence the derangement proportion is at least `1 / n`, the
constant `1 / 2` in the bound `c / n` is not tight, and the tight constant is `1`, attained by
the Frobenius group `S₃` on three points. -/
namespace Conjecture2311

open MulAction

/-- The derangements of an action: the elements without fixed points. -/
def derangements (G Ω : Type*) [Group G] [MulAction G Ω] : Set G :=
  {g | ∀ x : Ω, g • x ≠ x}

/-- The derangement proportion `|derangements| / |G|`. -/
noncomputable def derangementProportion (G Ω : Type*) [Group G] [MulAction G Ω] : ℚ :=
  (Nat.card (derangements G Ω) : ℚ) / (Nat.card G : ℚ)

/-- A Frobenius action: transitive on at least two points, no non-identity element fixes two
points, and some non-identity element fixes a point. -/
structure IsFrobenius (G Ω : Type*) [Group G] [MulAction G Ω] : Prop where
  transitive : IsPretransitive G Ω
  two_le : 2 ≤ Nat.card Ω
  fixes_at_most_one : ∀ g : G, g ≠ 1 → ∀ x y : Ω, g • x = x → g • y = y → x = y
  exists_fixing : ∃ g : G, g ≠ 1 ∧ ∃ x : Ω, g • x = x

section Counting

open scoped Classical

variable {G Ω : Type*} [Group G] [Fintype G] [MulAction G Ω] [Fintype Ω]

/-- A pair is fixed exactly when both of its entries are fixed. -/
def fixedByProdEquiv (g : G) : fixedBy (Ω × Ω) g ≃ fixedBy Ω g × fixedBy Ω g where
  toFun p := (⟨p.1.1, congrArg Prod.fst p.2⟩, ⟨p.1.2, congrArg Prod.snd p.2⟩)
  invFun q := ⟨(q.1.1, q.2.1), Prod.ext q.1.2 q.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Burnside's lemma for a transitive action: the fixed-point counts add up to `|G|`. -/
theorem sum_card_fixedBy [IsPretransitive G Ω] [Nonempty Ω] :
    ∑ g : G, Fintype.card (fixedBy Ω g) = Fintype.card G := by
  have hs : Subsingleton (orbitRel.Quotient G Ω) :=
    (pretransitive_iff_subsingleton_quotient G Ω).mp inferInstance
  have hn : Nonempty (orbitRel.Quotient G Ω) := (nonempty_quotient_iff _).mpr inferInstance
  have h1 : Fintype.card (Quotient (orbitRel G Ω)) = 1 :=
    le_antisymm (Fintype.card_le_one_iff_subsingleton.mpr hs) Fintype.card_pos
  rw [sum_card_fixedBy_eq_card_orbits_mul_card_group G Ω, h1, one_mul]

omit [Fintype G] in
/-- The diagonal and a pair of distinct points lie in different orbits on `Ω × Ω`. -/
theorem two_le_card_orbits_prod (h : ∃ a b : Ω, a ≠ b) :
    2 ≤ Fintype.card (Quotient (orbitRel G (Ω × Ω))) := by
  obtain ⟨a, b, hab⟩ := h
  refine Fintype.one_lt_card_iff.mpr
    ⟨Quotient.mk (orbitRel G (Ω × Ω)) (a, a), Quotient.mk (orbitRel G (Ω × Ω)) (a, b), ?_⟩
  intro heq
  have hmem : (a, a) ∈ orbit G (a, b) := Quotient.exact heq
  obtain ⟨g, hg⟩ := mem_orbit_iff.mp hmem
  have h1 : g • a = a := congrArg Prod.fst hg
  have h2 : g • b = a := congrArg Prod.snd hg
  exact hab (smul_left_cancel g (h1.trans h2.symm))

/-- Burnside's lemma on `Ω × Ω`: the squares of the fixed-point counts add up to at least
`2 |G|`. -/
theorem two_mul_card_le_sum_sq (h : ∃ a b : Ω, a ≠ b) :
    2 * Fintype.card G ≤ ∑ g : G, Fintype.card (fixedBy Ω g) ^ 2 := by
  have hB := sum_card_fixedBy_eq_card_orbits_mul_card_group G (Ω × Ω)
  have hsq : ∀ g : G, Fintype.card (fixedBy (Ω × Ω) g) = Fintype.card (fixedBy Ω g) ^ 2 := by
    intro g
    rw [Fintype.card_congr (fixedByProdEquiv g), Fintype.card_prod, sq]
  rw [Finset.sum_congr rfl fun g _ => hsq g] at hB
  rw [hB]
  exact Nat.mul_le_mul_right _ (two_le_card_orbits_prod h)

omit [Fintype G] in
/-- An element has no fixed point exactly when it is a derangement. -/
theorem card_fixedBy_eq_zero_iff (g : G) :
    Fintype.card (fixedBy Ω g) = 0 ↔ g ∈ derangements G Ω := by
  rw [Fintype.card_eq_zero_iff]
  constructor
  · intro h x hx
    exact h.false ⟨x, hx⟩
  · intro h
    exact ⟨fun x => h x.1 x.2⟩

/-- The number of derangements as a sum of indicators. -/
theorem card_derangements :
    Nat.card (derangements G Ω) =
      ∑ g : G, if Fintype.card (fixedBy Ω g) = 0 then 1 else 0 := by
  rw [← Finset.card_filter, Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  ext g
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact (card_fixedBy_eq_zero_iff g).symm

/-- The pointwise inequality behind the Cameron–Cohen bound. -/
theorem pointwise (f n : ℕ) (hf : f ≤ n) :
    f ^ 2 + n ≤ (n + 1) * f + n * (if f = 0 then 1 else 0) := by
  by_cases h0 : f = 0
  · subst h0
    simp
  · rw [if_neg h0]
    obtain ⟨a, rfl⟩ : ∃ a, f = a + 1 := ⟨f - 1, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, n = a + 1 + b := ⟨n - (a + 1), by omega⟩
    nlinarith [Nat.zero_le (a * b)]

/-- The Cameron–Cohen bound, for `Fintype` data. -/
theorem card_le_mul_card_derangements [IsPretransitive G Ω] (h : ∃ a b : Ω, a ≠ b) :
    Fintype.card G ≤ Fintype.card Ω * Nat.card (derangements G Ω) := by
  have hne : Nonempty Ω := let ⟨a, _⟩ := h; ⟨a⟩
  have hsum := sum_card_fixedBy (G := G) (Ω := Ω)
  have hsq := two_mul_card_le_sum_sq (G := G) h
  have hpt : ∀ g : G, Fintype.card (fixedBy Ω g) ^ 2 + Fintype.card Ω ≤
      (Fintype.card Ω + 1) * Fintype.card (fixedBy Ω g) +
        Fintype.card Ω * (if Fintype.card (fixedBy Ω g) = 0 then 1 else 0) :=
    fun g => pointwise _ _ (Fintype.card_subtype_le _)
  have htot := Finset.sum_le_sum fun g (_ : g ∈ Finset.univ) => hpt g
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    hsum, ← card_derangements, Finset.sum_const, Finset.card_univ, smul_eq_mul] at htot
  nlinarith

/-- In a Frobenius action exactly `|Ω| - 1` elements are derangements. -/
theorem card_derangements_add_one_of_frobenius (hF : IsFrobenius G Ω) :
    Nat.card (derangements G Ω) + 1 = Fintype.card Ω := by
  have := hF.transitive
  have hpos : 0 < Fintype.card Ω := by
    have := hF.two_le
    rw [Nat.card_eq_fintype_card] at this
    omega
  have hne : Nonempty Ω := Fintype.card_pos_iff.mp hpos
  have hsum := sum_card_fixedBy (G := G) (Ω := Ω)
  have hpt : ∀ g : G, Fintype.card (fixedBy Ω g) +
      (if Fintype.card (fixedBy Ω g) = 0 then 1 else 0) + (if g = 1 then 1 else 0) =
        1 + (if g = 1 then Fintype.card Ω else 0) := by
    intro g
    by_cases hg : g = 1
    · subst hg
      have hall : Fintype.card (fixedBy Ω (1 : G)) = Fintype.card Ω :=
        Fintype.card_congr (Equiv.subtypeUnivEquiv fun x => one_smul G x)
      rw [hall, if_neg (by omega), if_pos rfl, if_pos rfl]
      omega
    · rw [if_neg hg, if_neg hg]
      have hle : Fintype.card (fixedBy Ω g) ≤ 1 := by
        rw [Fintype.card_le_one_iff_subsingleton]
        exact ⟨fun x y => Subtype.ext (hF.fixes_at_most_one g hg x.1 y.1 x.2 y.2)⟩
      by_cases h0 : Fintype.card (fixedBy Ω g) = 0
      · rw [if_pos h0, h0]
      · rw [if_neg h0]
        omega
  have htot := Finset.sum_congr rfl fun g (_ : g ∈ Finset.univ) => hpt g
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, hsum,
    ← card_derangements, Finset.sum_ite_eq' Finset.univ (1 : G) fun _ => 1,
    Finset.sum_ite_eq' Finset.univ (1 : G) fun _ => Fintype.card Ω, Finset.sum_const,
    Finset.card_univ, smul_eq_mul] at htot
  simp only [Finset.mem_univ, if_true] at htot
  omega

end Counting

section Finite

variable (G Ω : Type*) [Group G] [Finite G] [MulAction G Ω] [Finite Ω]

/-- **Cameron–Cohen.** In a finite transitive permutation group of degree at least two, the
number of derangements times the degree is at least the group order. -/
theorem cameron_cohen [IsPretransitive G Ω] (h : 2 ≤ Nat.card Ω) :
    Nat.card G ≤ Nat.card Ω * Nat.card (derangements G Ω) := by
  have := Fintype.ofFinite G
  have := Fintype.ofFinite Ω
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at *
  exact card_le_mul_card_derangements (Fintype.one_lt_card_iff.mp h)

/-- The derangement proportion of a transitive group of degree `n ≥ 2` is at least `1 / n`. -/
theorem one_div_card_le_proportion [IsPretransitive G Ω] (h : 2 ≤ Nat.card Ω) :
    1 / (Nat.card Ω : ℚ) ≤ derangementProportion G Ω := by
  have hG : (0 : ℚ) < Nat.card G := by exact_mod_cast Nat.card_pos
  have hΩ : (0 : ℚ) < Nat.card Ω := by exact_mod_cast (by omega : 0 < Nat.card Ω)
  have hcc : (Nat.card G : ℚ) ≤ Nat.card Ω * Nat.card (derangements G Ω) := by
    exact_mod_cast cameron_cohen G Ω h
  unfold derangementProportion
  rw [div_le_div_iff₀ hΩ hG]
  linarith

/-- The claimed bound `(1 / 2) / n` is never attained: the proportion is strictly larger. -/
theorem half_div_card_lt_proportion [IsPretransitive G Ω] (h : 2 ≤ Nat.card Ω) :
    (1 / 2 : ℚ) / (Nat.card Ω : ℚ) < derangementProportion G Ω := by
  have hΩ : (0 : ℚ) < Nat.card Ω := by exact_mod_cast (by omega : 0 < Nat.card Ω)
  have h1 := one_div_card_le_proportion G Ω h
  have h2 : (1 / 2 : ℚ) / (Nat.card Ω : ℚ) < 1 / (Nat.card Ω : ℚ) := by
    apply div_lt_div_of_pos_right _ hΩ
    norm_num
  linarith

/-- In a Frobenius action of degree `n` exactly `n - 1` elements are derangements. -/
theorem frobenius_card_derangements (hF : IsFrobenius G Ω) :
    Nat.card (derangements G Ω) + 1 = Nat.card Ω := by
  have := Fintype.ofFinite G
  have := Fintype.ofFinite Ω
  rw [Nat.card_eq_fintype_card (α := Ω)]
  exact card_derangements_add_one_of_frobenius hF

/-- The derangement proportion of a Frobenius group of degree `n` is `(n - 1) / |G|`. -/
theorem frobenius_proportion (hF : IsFrobenius G Ω) :
    derangementProportion G Ω = ((Nat.card Ω : ℚ) - 1) / (Nat.card G : ℚ) := by
  have h := frobenius_card_derangements G Ω hF
  have hq : (Nat.card (derangements G Ω) : ℚ) + 1 = (Nat.card Ω : ℚ) := by exact_mod_cast h
  unfold derangementProportion
  rw [← hq]
  ring

/-- No Frobenius group attains the bound with the constant `1 / 2`. -/
theorem frobenius_ne_half (hF : IsFrobenius G Ω) :
    derangementProportion G Ω ≠ (1 / 2 : ℚ) / (Nat.card Ω : ℚ) := by
  have := hF.transitive
  exact (half_div_card_lt_proportion G Ω hF.two_le).ne'

end Finite

section Example

/-- The symmetric group on three points acts transitively. -/
instance : IsPretransitive (Equiv.Perm (Fin 3)) (Fin 3) :=
  ⟨fun x y => ⟨Equiv.swap x y, Equiv.swap_apply_left x y⟩⟩

/-- `S₃` on three points is a Frobenius group. -/
theorem s3_isFrobenius : IsFrobenius (Equiv.Perm (Fin 3)) (Fin 3) where
  transitive := inferInstance
  two_le := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num
  fixes_at_most_one := by decide
  exists_fixing := ⟨Equiv.swap 0 1, by decide, 2, by decide⟩

theorem card_s3 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rfl

/-- The Frobenius group `S₃` has derangement proportion exactly `1 / 3 = 1 / |Ω|`. -/
theorem s3_proportion :
    derangementProportion (Equiv.Perm (Fin 3)) (Fin 3) = 1 / (Nat.card (Fin 3) : ℚ) := by
  rw [frobenius_proportion _ _ s3_isFrobenius, card_s3, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  norm_num

end Example

section Statement

/-- The bound `c / |Ω| ≤ derangement proportion` for all finite transitive groups of degree at
least two. -/
def LowerBound (c : ℚ) : Prop :=
  ∀ (G Ω : Type) [Group G] [Finite G] [MulAction G Ω] [Finite Ω] [IsPretransitive G Ω],
    2 ≤ Nat.card Ω → c / (Nat.card Ω : ℚ) ≤ derangementProportion G Ω

/-- First reading of tightness: the constant cannot be enlarged. -/
def CannotBeImproved (c : ℚ) : Prop :=
  ∀ c' : ℚ, c < c' → ¬ LowerBound c'

/-- Second reading of tightness: some Frobenius group attains equality in the bound. -/
def AttainedByFrobenius (c : ℚ) : Prop :=
  ∃ (G Ω : Type) (_ : Group G) (_ : MulAction G Ω), Finite G ∧ Finite Ω ∧ IsFrobenius G Ω ∧
    derangementProportion G Ω = c / (Nat.card Ω : ℚ)

/-- Third reading of tightness: Frobenius groups come arbitrarily close to the bound. -/
def ApproachedByFrobenius (c : ℚ) : Prop :=
  ∀ ε : ℚ, 0 < ε → ∃ (G Ω : Type) (_ : Group G) (_ : MulAction G Ω), Finite G ∧ Finite Ω ∧
    IsFrobenius G Ω ∧ derangementProportion G Ω < (c + ε) / (Nat.card Ω : ℚ)

/-- The bound holds with the constant `1`. -/
theorem lowerBound_one : LowerBound 1 := by
  intro G Ω _ _ _ _ _ h
  exact one_div_card_le_proportion G Ω h

/-- In particular the bound of the source, with the constant `1 / 2`, holds. -/
theorem lowerBound_half : LowerBound (1 / 2) := by
  intro G Ω _ _ _ _ _ h
  exact (half_div_card_lt_proportion G Ω h).le

/-- The constant `1 / 2` can be improved. -/
theorem not_cannotBeImproved_half : ¬ CannotBeImproved (1 / 2) := fun h =>
  h 1 (by norm_num) lowerBound_one

/-- No Frobenius group attains the constant `1 / 2`. -/
theorem not_attainedByFrobenius_half : ¬ AttainedByFrobenius (1 / 2) := by
  rintro ⟨G, Ω, _, _, _, _, hF, h⟩
  exact frobenius_ne_half G Ω hF h

/-- Frobenius groups do not approach the constant `1 / 2`. -/
theorem not_approachedByFrobenius_half : ¬ ApproachedByFrobenius (1 / 2) := by
  intro h
  obtain ⟨G, Ω, _, _, _, _, hF, hlt⟩ := h (1 / 2) (by norm_num)
  have := hF.transitive
  have h1 := one_div_card_le_proportion G Ω hF.two_le
  have h2 : ((1 / 2 : ℚ) + 1 / 2) / (Nat.card Ω : ℚ) = 1 / (Nat.card Ω : ℚ) := by norm_num
  rw [h2] at hlt
  linarith

/-- The constant `1` is attained by the Frobenius group `S₃`. -/
theorem attainedByFrobenius_one : AttainedByFrobenius 1 :=
  ⟨Equiv.Perm (Fin 3), Fin 3, inferInstance, inferInstance, inferInstance, inferInstance,
    s3_isFrobenius, s3_proportion⟩

/-- The constant `1` cannot be improved. -/
theorem cannotBeImproved_one : CannotBeImproved 1 := by
  intro c' hc' h
  have h3 := h (Equiv.Perm (Fin 3)) (Fin 3)
    (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
  rw [s3_proportion, Nat.card_eq_fintype_card, Fintype.card_fin] at h3
  have h4 : c' / ((3 : ℕ) : ℚ) ≤ 1 / ((3 : ℕ) : ℚ) := h3
  rw [div_le_div_iff_of_pos_right (by norm_num)] at h4
  linarith

/-- The source's assertion: the bound with `c = 1 / 2` holds and this constant is tight, in at
least one of the three readings of tightness. -/
def Conjecture : Prop :=
  LowerBound (1 / 2) ∧
    (CannotBeImproved (1 / 2) ∨ AttainedByFrobenius (1 / 2) ∨ ApproachedByFrobenius (1 / 2))

/-- The source's assertion is false: its bound is true, but its tightness clause fails in each
of the three readings. -/
theorem conjecture_false : ¬ Conjecture := by
  rintro ⟨_, h | h | h⟩
  · exact not_cannotBeImproved_half h
  · exact not_attainedByFrobenius_half h
  · exact not_approachedByFrobenius_half h

/-- The corrected statement: the bound holds with `c = 1`, and this constant is tight in all
three readings. -/
theorem corrected_statement :
    LowerBound 1 ∧ CannotBeImproved 1 ∧ AttainedByFrobenius 1 ∧ ApproachedByFrobenius 1 := by
  refine ⟨lowerBound_one, cannotBeImproved_one, attainedByFrobenius_one, fun ε hε => ?_⟩
  refine ⟨Equiv.Perm (Fin 3), Fin 3, inferInstance, inferInstance, inferInstance, inferInstance,
    s3_isFrobenius, ?_⟩
  rw [s3_proportion, Nat.card_eq_fintype_card, Fintype.card_fin]
  apply div_lt_div_of_pos_right _ (by norm_num)
  linarith

end Statement

#print axioms cameron_cohen
#print axioms one_div_card_le_proportion
#print axioms half_div_card_lt_proportion
#print axioms frobenius_card_derangements
#print axioms frobenius_proportion
#print axioms frobenius_ne_half
#print axioms s3_isFrobenius
#print axioms s3_proportion
#print axioms lowerBound_one
#print axioms lowerBound_half
#print axioms not_cannotBeImproved_half
#print axioms not_attainedByFrobenius_half
#print axioms not_approachedByFrobenius_half
#print axioms conjecture_false
#print axioms corrected_statement

end Conjecture2311
