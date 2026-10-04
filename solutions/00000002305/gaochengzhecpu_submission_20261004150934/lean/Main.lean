import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.Index
import Mathlib.Order.Atoms
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Ring

/-! The Frobenius group `C₃₁ ⋊ C₅` of order 155 has exactly 11 conjugacy classes and a
maximal subgroup of index 31, so `k(G) ≥ [G:H] / 2` fails for a maximal subgroup `H`. -/
namespace Conjecture2305

/-- The multiplier `2 ^ k` in `ZMod 31`. As `2 ^ 5 = 32 = 1`, it depends only on `k` modulo 5. -/
def tw (k : ZMod 5) : ZMod 31 := 2 ^ k.val

theorem tw_zero : tw 0 = 1 := by decide

theorem tw_add : ∀ k l : ZMod 5, tw (k + l) = tw k * tw l := by decide

theorem tw_eq : ∀ k l : ZMod 5, tw k = tw l → k = l := by decide

theorem tw_pow_five : ∀ k : ZMod 5, tw k ^ 5 = 1 := by decide

/-- The element `(a, k)` stands for the affine map `x ↦ 2 ^ k * x + a` of `ZMod 31`. -/
@[ext] structure G where
  a : ZMod 31
  k : ZMod 5
deriving DecidableEq

def equivProd : G ≃ ZMod 31 × ZMod 5 where
  toFun g := (g.a, g.k)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype G := Fintype.ofEquiv _ equivProd.symm

/-- The semidirect product law `(a, k) (b, l) = (a + 2 ^ k * b, k + l)`. -/
instance : Group G where
  mul x y := ⟨x.a + tw x.k * y.a, x.k + y.k⟩
  one := ⟨0, 0⟩
  inv x := ⟨-(tw (-x.k) * x.a), -x.k⟩
  mul_assoc x y z := by
    apply G.ext
    · change x.a + tw x.k * y.a + tw (x.k + y.k) * z.a = x.a + tw x.k * (y.a + tw y.k * z.a)
      rw [tw_add]; ring
    · change x.k + y.k + z.k = x.k + (y.k + z.k)
      ring
  one_mul x := by
    apply G.ext
    · change 0 + tw 0 * x.a = x.a
      rw [tw_zero]; ring
    · change 0 + x.k = x.k
      ring
  mul_one x := by
    apply G.ext
    · change x.a + tw x.k * 0 = x.a
      ring
    · change x.k + 0 = x.k
      ring
  inv_mul_cancel x := by
    apply G.ext
    · change -(tw (-x.k) * x.a) + tw (-x.k) * x.a = 0
      ring
    · change -x.k + x.k = 0
      ring

@[simp] theorem mul_a (x y : G) : (x * y).a = x.a + tw x.k * y.a := rfl
@[simp] theorem mul_k (x y : G) : (x * y).k = x.k + y.k := rfl
@[simp] theorem one_a : (1 : G).a = 0 := rfl
@[simp] theorem one_k : (1 : G).k = 0 := rfl
@[simp] theorem inv_a (x : G) : x⁻¹.a = -(tw (-x.k) * x.a) := rfl
@[simp] theorem inv_k (x : G) : x⁻¹.k = -x.k := rfl

/-- The action of `G` on `ZMod 31` by affine maps. -/
def act (g : G) (x : ZMod 31) : ZMod 31 := tw g.k * x + g.a

theorem act_one (x : ZMod 31) : act 1 x = x := by
  simp [act, tw_zero]

theorem act_mul (g h : G) (x : ZMod 31) : act (g * h) x = act g (act h x) := by
  simp only [act, mul_a, mul_k, tw_add]; ring

/-- The action is faithful: `G` is a group of 155 affine permutations of `ZMod 31`. -/
theorem act_faithful : Function.Injective act := by
  intro g h hgh
  have h0 := congrFun hgh 0
  have h1 := congrFun hgh 1
  simp only [act, mul_zero, zero_add, mul_one] at h0 h1
  rw [h0] at h1
  exact G.ext h0 (tw_eq _ _ (add_right_cancel h1))

theorem card_G : Nat.card G = 155 := by
  rw [Nat.card_congr equivProd, Nat.card_prod, Nat.card_zmod, Nat.card_zmod]

/-- The point stabiliser of `0`: the multiplications `x ↦ 2 ^ k * x`. -/
def H : Subgroup G where
  carrier := {g | g.a = 0}
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    simp [hx, hy]
  one_mem' := rfl
  inv_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    simp [hx]

theorem mem_H {g : G} : g ∈ H ↔ act g 0 = 0 := by
  change g.a = 0 ↔ tw g.k * 0 + g.a = 0
  rw [mul_zero, zero_add]

def equivH : H ≃ ZMod 5 where
  toFun g := g.1.k
  invFun k := ⟨⟨0, k⟩, rfl⟩
  left_inv g := Subtype.ext (G.ext g.2.symm rfl)
  right_inv _ := rfl

theorem card_H : Nat.card H = 5 := by
  rw [Nat.card_congr equivH, Nat.card_zmod]

theorem index_H : H.index = 31 := by
  have h := H.card_mul_index
  rw [card_H, card_G] at h
  omega

/-- `H` is a maximal subgroup: a coatom of the subgroup lattice. -/
theorem H_maximal : IsCoatom H := by
  refine ⟨?_, ?_⟩
  · intro h
    have h5 := card_H
    rw [h, Subgroup.card_top, card_G] at h5
    omega
  · intro K hK
    have h1 : Nat.card H ∣ Nat.card K := Subgroup.card_dvd_of_le hK.le
    have h2 : Nat.card K ∣ Nat.card G := Subgroup.card_subgroup_dvd_card K
    rw [card_H] at h1
    rw [card_G] at h2
    obtain ⟨m, hm⟩ := h1
    have h3 : m ∣ 31 := by
      have h4 : 5 * m ∣ 5 * 31 := by rw [← hm]; exact h2
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h4
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 31)).mp h3 with rfl | rfl
    · exfalso
      have hHK : H = K := Subgroup.eq_of_le_of_card_ge hK.le (by rw [hm, card_H])
      exact hK.ne hHK
    · apply Subgroup.eq_top_of_card_eq
      rw [hm, card_G]

/-- Conjugation in coordinates. -/
theorem conj_a (c g : G) : (c * g * c⁻¹).a = tw c.k * g.a + (1 - tw g.k) * c.a := by
  have h : tw c.k * tw (-c.k) = 1 := by rw [← tw_add, add_neg_cancel, tw_zero]
  simp only [mul_a, mul_k, inv_a, tw_add]
  linear_combination (-(tw g.k) * c.a) * h

theorem conj_k (c g : G) : (c * g * c⁻¹).k = g.k := by
  simp

/-- Indices of the eleven class representatives. -/
abbrev Idx := Unit ⊕ Fin 6 ⊕ {k : ZMod 5 // k ≠ 0}

/-- Representatives: the identity, six translations, and four elements with `k ≠ 0`. -/
def rep : Idx → G
  | .inl _ => 1
  | .inr (.inl j) => ⟨3 ^ j.val, 0⟩
  | .inr (.inr k) => ⟨0, k.1⟩

theorem card_Idx : Nat.card Idx = 11 := by
  rw [Nat.card_eq_fintype_card]; decide

/-- The six cosets of `⟨2⟩` in the units of `ZMod 31` are represented by `3 ^ j`, `j < 6`. -/
theorem orbit_translation : ∀ a : ZMod 31, a ≠ 0 →
    ∃ j : Fin 6, ∃ l : ZMod 5, tw l * 3 ^ j.val = a := by decide

/-- For `k ≠ 0` the element `1 - 2 ^ k` is invertible modulo 31. -/
theorem solve_twisted : ∀ a : ZMod 31, ∀ k : ZMod 5, k ≠ 0 →
    ∃ b : ZMod 31, (1 - tw k) * b = a := by decide

/-- Every element is conjugate to one of the eleven representatives. -/
theorem exists_rep (g : G) : ∃ i : Idx, IsConj (rep i) g := by
  by_cases hk : g.k = 0
  · by_cases ha : g.a = 0
    · have hg : g = 1 := G.ext ha hk
      exact ⟨.inl (), hg ▸ IsConj.refl _⟩
    · obtain ⟨j, l, hjl⟩ := orbit_translation g.a ha
      refine ⟨.inr (.inl j), isConj_iff.mpr ⟨⟨0, l⟩, ?_⟩⟩
      apply G.ext
      · rw [conj_a]
        change tw l * 3 ^ j.val + (1 - tw 0) * 0 = g.a
        rw [mul_zero, add_zero, hjl]
      · rw [conj_k]
        exact hk.symm
  · obtain ⟨b, hb⟩ := solve_twisted g.a g.k hk
    refine ⟨.inr (.inr ⟨g.k, hk⟩), isConj_iff.mpr ⟨⟨b, 0⟩, ?_⟩⟩
    apply G.ext
    · rw [conj_a]
      change tw 0 * 0 + (1 - tw g.k) * b = g.a
      rw [mul_zero, zero_add, hb]
    · rw [conj_k]
      rfl

/-- A class function separating the representatives. -/
def label (g : G) : ZMod 5 × ZMod 31 := (g.k, if g.k = 0 then g.a ^ 5 else 0)

theorem label_conj (c g : G) : label (c * g * c⁻¹) = label g := by
  unfold label
  rw [conj_k, conj_a]
  by_cases hk : g.k = 0
  · simp [hk, tw_zero, mul_pow, tw_pow_five]
  · simp [hk]

theorem label_rep : ∀ i j : Idx, label (rep i) = label (rep j) → i = j := by decide

def classOf (i : Idx) : ConjClasses G := ConjClasses.mk (rep i)

theorem classOf_surjective : Function.Surjective classOf := by
  intro c
  obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
  obtain ⟨i, hi⟩ := exists_rep g
  exact ⟨i, ConjClasses.mk_eq_mk_iff_isConj.mpr hi⟩

theorem classOf_injective : Function.Injective classOf := by
  intro i j h
  obtain ⟨c, hc⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp h)
  apply label_rep
  rw [← hc, label_conj]

/-- The class number of `G` is exactly 11. -/
theorem card_conjClasses : Nat.card (ConjClasses G) = 11 := by
  rw [← card_Idx]
  exact (Nat.card_congr (Equiv.ofBijective classOf ⟨classOf_injective, classOf_surjective⟩)).symm

/-- The bound fails for `G` and `H` with `c = 1 / 2`. -/
theorem counterexample :
    (Nat.card (ConjClasses G) : ℚ) < (1 / 2 : ℚ) * (H.index : ℚ) := by
  rw [card_conjClasses, index_H]; norm_num

/-- More precisely, it fails for every constant `c > 11 / 31`. -/
theorem fails_above (c : ℚ) (hc : 11 / 31 < c) :
    (Nat.card (ConjClasses G) : ℚ) < c * (H.index : ℚ) := by
  rw [card_conjClasses, index_H]
  push_cast
  linarith

/-- The asserted bound `k(Γ) ≥ [Γ : M] / 2` for every finite group and maximal subgroup. -/
def ClaimedBound : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (M : Subgroup Γ), IsCoatom M →
    (1 / 2 : ℚ) * (M.index : ℚ) ≤ (Nat.card (ConjClasses Γ) : ℚ)

theorem conjecture_false : ¬ ClaimedBound := fun h =>
  absurd (h G H H_maximal) (not_le.mpr counterexample)

#print axioms act_faithful
#print axioms card_G
#print axioms index_H
#print axioms H_maximal
#print axioms exists_rep
#print axioms label_conj
#print axioms card_conjClasses
#print axioms counterexample
#print axioms fails_above
#print axioms conjecture_false

end Conjecture2305
