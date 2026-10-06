import Mathlib

/-!
# Conjecture 00000007751: MSD(1,2) = 9 is false

The conjecture asserts that the minimal uniform bound `MSD(1,2)` for the number of `ℚ`-rational
preperiodic points of a degree-2 rational map `P¹ → P¹` defined over `ℚ` equals `9`.

We exhibit the degree-2 map `f(z) = (-2z² - 3z - 1)/(2z² - z)` over `ℚ` with twelve distinct
preperiodic points in `P¹(ℚ)` (eleven of them finite), so `12 ≤ MSD(1,2)` and `MSD(1,2) ≠ 9`.

Conventions.
* `P¹(ℚ)` is modelled as `Option ℚ`: `some a` is the point `[a : 1]`, `none` is `∞ = [1 : 0]`.
* A rational map of degree `d` is `φ = p/q` with `p q : ℚ[X]` coprime and
  `max (deg p) (deg q) = d`; it acts on `P¹(ℚ)` by the homogeneous formula
  `[x : y] ↦ [F(x,y) : G(x,y)]`, `F = Y^d p(X/Y)`, `G = Y^d q(X/Y)`, i.e.
  `[a : 1] ↦ [p(a) : q(a)]` and `[1 : 0] ↦ [coeff p d : coeff q d]`.
* A point is preperiodic iff its forward orbit `{f^[n] x | n ∈ ℕ}` is finite (as in the statement).
-/

open Polynomial

namespace C7751

/-- A rational map of degree `d` over `ℚ`: `φ = p/q`, `p, q` coprime, `max (deg p) (deg q) = d`. -/
structure RatMap (d : ℕ) where
  p : ℚ[X]
  q : ℚ[X]
  coprime : IsCoprime p q
  natDegree_eq : max p.natDegree q.natDegree = d

/-- The point `[u : v]` of `P¹(ℚ)` (`none = ∞`); used only when `(u, v) ≠ (0, 0)`. -/
def proj (u v : ℚ) : Option ℚ := if v = 0 then none else some (u / v)

/-- The action on `P¹(ℚ) = Option ℚ` by the degree-`d` homogeneous formula. -/
def RatMap.act {d : ℕ} (f : RatMap d) : Option ℚ → Option ℚ
  | some a => proj (f.p.eval a) (f.q.eval a)
  | none => proj (f.p.coeff d) (f.q.coeff d)

/-- The homogeneous formula never produces `[0 : 0]`: the action is well defined. -/
theorem RatMap.act_wellDefined {d : ℕ} (hd : 1 ≤ d) (f : RatMap d) :
    (∀ a : ℚ, (f.p.eval a, f.q.eval a) ≠ (0, 0)) ∧ (f.p.coeff d, f.q.coeff d) ≠ (0, 0) := by
  refine ⟨fun a h => ?_, fun h => ?_⟩
  · obtain ⟨u, v, huv⟩ := f.coprime
    have := congrArg (eval a) huv
    simp only [Prod.mk.injEq] at h
    simp [eval_add, eval_mul, h.1, h.2] at this
  · simp only [Prod.mk.injEq] at h
    have hm := f.natDegree_eq
    rcases le_total f.p.natDegree f.q.natDegree with hpq | hpq
    · rw [max_eq_right hpq] at hm
      have hq : f.q ≠ 0 := by intro h0; rw [h0] at hm; simp at hm; omega
      exact hq (leadingCoeff_eq_zero.mp (by rw [leadingCoeff, hm]; exact h.2))
    · rw [max_eq_left hpq] at hm
      have hp : f.p ≠ 0 := by intro h0; rw [h0] at hm; simp at hm; omega
      exact hp (leadingCoeff_eq_zero.mp (by rw [leadingCoeff, hm]; exact h.1))

/-- Preperiodic point: the forward orbit is finite. -/
def IsPreperiodic {α : Type*} (g : α → α) (x : α) : Prop :=
  (Set.range fun n : ℕ => g^[n] x).Finite

/-- A point in a finite forward-invariant set is preperiodic. -/
theorem isPreperiodic_of_mem {α : Type*} (g : α → α) (S : Finset α)
    (hS : ∀ y ∈ S, g y ∈ S) {x : α} (hx : x ∈ S) : IsPreperiodic g x := by
  refine S.finite_toSet.subset ?_
  rintro _ ⟨n, rfl⟩
  induction n with
  | zero => simpa using hx
  | succ n ih => show g^[n + 1] x ∈ S; rw [Function.iterate_succ_apply']; exact hS _ ih

/-- `MSD(1,d)` over `ℚ`: the least `B ∈ ℕ∞` bounding the number of `ℚ`-rational preperiodic
points of every degree-`d` rational map over `ℚ` (`⊤` if there is no such bound). -/
noncomputable def MSD (d : ℕ) : ℕ∞ :=
  sInf {B : ℕ∞ | ∀ f : RatMap d, ∀ S : Finset (Option ℚ),
    (∀ x ∈ S, IsPreperiodic f.act x) → (S.card : ℕ∞) ≤ B}

/-- Numerator `-2X² - 3X - 1 = -(2X+1)(X+1)`. -/
noncomputable def P : ℚ[X] := -2 * X ^ 2 - 3 * X - 1
/-- Denominator `2X² - X = X(2X-1)`. -/
noncomputable def Q : ℚ[X] := 2 * X ^ 2 - X

theorem P_Q_coprime : IsCoprime P Q := by
  -- Bezout identity: (4X - 3) P + (4X + 5) Q = 3
  refine ⟨C (1 / 3) * (4 * X - 3), C (1 / 3) * (4 * X + 5), ?_⟩
  have h : (4 * X - 3) * P + (4 * X + 5) * Q = C 3 := by
    simp only [P, Q, map_ofNat]; ring
  calc C (1 / 3) * (4 * X - 3) * P + C (1 / 3) * (4 * X + 5) * Q
      = C (1 / 3) * ((4 * X - 3) * P + (4 * X + 5) * Q) := by ring
    _ = 1 := by rw [h, ← C_mul]; norm_num

theorem P_natDegree : P.natDegree = 2 := by unfold P; compute_degree!
theorem Q_natDegree : Q.natDegree = 2 := by unfold Q; compute_degree!

/-- The witness `f(z) = (-2z² - 3z - 1)/(2z² - z)`, a degree-2 rational map over `ℚ`. -/
noncomputable def f : RatMap 2 where
  p := P
  q := Q
  coprime := P_Q_coprime
  natDegree_eq := by rw [P_natDegree, Q_natDegree]; rfl

theorem f_act_some (a : ℚ) :
    f.act (some a) = proj (-2 * a ^ 2 - 3 * a - 1) (2 * a ^ 2 - a) := by
  simp [RatMap.act, f, P, Q]

theorem f_act_none : f.act none = some (-1) := by
  simp [RatMap.act, f, P, Q, proj, coeff_X, coeff_one]

/-- Twelve points of `P¹(ℚ)`: the 3-cycles `∞ → -1 → 0 → ∞`, `-5/2 → -2/5 → -1/6 → -5/2`
and the tails `-1/2 → 0`, `1/2 → ∞`, `-1/4 → -1`, `-3/2 → -1/6`, `-1/3 → -2/5`, `2 → -5/2`. -/
def S : Finset (Option ℚ) :=
  {none, some (-1), some 0, some (-5/2), some (-2/5), some (-1/6),
   some (-1/2), some (1/2), some (-1/4), some (-3/2), some (-1/3), some 2}

theorem S_card : S.card = 12 := by
  simp only [S]
  repeat rw [Finset.card_insert_of_notMem (by simp <;> norm_num)]
  rfl

theorem S_invariant : ∀ x ∈ S, f.act x ∈ S := by
  intro x hx
  simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [f_act_none, f_act_some, proj] <;> norm_num [S]

/-- Main theorem: a degree-2 rational map over `ℚ` with twelve distinct `ℚ`-rational
preperiodic points in `P¹(ℚ)`. -/
theorem exists_degree_two_twelve_preperiodic :
    ∃ g : RatMap 2, ∃ T : Finset (Option ℚ), T.card = 12 ∧ ∀ x ∈ T, IsPreperiodic g.act x :=
  ⟨f, S, S_card, fun _ hx => isPreperiodic_of_mem f.act S S_invariant hx⟩

/-- Even counting only finite points `[a : 1]`, there are eleven preperiodic points. -/
theorem exists_degree_two_eleven_affine_preperiodic :
    ∃ g : RatMap 2, ∃ T : Finset ℚ, T.card = 11 ∧ ∀ a ∈ T, IsPreperiodic g.act (some a) := by
  refine ⟨f, {-1, 0, -5/2, -2/5, -1/6, -1/2, 1/2, -1/4, -3/2, -1/3, 2}, ?_, fun a ha => ?_⟩
  · repeat rw [Finset.card_insert_of_notMem (by simp; norm_num)]
    rfl
  · refine isPreperiodic_of_mem f.act S S_invariant ?_
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [S]

/-- `MSD(1,2) ≥ 12`. -/
theorem twelve_le_MSD : (12 : ℕ∞) ≤ MSD 2 := by
  refine le_sInf fun B hB => ?_
  have := hB f S (fun _ hx => isPreperiodic_of_mem f.act S S_invariant hx)
  rwa [S_card] at this

/-- The conjecture `MSD(1,2) = 9` (over `ℚ`) is false. -/
theorem MSD_ne_nine : MSD 2 ≠ 9 := by
  intro h
  have := twelve_le_MSD
  rw [h] at this
  exact absurd this (by norm_num)

/-- Equivalently: it is false that every degree-2 rational map over `ℚ` has at most nine
`ℚ`-rational preperiodic points in `P¹(ℚ)`. -/
theorem not_all_le_nine :
    ¬ ∀ g : RatMap 2, ∀ T : Finset (Option ℚ), (∀ x ∈ T, IsPreperiodic g.act x) → T.card ≤ 9 := by
  intro h
  have := h f S (fun _ hx => isPreperiodic_of_mem f.act S S_invariant hx)
  rw [S_card] at this
  omega

end C7751
