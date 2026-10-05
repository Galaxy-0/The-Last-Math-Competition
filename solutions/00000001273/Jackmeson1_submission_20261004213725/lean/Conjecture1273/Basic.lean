import Mathlib

/-!
# Conjecture 00000001273 is false

> For any mixing SFT under a Z² action, the count of periodic points has main term
> λ^{t₁t₂}·(1 + O(2^{-min t})) as t₁, t₂ → ∞.

Readings (both refuted): `Conjecture` (literal: `|P - λ^{t₁t₂}| ≤ C·2^{-min(t₁,t₂)}·λ^{t₁t₂}` for
`t₁, t₂ ≥ max(T,1)`) and `ConjectureMainTerm` (`P/λ^{t₁t₂} → 1`), over all nonempty mixing `ℤ²`
SFTs `X ⊆ Fin n ^ (ℤ × ℤ)`, with `P = perCount X t₁ t₂` the number of points fixed by `σ^(t₁,0)`
and `σ^(0,t₂)`. Witness: `X3 = {x ∈ {0,1,2}^(ℤ×ℤ) : x(i,j) ≠ x(i+1,j)}`, with
`P(t₁,t₂) = (2^{t₁} + 2(-1)^{t₁})^{t₂}`. For even `t₁` the ratio `P/λ^{t₁t₂} = r^{t₂}` stays in
`[1/2, 3/2]` for all large `t₂` only if `λ^{t₁} = 2^{t₁} + 2`; three consecutive even `t₁` clash.
-/

namespace Conjecture1273

open Finset

/-! ## 1. Full shift, patterns, SFTs, mixing, periodic points -/

/-- Configurations of the full shift `{0, …, n-1}^(ℤ × ℤ)`. -/
abbrev Config (n : ℕ) : Type := ℤ × ℤ → Fin n

/-- The `ℤ²` shift action: `(σ^v x)(u) = x(u + v)`. -/
def shift {n : ℕ} (v : ℤ × ℤ) (x : Config n) : Config n := fun u => x (u + v)

/-- A finite pattern: a finite window `support` and its symbols (values off `support` are
irrelevant). -/
structure Pattern (n : ℕ) where
  /-- the finite window -/
  support : Finset (ℤ × ℤ)
  /-- the symbols (only the values on `support` matter) -/
  val : ℤ × ℤ → Fin n

/-- `x` shows `p` at position `v`: `x (v + u) = p.val u` for all `u ∈ p.support`. -/
def Occurs {n : ℕ} (x : Config n) (p : Pattern n) (v : ℤ × ℤ) : Prop :=
  ∀ u ∈ p.support, x (v + u) = p.val u

/-- `X` is an SFT: the configurations in which none of finitely many forbidden patterns occurs. -/
def IsSFT {n : ℕ} (X : Set (Config n)) : Prop :=
  ∃ forbidden : List (Pattern n), X = {x | ∀ p ∈ forbidden, ∀ v : ℤ × ℤ, ¬ Occurs x p v}

/-- The sup norm on `ℤ²`. -/
def supNorm (v : ℤ × ℤ) : ℕ := max v.1.natAbs v.2.natAbs

/-- Topological mixing of the `ℤ²` action, cylinder form: for finite patterns `p, q` occurring in
`X` there is `N` such that for all `‖v‖_∞ ≥ N` some point of `X` shows `p` at `0` and `q` at `v`. -/
def IsMixing {n : ℕ} (X : Set (Config n)) : Prop :=
  ∀ p q : Pattern n, (∃ x ∈ X, Occurs x p 0) → (∃ y ∈ X, Occurs y q 0) →
    ∃ N : ℕ, ∀ v : ℤ × ℤ, N ≤ supNorm v → ∃ z ∈ X, Occurs z p 0 ∧ Occurs z q v

/-- Points of `X` fixed by `σ^(t₁,0)` and `σ^(0,t₂)`. -/
def perPts {n : ℕ} (X : Set (Config n)) (t₁ t₂ : ℕ) : Set (Config n) :=
  {x | x ∈ X ∧ shift ((t₁ : ℤ), 0) x = x ∧ shift (0, (t₂ : ℤ)) x = x}

/-- The periodic-point count `P_X(t₁,t₂)`. -/
noncomputable def perCount {n : ℕ} (X : Set (Config n)) (t₁ t₂ : ℕ) : ℕ :=
  (perPts X t₁ t₂).ncard

/-! ## 2. The two readings of the conjecture -/

/-- Literal reading: `P_X(t₁,t₂) = λ^{t₁t₂}(1 + O(2^{-min(t₁,t₂)}))` as `t₁, t₂ → ∞`. -/
def HasPeriodicAsymptotics {n : ℕ} (X : Set (Config n)) : Prop :=
  ∃ lam : ℝ, 0 < lam ∧ ∃ C : ℝ, ∃ T : ℕ, ∀ t₁ t₂ : ℕ, 1 ≤ t₁ → 1 ≤ t₂ → T ≤ t₁ → T ≤ t₂ →
    |(perCount X t₁ t₂ : ℝ) - lam ^ (t₁ * t₂)| ≤ C * (1 / 2 : ℝ) ^ min t₁ t₂ * lam ^ (t₁ * t₂)

/-- Conjecture 00000001273, literal reading. -/
def Conjecture : Prop :=
  ∀ (n : ℕ) (X : Set (Config n)), X.Nonempty → IsSFT X → IsMixing X → HasPeriodicAsymptotics X

/-- "Main term" reading: `P_X(t₁,t₂)/λ^{t₁t₂} → 1` as `t₁, t₂ → ∞`. -/
def HasMainTerm {n : ℕ} (X : Set (Config n)) : Prop :=
  ∃ lam : ℝ, 0 < lam ∧ ∀ ε : ℝ, 0 < ε → ∃ T : ℕ, ∀ t₁ t₂ : ℕ, 1 ≤ t₁ → 1 ≤ t₂ → T ≤ t₁ →
    T ≤ t₂ → |(perCount X t₁ t₂ : ℝ) - lam ^ (t₁ * t₂)| ≤ ε * lam ^ (t₁ * t₂)

/-- Conjecture 00000001273, "main term" reading. -/
def ConjectureMainTerm : Prop :=
  ∀ (n : ℕ) (X : Set (Config n)), X.Nonempty → IsSFT X → IsMixing X → HasMainTerm X

/-! ## 3. Periodic points form a finite set -/

theorem perPts_apply_emod {n : ℕ} {X : Set (Config n)} {t₁ t₂ : ℕ} {x : Config n}
    (hx : x ∈ perPts X t₁ t₂) (a b : ℤ) : x (a % t₁, b % t₂) = x (a, b) := by
  have h1 : Function.Periodic x ((t₁ : ℤ), (0 : ℤ)) := fun u => congrFun hx.2.1 u
  have h2 : Function.Periodic x ((0 : ℤ), (t₂ : ℤ)) := fun u => congrFun hx.2.2 u
  have e : ((a % t₁, b % t₂) : ℤ × ℤ) =
      (a, b) - (b / t₂) • ((0 : ℤ), (t₂ : ℤ)) - (a / t₁) • ((t₁ : ℤ), (0 : ℤ)) := by
    ext <;> simp [Int.emod_def, mul_comm]
  rw [e, h1.sub_zsmul_eq, h2.sub_zsmul_eq]

theorem perPts_congr {n : ℕ} {X : Set (Config n)} {t₁ t₂ : ℕ} {x : Config n}
    (hx : x ∈ perPts X t₁ t₂) {a a' b b' : ℤ} (ha : (a : ZMod t₁) = a')
    (hb : (b : ZMod t₂) = b') : x (a, b) = x (a', b') := by
  rw [← perPts_apply_emod hx a b, ← perPts_apply_emod hx a' b',
    (ZMod.intCast_eq_intCast_iff' a a' t₁).1 ha, (ZMod.intCast_eq_intCast_iff' b b' t₂).1 hb]

/-- For `t₁, t₂ ≥ 1` and every `X`, the periodic points of period `(t₁, t₂)` form a finite set
(each is determined by its values on a `t₁ × t₂` box), so `perCount` counts a finite set. -/
theorem perPts_finite {n : ℕ} (X : Set (Config n)) {t₁ t₂ : ℕ} (h₁ : 1 ≤ t₁) (h₂ : 1 ≤ t₂) :
    (perPts X t₁ t₂).Finite := by
  have : NeZero t₁ := ⟨by omega⟩
  have : NeZero t₂ := ⟨by omega⟩
  refine Set.Finite.of_finite_image
    (f := fun (x : Config n) (p : ZMod t₁ × ZMod t₂) => x ((p.1.val : ℤ), (p.2.val : ℤ)))
    (Set.toFinite _) fun x hx y hy hxy => funext fun ⟨a, b⟩ => ?_
  rw [← perPts_apply_emod hx, ← perPts_apply_emod hy]
  have := congrFun hxy ((a : ZMod t₁), (b : ZMod t₂))
  simp only [ZMod.val_intCast] at this
  exact this

/-! ## 4. The witness `X3`: a nonempty mixing SFT -/

/-- Rows are proper 3-colourings of `ℤ`; no vertical constraint. -/
def X3 : Set (Config 3) := {x | ∀ i j : ℤ, x (i, j) ≠ x (i + 1, j)}

theorem X3_nonempty : X3.Nonempty :=
  ⟨fun u => if Even u.1 then 0 else 1, fun i j => by
    by_cases h : Even i <;> simp [h]⟩

/-- The forbidden horizontal domino `aa` on the window `{(0,0), (1,0)}`. -/
def domino (a : Fin 3) : Pattern 3 := ⟨{(0, 0), (1, 0)}, fun _ => a⟩

/-- `X3` is the SFT with the three forbidden dominoes `00`, `11`, `22`. -/
theorem X3_isSFT : IsSFT X3 := by
  refine ⟨List.ofFn domino, ?_⟩
  ext x
  have hd : ∀ a i j, Occurs x (domino a) (i, j) ↔ x (i, j) = a ∧ x (i + 1, j) = a := by
    intro a i j
    simp [Occurs, domino]
  simp only [X3, Set.mem_ofPred_eq, List.forall_mem_ofFn_iff, Prod.forall, hd]
  constructor
  · rintro h a i j ⟨h1, h2⟩
    exact h i j (h1.trans h2.symm)
  · intro h i j hij
    exact h (x (i, j)) i j ⟨rfl, hij.symm⟩

/-- A colour different from `a` and from `b`. -/
def third (a b : Fin 3) : Fin 3 :=
  if a ≠ 0 ∧ b ≠ 0 then 0 else if a ≠ 1 ∧ b ≠ 1 then 1 else 2

theorem third_ne (a b : Fin 3) : third a b ≠ a ∧ third a b ≠ b := by
  fin_cases a <;> fin_cases b <;> decide

section Gluing

open Classical

variable (G : Set (ℤ × ℤ))

/-- Sites of row `j` where the glued point copies `y`. -/
def yZone (i j : ℤ) : Prop := (i, j) ∈ G ∨ ((i - 1, j) ∈ G ∧ (i + 2, j) ∈ G)

/-- Buffer sites: outside the `y`-zone but horizontally adjacent to it. -/
def buffer (i j : ℤ) : Prop := ¬ yZone G i j ∧ (yZone G (i - 1) j ∨ yZone G (i + 1) j)

/-- `y` on the `y`-zone, `x` elsewhere. -/
noncomputable def glue0 (x y : Config 3) (i j : ℤ) : Fin 3 :=
  if yZone G i j then y (i, j) else x (i, j)

/-- Glue `x` (away from `G`) and `y` (on `G`), recolouring buffer sites. -/
noncomputable def glue (x y : Config 3) : Config 3 := fun u =>
  if buffer G u.1 u.2 then third (glue0 G x y (u.1 - 1) u.2) (glue0 G x y (u.1 + 1) u.2)
  else glue0 G x y u.1 u.2

theorem glue_mem {x y : Config 3} (hx : x ∈ X3) (hy : y ∈ X3) : glue G x y ∈ X3 := by
  intro i j
  have hnb : ¬ (buffer G i j ∧ buffer G (i + 1) j) := by
    rintro ⟨h1, h2⟩
    unfold buffer yZone at h1 h2
    ring_nf at h1 h2
    tauto
  have e : i + 1 - 1 = i := by ring
  simp only [glue]
  by_cases b1 : buffer G i j <;> by_cases b2 : buffer G (i + 1) j
  · exact absurd ⟨b1, b2⟩ hnb
  · rw [if_pos b1, if_neg b2]
    exact (third_ne _ _).2
  · rw [if_neg b1, if_pos b2, e]
    exact (third_ne _ _).1.symm
  · rw [if_neg b1, if_neg b2]
    unfold glue0
    by_cases y1 : yZone G i j <;> by_cases y2 : yZone G (i + 1) j
    · rw [if_pos y1, if_pos y2]
      exact hy i j
    · exact absurd ⟨y2, Or.inl (by rwa [e])⟩ b2
    · exact absurd ⟨y1, Or.inr y2⟩ b1
    · rw [if_neg y1, if_neg y2]
      exact hx i j

/-- Away from `G` (at sup-distance `≥ 2`) the glued point equals `x`. -/
theorem glue_eq_left {x y : Config 3} {a : ℤ × ℤ} (ha : ∀ b ∈ G, 1 < supNorm (a - b)) :
    glue G x y a = x a := by
  obtain ⟨i, j⟩ := a
  have g0 : (i, j) ∉ G := fun h => by simpa [supNorm] using ha _ h
  have g1 : (i - 1, j) ∉ G := fun h => by simpa [supNorm] using ha _ h
  have g2 : (i + 1, j) ∉ G := fun h => by simpa [supNorm] using ha _ h
  have ny : ¬ yZone G i j := by unfold yZone; tauto
  have nb : ¬ buffer G i j := by
    unfold buffer yZone
    rw [show i - 1 + 2 = i + 1 by ring, show i + 1 - 1 = i by ring]
    tauto
  simp only [glue, glue0]
  rw [if_neg nb, if_neg ny]

/-- On `G` the glued point equals `y`. -/
theorem glue_eq_right (x y : Config 3) {b : ℤ × ℤ} (hb : b ∈ G) : glue G x y b = y b := by
  obtain ⟨i, j⟩ := b
  have hy : yZone G i j := Or.inl hb
  simp only [glue, glue0]
  rw [if_neg fun h => h.1 hy, if_pos hy]

end Gluing

/-- `X3` is mixing: glue a point showing `p` at `0` with a translate of a point showing `q`. -/
theorem X3_isMixing : IsMixing X3 := by
  rintro p q ⟨x, hx, hxp⟩ ⟨y, hy, hyq⟩
  obtain ⟨M, hpM, hqM⟩ : ∃ M : ℕ, (∀ a ∈ p.support, supNorm a ≤ M) ∧
      ∀ b ∈ q.support, supNorm b ≤ M :=
    ⟨(p.support ∪ q.support).sup supNorm, fun a ha => Finset.le_sup (Finset.mem_union_left _ ha),
      fun b hb => Finset.le_sup (Finset.mem_union_right _ hb)⟩
  refine ⟨2 * M + 2, fun v hv => ?_⟩
  -- the translate `y' = σ^{-v} y` shows `q` at `v` and lies in `X3`
  have hy' : shift (-v) y ∈ X3 := fun i j => by
    have e1 : ((i, j) : ℤ × ℤ) + -v = (i - v.1, j - v.2) := by
      ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg] <;> ring
    have e2 : ((i + 1, j) : ℤ × ℤ) + -v = (i - v.1 + 1, j - v.2) := by
      ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg] <;> ring
    simpa only [shift, e1, e2] using hy (i - v.1) (j - v.2)
  let G : Set (ℤ × ℤ) := (fun u => v + u) '' ↑q.support
  refine ⟨glue G x (shift (-v) y), glue_mem G hx hy', fun u hu => ?_, fun u hu => ?_⟩
  · rw [zero_add, glue_eq_left G (fun c hc => ?_)]
    · simpa using hxp u hu
    obtain ⟨b, hb, rfl⟩ := hc
    have h1 := hpM u hu
    have h2 := hqM b hb
    obtain ⟨a1, a2⟩ := u
    obtain ⟨b1, b2⟩ := b
    obtain ⟨v1, v2⟩ := v
    simp only [supNorm, max_le_iff, le_max_iff, lt_max_iff, Prod.mk_add_mk, Prod.mk_sub_mk]
      at h1 h2 hv ⊢
    rcases hv with hv | hv
    · left
      omega
    · right
      omega
  · rw [glue_eq_right G _ _ ⟨u, hu, rfl⟩]
    have h1 := hyq u hu
    rw [zero_add] at h1
    simpa [shift, add_neg_cancel_comm] using h1

/-! ## 5. Counting the periodic points of `X3` -/

/-- Proper 3-colourings of the cycle `ℤ/t`; `cycCount t` is their number. -/
abbrev CycCol (t : ℕ) : Type := {r : ZMod t → Fin 3 // ∀ i, r i ≠ r (i + 1)}

/-- The number `c(t)` of proper 3-colourings of the cycle `ℤ/t`. -/
noncomputable def cycCount (t : ℕ) : ℕ := Nat.card (CycCol t)

/-- A periodic point of `X3` of period `(t₁, t₂)` is a `ℤ/t₂`-family of rows, each a proper
3-colouring of the cycle `ℤ/t₁`. -/
noncomputable def perEquiv (t₁ t₂ : ℕ) [NeZero t₁] [NeZero t₂] :
    perPts X3 t₁ t₂ ≃ (ZMod t₂ → CycCol t₁) where
  toFun x b := ⟨fun a => x.1 ((a.val : ℤ), (b.val : ℤ)), fun a => by
    have h := x.2.1 (a.val : ℤ) (b.val : ℤ)
    have e : x.1 ((a.val : ℤ) + 1, (b.val : ℤ)) = x.1 (((a + 1).val : ℤ), (b.val : ℤ)) :=
      perPts_congr x.2 (by simp) rfl
    rw [e] at h
    exact h⟩
  invFun R := ⟨fun u => (R (u.2 : ZMod t₂)).1 (u.1 : ZMod t₁), by
    refine ⟨fun i j => ?_, ?_, ?_⟩
    · simpa using (R (j : ZMod t₂)).2 (i : ZMod t₁)
    · funext u
      simp [shift]
    · funext u
      simp [shift]⟩
  left_inv x := Subtype.ext <| funext fun ⟨_, _⟩ => perPts_congr x.2 (by simp) (by simp)
  right_inv R := funext fun b => Subtype.ext <| funext fun a => by simp

theorem perCount_X3 (t₁ t₂ : ℕ) [NeZero t₁] [NeZero t₂] :
    perCount X3 t₁ t₂ = cycCount t₁ ^ t₂ := by
  rw [perCount, ← Nat.card_coe_set_eq, Nat.card_congr (perEquiv t₁ t₂), Nat.card_fun,
    Nat.card_zmod]
  rfl

/-- Proper colourings of the path `0 - 1 - ⋯ - m`. -/
def PathProper {m : ℕ} (r : Fin (m + 1) → Fin 3) : Prop := ∀ k : Fin m, r k.castSucc ≠ r k.succ

instance {m : ℕ} (r : Fin (m + 1) → Fin 3) : Decidable (PathProper r) :=
  inferInstanceAs (Decidable (∀ k : Fin m, r k.castSucc ≠ r k.succ))

/-- Proper 3-colourings of the path on `m + 1` vertices with end colours `a`, `b` (the `(a,b)`
entry of `(J - I)^m`, `J - I` the transfer matrix). -/
def pathCount (m : ℕ) (a b : Fin 3) : ℕ :=
  ∑ r : Fin (m + 1) → Fin 3, if r 0 = a ∧ r (Fin.last m) = b ∧ PathProper r then 1 else 0

/-- Transfer-matrix recursion: `pathCount (m+1) a b = ∑_{d ≠ a} pathCount m d b`. -/
theorem pathCount_succ (m : ℕ) (a b : Fin 3) :
    pathCount (m + 1) a b = ∑ d : Fin 3, if d ≠ a then pathCount m d b else 0 := by
  have hcons (c : Fin 3) (s : Fin (m + 1) → Fin 3) :
      PathProper (Fin.cons c s : Fin (m + 2) → Fin 3) ↔ c ≠ s 0 ∧ PathProper s := by
    unfold PathProper
    rw [Fin.forall_fin_succ]
    simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, ← Fin.succ_castSucc]
  have aux (e : Fin 3) (X Y : Prop) [Decidable X] [Decidable Y] :
      (∑ c : Fin 3, if c = a ∧ X ∧ c ≠ e ∧ Y then 1 else 0 : ℕ) =
        ∑ d : Fin 3, if d ≠ a then (if e = d ∧ X ∧ Y then 1 else 0) else 0 := by
    fin_cases a <;> fin_cases e <;> by_cases hX : X <;> by_cases hY : Y <;>
      simp only [Fin.sum_univ_three] <;> simp [hX, hY]
  unfold pathCount
  have hc : ∀ p : Fin 3 × (Fin (m + 1) → Fin 3),
      (Fin.consEquiv (fun _ => Fin 3)) p = Fin.cons p.1 p.2 := fun _ => rfl
  rw [← (Fin.consEquiv (fun _ => Fin 3)).sum_comp, Fintype.sum_prod_type]
  simp only [hc, Fin.cons_zero, Fin.cons_last, hcons]
  rw [Finset.sum_comm, Finset.sum_congr rfl fun s _ => aux _ _ _, Finset.sum_comm]
  exact Finset.sum_congr rfl fun d _ => by split_ifs <;> simp

/-- `3 · pathCount m a b = 2^m + 2(-1)^m` if `a = b`, and `2^m - (-1)^m` if `a ≠ b`. -/
theorem pathCount_formula (m : ℕ) (a b : Fin 3) :
    (3 * pathCount m a b : ℤ) = 2 ^ m + (if a = b then 2 else -1) * (-1) ^ m := by
  induction m generalizing a with
  | zero =>
    have h0 : pathCount 0 a b = if a = b then 1 else 0 := by
      unfold pathCount
      rw [← (Equiv.funUnique (Fin 1) (Fin 3)).symm.sum_comp]
      fin_cases a <;> fin_cases b <;> simp [PathProper]
    rw [h0]
    split_ifs <;> norm_num
  | succ m ih =>
    rw [pathCount_succ]
    have h0 := ih 0
    have h1 := ih 1
    have h2 := ih 2
    push_cast
    fin_cases a <;> fin_cases b <;> simp [Fin.sum_univ_three] at h0 h1 h2 ⊢ <;>
      first
        | linear_combination h1 + h2
        | linear_combination h0 + h2
        | linear_combination h0 + h1

/-- The cycle count as the sum of the off-diagonal path counts. -/
theorem cycCount_eq_sum (m : ℕ) :
    cycCount (m + 1) = ∑ a : Fin 3, ∑ b : Fin 3, if a ≠ b then pathCount m a b else 0 := by
  have h : cycCount (m + 1) = Nat.card {r : Fin (m + 1) → Fin 3 // ∀ i, r i ≠ r (i + 1)} := rfl
  rw [h, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
  have key (r : Fin (m + 1) → Fin 3) :
      (∀ i, r i ≠ r (i + 1)) ↔ (PathProper r ∧ r (Fin.last m) ≠ r 0) := by
    rw [Fin.forall_fin_succ']
    simp only [Fin.coeSucc_eq_succ, Fin.last_add_one]
    rfl
  have aux (e f : Fin 3) (P : Prop) [Decidable P] :
      (∑ a : Fin 3, ∑ b : Fin 3,
        if a ≠ b then (if e = a ∧ f = b ∧ P then 1 else 0) else 0 : ℕ) =
        if P ∧ f ≠ e then 1 else 0 := by
    fin_cases e <;> fin_cases f <;> by_cases hP : P <;>
      simp only [Fin.sum_univ_three] <;> simp [hP]
  simp only [key]
  unfold pathCount
  rw [← Finset.sum_congr rfl fun r _ => aux (r 0) (r (Fin.last m)) (PathProper r),
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => by split_ifs <;> simp

/-- The number of proper 3-colourings of the cycle `ℤ/t` is `2^t + 2(-1)^t` for `t ≥ 1`. -/
theorem cycCount_formula (t : ℕ) (ht : 1 ≤ t) : (cycCount t : ℤ) = 2 ^ t + 2 * (-1) ^ t := by
  obtain ⟨m, rfl⟩ : ∃ m, t = m + 1 := ⟨t - 1, by omega⟩
  have hab : ∀ a b : Fin 3, a ≠ b → (3 * pathCount m a b : ℤ) = 2 ^ m - (-1) ^ m := by
    intro a b h
    rw [pathCount_formula, if_neg h]
    ring
  have h3 : (3 : ℤ) * cycCount (m + 1) = 3 * (2 ^ (m + 1) + 2 * (-1) ^ (m + 1)) := by
    rw [cycCount_eq_sum]
    push_cast
    simp (config := { decide := true }) only [Fin.sum_univ_three, ne_eq, if_true, if_false,
      add_zero, zero_add]
    linear_combination hab 0 1 (by decide) + hab 0 2 (by decide) + hab 1 0 (by decide) +
      hab 1 2 (by decide) + hab 2 0 (by decide) + hab 2 1 (by decide)
  linarith

/-- **Periodic-point count of `X3`:** `P(t₁,t₂) = (2^{t₁} + 2(-1)^{t₁})^{t₂}` for `t₁, t₂ ≥ 1`. -/
theorem perCount_X3_formula (t₁ t₂ : ℕ) (h₁ : 1 ≤ t₁) (h₂ : 1 ≤ t₂) :
    (perCount X3 t₁ t₂ : ℤ) = (2 ^ t₁ + 2 * (-1) ^ t₁) ^ t₂ := by
  have : NeZero t₁ := ⟨by omega⟩
  have : NeZero t₂ := ⟨by omega⟩
  rw [perCount_X3, Nat.cast_pow, cycCount_formula t₁ h₁]

theorem perCount_X3_even (k t₂ : ℕ) (hk : 1 ≤ k) (h₂ : 1 ≤ t₂) :
    (perCount X3 (2 * k) t₂ : ℝ) = ((2 : ℝ) ^ (2 * k) + 2) ^ t₂ := by
  have h := perCount_X3_formula (2 * k) t₂ (by omega) h₂
  have e : ((-1 : ℤ)) ^ (2 * k) = 1 := by rw [pow_mul]; norm_num
  rw [e, mul_one] at h
  exact_mod_cast h

/-! ## 6. The refutation -/

/-- If `a^t ≤ 2 b^t` and `b^t ≤ 2 a^t` for all `t ≥ N`, then `a = b`. -/
theorem eq_of_pow_comparable {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (N : ℕ)
    (h : ∀ t, N ≤ t → a ^ t ≤ 2 * b ^ t ∧ b ^ t ≤ 2 * a ^ t) : a = b := by
  have key : ∀ {a b : ℝ}, 0 < a → a < b → (∀ t, N ≤ t → b ^ t ≤ 2 * a ^ t) → False := by
    intro a b ha hab h
    have h1ab : 1 < b / a := (one_lt_div ha).2 hab
    obtain ⟨M, hM⟩ := pow_unbounded_of_one_lt 2 h1ab
    have h1 : (b / a) ^ M ≤ (b / a) ^ (max M N) := pow_le_pow_right₀ h1ab.le (le_max_left _ _)
    rw [div_pow, div_pow, le_div_iff₀ (pow_pos ha _)] at h1
    have h4 := mul_lt_mul_of_pos_right hM (pow_pos ha (max M N))
    rw [div_pow] at h4
    linarith [h (max M N) (le_max_right _ _)]
  rcases lt_trichotomy a b with hab | hab | hab
  · exact (key ha hab fun t ht => (h t ht).2).elim
  · exact hab
  · exact (key hb hab fun t ht => (h t ht).1).elim

/-- Core estimate: no `λ > 0` keeps `|P(t₁,t₂) - λ^{t₁t₂}| ≤ λ^{t₁t₂}/2` for all large periods. -/
theorem X3_no_half_bound (lam : ℝ) (hlam : 0 < lam) (T : ℕ)
    (h : ∀ t₁ t₂ : ℕ, 1 ≤ t₁ → 1 ≤ t₂ → T ≤ t₁ → T ≤ t₂ →
      |(perCount X3 t₁ t₂ : ℝ) - lam ^ (t₁ * t₂)| ≤ 1 / 2 * lam ^ (t₁ * t₂)) : False := by
  -- for every even `t₁ = 2k ≥ T`, letting `t₂ → ∞` forces `λ^{2k} = 2^{2k} + 2`
  have key : ∀ k, T + 1 ≤ k → lam ^ (2 * k) = (2 : ℝ) ^ (2 * k) + 2 := by
    intro k hk
    refine eq_of_pow_comparable (pow_pos hlam _) (by positivity) (T + 1) fun t ht => ?_
    have h' := abs_le.1 (h (2 * k) t (by omega) (by omega) (by omega) (by omega))
    rw [perCount_X3_even k t (by omega) (by omega), pow_mul] at h'
    have hp : 0 < (lam ^ (2 * k)) ^ t := pow_pos (pow_pos hlam _) t
    constructor <;> linarith [h'.1, h'.2]
  -- three consecutive even values are incompatible
  have e0 := key (T + 1) le_rfl
  have e1 := key (T + 2) (by omega)
  have e2 := key (T + 3) (by omega)
  rw [show 2 * (T + 2) = 2 * (T + 1) + 2 by omega, pow_add, e0, pow_add] at e1
  rw [show 2 * (T + 3) = 2 * (T + 1) + 4 by omega, pow_add, e0, pow_add] at e2
  have hA : (0 : ℝ) < 2 ^ (2 * (T + 1)) := by positivity
  set A : ℝ := 2 ^ (2 * (T + 1))
  -- e1 : (A + 2) λ² = 4A + 2 and e2 : (A + 2) λ⁴ = 16A + 2 force 18A = 0
  have h18 : (18 : ℝ) * A = 0 := by
    linear_combination (4 * A + 2 + (A + 2) * lam ^ 2) * e1 - (A + 2) * e2
  linarith

theorem not_hasMainTerm_X3 : ¬ HasMainTerm X3 := by
  rintro ⟨lam, hlam, h⟩
  obtain ⟨T, hT⟩ := h (1 / 2) (by norm_num)
  exact X3_no_half_bound lam hlam T hT

theorem not_hasPeriodicAsymptotics_X3 : ¬ HasPeriodicAsymptotics X3 := by
  rintro ⟨lam, hlam, C, T, h⟩
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / (2 * (|C| + 1)) by positivity)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  refine X3_no_half_bound lam hlam (max T N) fun t₁ t₂ h1 h2 h3 h4 => ?_
  have hmin : (1 / 2 : ℝ) ^ min t₁ t₂ ≤ (1 / 2) ^ N := pow_le_pow_of_le_one (by norm_num)
    (by norm_num) (le_min (le_of_max_le_right h3) (le_of_max_le_right h4))
  have hC1 : (0 : ℝ) < |C| + 1 := by positivity
  have hC : C * (1 / 2 : ℝ) ^ min t₁ t₂ ≤ 1 / 2 :=
    calc C * (1 / 2 : ℝ) ^ min t₁ t₂ ≤ (|C| + 1) * (1 / 2) ^ min t₁ t₂ :=
          mul_le_mul_of_nonneg_right (by linarith [le_abs_self C]) (by positivity)
      _ ≤ (|C| + 1) * (1 / (2 * (|C| + 1))) :=
          mul_le_mul_of_nonneg_left (hmin.trans hN.le) hC1.le
      _ = 1 / 2 := by field_simp
  exact (h t₁ t₂ h1 h2 (le_of_max_le_left h3) (le_of_max_le_left h4)).trans
    (mul_le_mul_of_nonneg_right hC (pow_pos hlam _).le)

/-- Infinite-family violation, literal reading: for every `λ > 0`, `C`, `T` there are periods
`t₁, t₂ ≥ T` with `|P(t₁,t₂) - λ^{t₁t₂}| > C · 2^{-min(t₁,t₂)} · λ^{t₁t₂}`. -/
theorem X3_violates_periodicAsymptotics (lam : ℝ) (hlam : 0 < lam) (C : ℝ) (T : ℕ) :
    ∃ t₁ t₂ : ℕ, 1 ≤ t₁ ∧ 1 ≤ t₂ ∧ T ≤ t₁ ∧ T ≤ t₂ ∧
      C * (1 / 2 : ℝ) ^ min t₁ t₂ * lam ^ (t₁ * t₂) <
        |(perCount X3 t₁ t₂ : ℝ) - lam ^ (t₁ * t₂)| := by
  by_contra hcon
  push Not at hcon
  exact not_hasPeriodicAsymptotics_X3 ⟨lam, hlam, C, T, hcon⟩

/-- Infinite-family violation, main-term reading: for every `λ > 0` and `T` there are periods
`t₁, t₂ ≥ T` with `|P(t₁,t₂)/λ^{t₁t₂} - 1| > 1/2`. -/
theorem X3_violates_mainTerm (lam : ℝ) (hlam : 0 < lam) (T : ℕ) :
    ∃ t₁ t₂ : ℕ, 1 ≤ t₁ ∧ 1 ≤ t₂ ∧ T ≤ t₁ ∧ T ≤ t₂ ∧
      1 / 2 * lam ^ (t₁ * t₂) < |(perCount X3 t₁ t₂ : ℝ) - lam ^ (t₁ * t₂)| := by
  by_contra hcon
  push Not at hcon
  exact X3_no_half_bound lam hlam T hcon

/-! ## 7. Main theorems -/

/-- `X3` satisfies every hypothesis of the class, has finitely many periodic points of each period,
the explicit count, and violates both readings. -/
theorem X3_counterexample :
    X3.Nonempty ∧ IsSFT X3 ∧ IsMixing X3 ∧
      (∀ t₁ t₂ : ℕ, 1 ≤ t₁ → 1 ≤ t₂ → (perPts X3 t₁ t₂).Finite) ∧
      (∀ t₁ t₂ : ℕ, 1 ≤ t₁ → 1 ≤ t₂ →
        (perCount X3 t₁ t₂ : ℤ) = (2 ^ t₁ + 2 * (-1) ^ t₁) ^ t₂) ∧
      ¬ HasPeriodicAsymptotics X3 ∧ ¬ HasMainTerm X3 :=
  ⟨X3_nonempty, X3_isSFT, X3_isMixing, fun _ _ h₁ h₂ => perPts_finite X3 h₁ h₂,
    perCount_X3_formula, not_hasPeriodicAsymptotics_X3, not_hasMainTerm_X3⟩

/-- **Main theorem.** Conjecture 00000001273 (literal reading, written out) is false. -/
theorem conjecture_00000001273_false :
    ¬ ∀ (n : ℕ) (X : Set (Config n)), X.Nonempty → IsSFT X → IsMixing X →
      ∃ lam : ℝ, 0 < lam ∧ ∃ C : ℝ, ∃ T : ℕ, ∀ t₁ t₂ : ℕ, 1 ≤ t₁ → 1 ≤ t₂ → T ≤ t₁ → T ≤ t₂ →
        |(perCount X t₁ t₂ : ℝ) - lam ^ (t₁ * t₂)| ≤
          C * (1 / 2 : ℝ) ^ min t₁ t₂ * lam ^ (t₁ * t₂) := fun h =>
  not_hasPeriodicAsymptotics_X3 (h 3 X3 X3_nonempty X3_isSFT X3_isMixing)

/-- The "main term" reading (written out) is false as well. -/
theorem conjecture_00000001273_mainTerm_false :
    ¬ ∀ (n : ℕ) (X : Set (Config n)), X.Nonempty → IsSFT X → IsMixing X →
      ∃ lam : ℝ, 0 < lam ∧ ∀ ε : ℝ, 0 < ε → ∃ T : ℕ, ∀ t₁ t₂ : ℕ, 1 ≤ t₁ → 1 ≤ t₂ →
        T ≤ t₁ → T ≤ t₂ →
          |(perCount X t₁ t₂ : ℝ) - lam ^ (t₁ * t₂)| ≤ ε * lam ^ (t₁ * t₂) := fun h =>
  not_hasMainTerm_X3 (h 3 X3 X3_nonempty X3_isSFT X3_isMixing)

/-- Capstone: both readings are refuted. -/
theorem conjecture_00000001273_disproved : ¬ Conjecture ∧ ¬ ConjectureMainTerm :=
  ⟨conjecture_00000001273_false, conjecture_00000001273_mainTerm_false⟩

end Conjecture1273
