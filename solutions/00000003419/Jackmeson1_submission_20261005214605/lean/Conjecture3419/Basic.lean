import Mathlib

/-!
# Conjecture 00000003419: commute time = 2 * (number of edges) * effective resistance

For a finite connected simple graph `G` with `m` edges and vertices `a, b`, the commute time of the
simple random walk satisfies `H(a,b) + H(b,a) = 2 m R_eff(a,b)` (Chandra, Raghavan, Ruzzo, Smolensky,
STOC 1989; with Tiwari, Comput. Complexity 1996).  The proof is the "difference of hitting-time potentials" argument: the hitting-time
vector `h_b = H(., b)` satisfies `L h_b = d - 2m e_b`, so `(h_b - h_a) / (2m)` is the unit-current
potential from `a` to `b`.

* `trans G x y`: one-step transition probability `1/deg x` if `x ~ y`, else `0`.
* `pathProb G w`: probability that the walk follows the trajectory `w 0, ..., w t`.
* `survProb G b t x = P_x(T_b > t)`: total probability of the trajectories from `x` that avoid `b`
  at all times `0, ..., t` (`T_b` = first time `s >= 0` with `X_s = b`).
* `hittingTime G x b = E_x[T_b] = sum_{t >= 0} P_x(T_b > t)` (tail-sum formula); we prove the series
  is summable, so `tsum` is the genuine sum.
* `IsUnitPotential G a b v`: `L v = e_a - e_b` (`L = G.lapMatrix ℝ`), and
  `effRes G a b = v a - v b` for such a `v`; we prove a `v` exists and `v a - v b` is independent of it.
-/

open Finset Matrix

set_option linter.unusedSectionVars false

namespace C3419

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Transition probability of the simple random walk on `G`. -/
noncomputable def trans (x y : V) : ℝ := if G.Adj x y then ((G.degree x : ℝ))⁻¹ else 0

/-- Probability that the walk started at `w 0` follows the trajectory `w 0, w 1, ..., w t`. -/
noncomputable def pathProb {t : ℕ} (w : Fin (t + 1) → V) : ℝ :=
  ∏ i : Fin t, trans G (w i.castSucc) (w i.succ)

/-- `P_x(T_b > t)`: probability that the walk from `x` avoids `b` at all times `0, ..., t`. -/
noncomputable def survProb (b : V) (t : ℕ) (x : V) : ℝ :=
  ∑ w : Fin (t + 1) → V, if w 0 = x ∧ ∀ i, w i ≠ b then pathProb G w else 0

/-- Expected hitting time `H(x,b) = E_x[T_b] = ∑_{t ≥ 0} P_x(T_b > t)`. -/
noncomputable def hittingTime (x b : V) : ℝ := ∑' t, survProb G b t x

/-- Commute time `κ(a,b) = H(a,b) + H(b,a)`. -/
noncomputable def commuteTime (a b : V) : ℝ := hittingTime G a b + hittingTime G b a

/-- `v` is a unit-current potential from `a` to `b`: `L v = e_a - e_b`. -/
def IsUnitPotential (a b : V) (v : V → ℝ) : Prop :=
  G.lapMatrix ℝ *ᵥ v = Pi.single a 1 - Pi.single b 1

/-- Effective resistance `R_eff(a,b) = v a - v b` for a unit-current potential `v`. -/
noncomputable def effRes (a b : V) : ℝ :=
  by classical exact if h : ∃ v, IsUnitPotential G a b v then h.choose a - h.choose b else 0

lemma trans_nonneg (x y : V) : 0 ≤ trans G x y := by
  unfold trans; split_ifs <;> positivity

lemma survProb_nonneg (b : V) (t : ℕ) (x : V) : 0 ≤ survProb G b t x :=
  Finset.sum_nonneg fun _ _ => by
    split_ifs
    · exact Finset.prod_nonneg fun i _ => trans_nonneg G _ _
    · exact le_refl 0

lemma survProb_self (b : V) (t : ℕ) : survProb G b t b = 0 :=
  Finset.sum_eq_zero fun _ _ => if_neg fun h => h.2 0 h.1

lemma survProb_zero (b x : V) : survProb G b 0 x = if x = b then 0 else 1 := by
  unfold survProb pathProb
  simp only [Fin.prod_univ_zero]
  rw [Fintype.sum_equiv (Equiv.funUnique (Fin 1) V) _ (fun y => if y = x ∧ y ≠ b then 1 else 0)
    (fun w => by simp [Fin.default_eq_zero])]
  simp only [ite_and, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases hx : x = b <;> simp [hx]

lemma survProb_succ (b : V) (t : ℕ) (x : V) :
    survProb G b (t + 1) x = if x = b then 0 else ∑ y, trans G x y * survProb G b t y := by
  by_cases hx : x = b
  · subst hx; simp [survProb_self]
  rw [if_neg hx]
  unfold survProb
  rw [← (Fin.consEquiv (fun _ : Fin (t + 2) => V)).sum_comp, Fintype.sum_prod_type]
  simp only [Fin.consEquiv_apply, Fin.cons_zero, Fin.forall_fin_succ, Fin.cons_succ, pathProb,
    Fin.prod_univ_succ, Fin.castSucc_zero, ← Fin.succ_castSucc]
  rw [Finset.sum_eq_single x (fun y _ hy => Finset.sum_eq_zero fun _ _ => if_neg fun h => hy h.1)
    (by simp)]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [ite_and, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp [hx]

lemma sum_trans_mul (x : V) (f : V → ℝ) :
    ∑ y, trans G x y * f y = (G.degree x : ℝ)⁻¹ * ∑ y ∈ G.neighborFinset x, f y := by
  simp only [trans, ite_mul, zero_mul, Finset.mul_sum, ← Finset.sum_filter,
    SimpleGraph.neighborFinset_eq_filter]

lemma degree_pos_of_ne (hG : G.Connected) {x b : V} (h : x ≠ b) : (0 : ℝ) < G.degree x := by
  obtain ⟨p⟩ := hG.preconnected x b
  cases p with
  | nil => exact absurd rfl h
  | cons hadj _ => exact_mod_cast (G.degree_pos_iff_exists_adj x).2 ⟨_, hadj⟩

/-- Column sums of the Laplacian vanish: `∑ₓ (L f) x = 0`. -/
lemma sum_lapMatrix_mulVec (f : V → ℝ) : ∑ x, (G.lapMatrix ℝ *ᵥ f) x = 0 := by
  have h : (fun _ => (1 : ℝ)) ⬝ᵥ (G.lapMatrix ℝ *ᵥ f) = 0 := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, (SimpleGraph.isSymm_lapMatrix (R := ℝ) (G := G)).eq,
      G.lapMatrix_mulVec_const_eq_zero, zero_dotProduct]
  simpa [dotProduct] using h

/-- For `x ≠ b`, `(L g) x = deg x` is the first-step relation `g x = 1 + ∑ y, P(x,y) g y`. -/
lemma lap_eq_degree_iff (hG : G.Connected) {x b : V} (hx : x ≠ b) (g : V → ℝ) :
    (G.lapMatrix ℝ *ᵥ g) x = G.degree x ↔ g x = 1 + ∑ y, trans G x y * g y := by
  have hd := degree_pos_of_ne G hG hx
  rw [SimpleGraph.lapMatrix_mulVec_apply, sum_trans_mul]
  have key : (G.degree x : ℝ) * ((G.degree x : ℝ)⁻¹ * ∑ y ∈ G.neighborFinset x, g y) =
      ∑ y ∈ G.neighborFinset x, g y := by field_simp
  constructor
  · intro h; apply mul_left_cancel₀ hd.ne'; rw [mul_add, key]; linarith
  · intro h; rw [h, mul_add, key]; ring

/-- Dirichlet problem: some `g` has `g b = 0` and `(L g) x = deg x` for all `x ≠ b`. -/
lemma exists_dirichlet (hG : G.Connected) (b : V) :
    ∃ g : V → ℝ, g b = 0 ∧ ∀ x, x ≠ b → (G.lapMatrix ℝ *ᵥ g) x = G.degree x := by
  let M : Matrix V V ℝ :=
    Matrix.of fun x y => if x = b then (if y = b then 1 else 0) else G.lapMatrix ℝ x y
  have hM : ∀ g x, (M *ᵥ g) x = if x = b then g b else (G.lapMatrix ℝ *ᵥ g) x := by
    intro g x
    by_cases hx : x = b
    · simp [M, hx, Matrix.mulVec, dotProduct]
    · simp [M, hx, Matrix.mulVec, dotProduct]
  have hinj : Function.Injective M.mulVec := by
    intro g₁ g₂ h12
    have h0 : M *ᵥ (g₁ - g₂) = 0 := by rw [Matrix.mulVec_sub, h12, sub_self]
    have hgb : (g₁ - g₂) b = 0 := by simpa [hM] using congrFun h0 b
    have hLx : ∀ x, x ≠ b → (G.lapMatrix ℝ *ᵥ (g₁ - g₂)) x = 0 := fun x hx => by
      simpa [hM, hx] using congrFun h0 x
    have hL : G.lapMatrix ℝ *ᵥ (g₁ - g₂) = 0 := by
      funext x
      by_cases hx : x = b
      · subst hx
        rw [Pi.zero_apply, ← sum_lapMatrix_mulVec G (g₁ - g₂),
          Finset.sum_eq_single x (fun y _ hy => hLx y hy) (by simp)]
      · exact hLx x hx
    have hc := G.lapMatrix_mulVec_eq_zero_iff_forall_reachable.1 hL
    funext x
    have : (g₁ - g₂) x = 0 := by rw [hc x b (hG.preconnected x b), hgb]
    exact sub_eq_zero.1 this
  obtain ⟨g, hg⟩ := (Matrix.mulVec_surjective_iff_isUnit.2 (Matrix.mulVec_injective_iff_isUnit.1 hinj))
    (fun x => if x = b then 0 else (G.degree x : ℝ))
  exact ⟨g, by simpa [hM] using congrFun hg b, fun x hx => by simpa [hM, hx] using congrFun hg x⟩

/-- Minimum principle: the Dirichlet solution is nonnegative. -/
lemma dirichlet_nonneg (hG : G.Connected) (b : V) (g : V → ℝ) (hgb : g b = 0)
    (hL : ∀ x, x ≠ b → (G.lapMatrix ℝ *ᵥ g) x = G.degree x) (x : V) : 0 ≤ g x := by
  have : Nonempty V := ⟨b⟩
  obtain ⟨x0, -, hx0⟩ := Finset.exists_min_image Finset.univ g Finset.univ_nonempty
  by_cases h : x0 = b
  · rw [← hgb, ← h]; exact hx0 x (Finset.mem_univ x)
  · exfalso
    have h1 := hL x0 h
    rw [SimpleGraph.lapMatrix_mulVec_apply] at h1
    have h2 : (G.degree x0 : ℝ) * g x0 ≤ ∑ y ∈ G.neighborFinset x0, g y := by
      calc (G.degree x0 : ℝ) * g x0 = ∑ y ∈ G.neighborFinset x0, g x0 := by
            rw [Finset.sum_const, G.card_neighborFinset_eq_degree, nsmul_eq_mul]
        _ ≤ _ := Finset.sum_le_sum fun y _ => hx0 y (Finset.mem_univ y)
    have h3 := degree_pos_of_ne G hG h
    linarith

/-- Partial sums of `t ↦ P_x(T_b > t)` are bounded by any nonnegative solution of the
first-step equations. -/
lemma partial_le (b : V) (g : V → ℝ) (hg0 : ∀ x, 0 ≤ g x)
    (hge : ∀ x, x ≠ b → g x = 1 + ∑ y, trans G x y * g y) :
    ∀ N x, ∑ t ∈ Finset.range N, survProb G b t x ≤ g x := by
  intro N
  induction N with
  | zero => intro x; simpa using hg0 x
  | succ N ih =>
    intro x
    by_cases hx : x = b
    · subst hx; simp only [survProb_self, Finset.sum_const_zero]; exact hg0 _
    rw [Finset.sum_range_succ']
    simp only [survProb_succ, survProb_zero, hx, if_false]
    rw [Finset.sum_comm, hge x hx]
    have : ∀ y, ∑ t ∈ Finset.range N, trans G x y * survProb G b t y ≤ trans G x y * g y :=
      fun y => by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (ih y) (trans_nonneg G x y)
    linarith [Finset.sum_le_sum fun y (_ : y ∈ Finset.univ) => this y]

/-- The tail series defining `H(x,b)` converges. -/
theorem summable_survProb (hG : G.Connected) (b x : V) : Summable fun t => survProb G b t x := by
  obtain ⟨g, hgb, hL⟩ := exists_dirichlet G hG b
  exact summable_of_sum_range_le (fun t => survProb_nonneg G b t x)
    (fun N => partial_le G b g (dirichlet_nonneg G hG b g hgb hL)
      (fun y hy => (lap_eq_degree_iff G hG hy g).1 (hL y hy)) N x)

lemma hittingTime_self (b : V) : hittingTime G b b = 0 := by
  simp [hittingTime, survProb_self]

/-- First-step equation for the expected hitting time. -/
theorem hittingTime_step (hG : G.Connected) {x b : V} (hx : x ≠ b) :
    hittingTime G x b = 1 + ∑ y, trans G x y * hittingTime G y b := by
  unfold hittingTime
  rw [(summable_survProb G hG b x).tsum_eq_zero_add]
  simp only [survProb_succ, survProb_zero, hx, if_false]
  rw [Summable.tsum_finsetSum (fun y _ => (summable_survProb G hG b y).mul_left _)]
  simp_rw [tsum_mul_left]

/-- `L h_b = d - 2m e_b` for the hitting-time vector `h_b = H(·, b)`. -/
theorem lap_hittingTime (hG : G.Connected) (b x : V) :
    (G.lapMatrix ℝ *ᵥ fun y => hittingTime G y b) x =
      G.degree x - if x = b then 2 * (#G.edgeFinset : ℝ) else 0 := by
  have hne : ∀ y, y ≠ b → (G.lapMatrix ℝ *ᵥ fun y => hittingTime G y b) y = G.degree y :=
    fun y hy => (lap_eq_degree_iff G hG hy _).2 (hittingTime_step G hG hy)
  by_cases hx : x = b
  · subst hx
    rw [if_pos rfl]
    have hsum := sum_lapMatrix_mulVec G (fun y => hittingTime G y x)
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x),
      Finset.sum_congr rfl (fun y hy => hne y (Finset.ne_of_mem_erase hy))] at hsum
    have hdeg : ∑ y, (G.degree y : ℝ) = 2 * #G.edgeFinset := by
      exact_mod_cast G.sum_degrees_eq_twice_card_edges
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x)] at hdeg
    linarith
  · rw [if_neg hx, sub_zero]; exact hne x hx

/-- Sanity check: `trans G x ·` is a probability distribution when `deg x > 0`. -/
lemma sum_trans (x : V) (hx : 0 < G.degree x) : ∑ y, trans G x y = 1 := by
  have h := sum_trans_mul G x (fun _ => 1)
  simp only [mul_one, Finset.sum_const, G.card_neighborFinset_eq_degree, nsmul_eq_mul] at h
  rw [h]; exact inv_mul_cancel₀ (by exact_mod_cast hx.ne')

lemma two_card_edges_pos (hG : G.Connected) {a b : V} (hab : a ≠ b) :
    (0 : ℝ) < 2 * #G.edgeFinset := by
  have hdeg : ∑ y, (G.degree y : ℝ) = 2 * #G.edgeFinset := by
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  rw [← hdeg]
  exact lt_of_lt_of_le (degree_pos_of_ne G hG hab)
    (Finset.single_le_sum (fun y _ => Nat.cast_nonneg (G.degree y)) (Finset.mem_univ a))

/-- Two unit-current potentials differ by a constant, so `v a - v b` does not depend on `v`. -/
lemma potential_diff_eq (hG : G.Connected) {a b : V} {u v : V → ℝ}
    (hu : IsUnitPotential G a b u) (hv : IsUnitPotential G a b v) : u a - u b = v a - v b := by
  have h : G.lapMatrix ℝ *ᵥ (u - v) = 0 := by rw [Matrix.mulVec_sub, hu, hv, sub_self]
  have := G.lapMatrix_mulVec_eq_zero_iff_forall_reachable.1 h a b (hG.preconnected a b)
  simp only [Pi.sub_apply] at this
  linarith

/-- Difference of hitting-time potentials: `(h_b - h_a) / (2m)` is the unit-current potential. -/
theorem hitting_potential (hG : G.Connected) {a b : V} (hab : a ≠ b) :
    IsUnitPotential G a b fun x =>
      (hittingTime G x b - hittingTime G x a) / (2 * #G.edgeFinset) := by
  have hm := two_card_edges_pos G hG hab
  have hm' : (#G.edgeFinset : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have e : (fun x => (hittingTime G x b - hittingTime G x a) / (2 * (#G.edgeFinset : ℝ))) =
      (2 * (#G.edgeFinset : ℝ))⁻¹ • ((fun y => hittingTime G y b) - fun y => hittingTime G y a) := by
    funext y; simp [div_eq_inv_mul]
  unfold IsUnitPotential
  rw [e, Matrix.mulVec_smul, Matrix.mulVec_sub]
  funext x
  simp only [Pi.smul_apply, Pi.sub_apply, lap_hittingTime G hG, Pi.single_apply, smul_eq_mul]
  by_cases hxa : x = a
  · subst hxa; simp [hab]; field_simp
  · by_cases hxb : x = b
    · subst hxb; simp [hxa]; field_simp
    · simp [hxa, hxb]

theorem exists_unitPotential (hG : G.Connected) (a b : V) : ∃ v, IsUnitPotential G a b v := by
  by_cases hab : a = b
  · subst hab; exact ⟨0, by simp [IsUnitPotential]⟩
  · exact ⟨_, hitting_potential G hG hab⟩

theorem commuteTime_eq_of_potential (hG : G.Connected) (a b : V) (v : V → ℝ)
    (hv : IsUnitPotential G a b v) : commuteTime G a b = 2 * #G.edgeFinset * (v a - v b) := by
  by_cases hab : a = b
  · subst hab; simp [commuteTime, hittingTime_self]
  have hm : (#G.edgeFinset : ℝ) ≠ 0 := ne_of_gt (by linarith [two_card_edges_pos G hG hab])
  rw [potential_diff_eq G hG hv (hitting_potential G hG hab)]
  simp only [hittingTime_self, commuteTime]
  field_simp
  ring

theorem effRes_eq (hG : G.Connected) {a b : V} {v : V → ℝ} (hv : IsUnitPotential G a b v) :
    effRes G a b = v a - v b := by
  have h : ∃ v, IsUnitPotential G a b v := ⟨v, hv⟩
  unfold effRes
  rw [dif_pos h]
  exact potential_diff_eq G hG h.choose_spec hv

theorem effRes_comm (hG : G.Connected) (a b : V) : effRes G a b = effRes G b a := by
  obtain ⟨v, hv⟩ := exists_unitPotential G hG a b
  have hv' : IsUnitPotential G b a (-v) := by
    unfold IsUnitPotential at *; rw [Matrix.mulVec_neg, hv, neg_sub]
  rw [effRes_eq G hG hv, effRes_eq G hG hv']
  simp only [Pi.neg_apply]; ring

/-- **Commute-time identity** (Chandra, Raghavan, Ruzzo, Smolensky, Tiwari).  For a finite
connected simple graph `G` with `m = #G.edgeFinset` edges and vertices `a, b`: the tail series of both
hitting times converge; a unit-current potential exists; for `a ≠ b` the normalized difference
`(h_b - h_a)/(2m)` of the hitting-time vectors is one; every unit-current potential `v` gives
`κ(a,b) = H(a,b) + H(b,a) = 2m (v a - v b)`, i.e. `κ(a,b) = 2m R_eff(a,b)`; and `κ` and `R_eff` are
symmetric. -/
theorem commute_time_identity (hG : G.Connected) (a b : V) :
    (Summable fun t => survProb G b t a) ∧ (Summable fun t => survProb G a t b) ∧
    (∃ v, IsUnitPotential G a b v) ∧
    (a ≠ b → IsUnitPotential G a b fun x =>
      (hittingTime G x b - hittingTime G x a) / (2 * #G.edgeFinset)) ∧
    (∀ v, IsUnitPotential G a b v → commuteTime G a b = 2 * #G.edgeFinset * (v a - v b)) ∧
    commuteTime G a b = 2 * #G.edgeFinset * effRes G a b ∧
    commuteTime G a b = commuteTime G b a ∧ effRes G a b = effRes G b a := by
  obtain ⟨v, hv⟩ := exists_unitPotential G hG a b
  refine ⟨summable_survProb G hG b a, summable_survProb G hG a b, ⟨v, hv⟩,
    fun hab => hitting_potential G hG hab, commuteTime_eq_of_potential G hG a b, ?_,
    add_comm _ _, effRes_comm G hG a b⟩
  rw [effRes_eq G hG hv]; exact commuteTime_eq_of_potential G hG a b v hv

end C3419
