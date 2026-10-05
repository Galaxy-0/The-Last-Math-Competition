import Mathlib

/-!
# Conjecture 00000003423: adding an edge can increase hitting times

For the simple random walk on a finite connected simple graph `G` and a target vertex `b`, the
expected hitting times `h(v) = E_v[τ_b]`, `τ_b = min {t ≥ 0 : X_t = b}`, are characterised by
first-step analysis as the unique solution of the linear system
`h(b) = 0`, `h(v) = 1 + (1/deg v) ∑_{u ~ v} h(u)` for `v ≠ b`.
We prove in general that on a connected finite graph this system has exactly one real solution
(maximum principle + finite-dimensional linear algebra), and define `hittingTime G a b` as the
value at `a` of that solution.

The conjecture claims (second clause) that adding edges decreases hitting time (submodularly).
Counterexample: the path `P₅ = 0 - 1 - 2 - 3 - 4` (Mathlib's `pathGraph 5`) and the graph
`P₅ + {0,2}` obtained by adding the single edge `{0,2}`. Then
`H_{P₅}(0 → 4) = 16` but `H_{P₅+{0,2}}(0 → 4) = 18`; moreover the maximal hitting time
`max_{a,b} H(a → b)` goes up from `16` to at least `18`.
-/

open Finset

noncomputable section

namespace C3423

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `h` solves the first-step (hitting-time) system of the simple random walk on `G` with
target `b`: `h b = 0` and `h v = 1 + (1/deg v) ∑_{u ~ v} h u` for `v ≠ b`. -/
def IsHittingTimeVec (G : SimpleGraph V) [DecidableRel G.Adj] (b : V) (h : V → ℝ) : Prop :=
  h b = 0 ∧ ∀ v, v ≠ b → h v = 1 + (∑ u ∈ G.neighborFinset v, h u) / G.degree v

/-- Maximum principle: a function vanishing at `b` and harmonic (mean-value property over
neighbours) off `b` on a connected graph is `≤ 0` everywhere. -/
theorem harmonic_le_zero (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected) (b : V)
    (f : V → ℝ) (hb : f b = 0)
    (hf : ∀ v, v ≠ b → f v = (∑ u ∈ G.neighborFinset v, f u) / G.degree v) (v : V) :
    f v ≤ 0 := by
  have : Nonempty V := ⟨b⟩
  obtain ⟨m, hm⟩ := Finite.exists_max f
  -- propagation: a maximiser `x ≠ b` has all neighbours maximisers
  have step : ∀ x y, G.Adj x y → x ≠ b → f x = f m → f y = f m := by
    intro x y hxy hxb hx
    have hdeg : (0 : ℝ) < G.degree x := by
      exact_mod_cast G.degree_pos_iff_exists_adj x |>.2 ⟨y, hxy⟩
    have hsum : ∑ u ∈ G.neighborFinset x, (f m - f u) = 0 := by
      rw [sum_sub_distrib, sum_const, G.card_neighborFinset_eq_degree, nsmul_eq_mul]
      have := hf x hxb
      rw [hx, eq_div_iff hdeg.ne'] at this
      linarith
    have hy : y ∈ G.neighborFinset x := (G.mem_neighborFinset x y).2 hxy
    have := (sum_eq_zero_iff_of_nonneg (fun u _ => sub_nonneg.2 (hm u))).1 hsum y hy
    linarith
  have reach : ∀ x z (p : G.Walk x z), z = b → f x = f m → f b = f m := by
    intro x z p
    induction p with
    | nil => intro hz hx; subst hz; exact hx
    | @cons x y z hxy p ih =>
      intro hz hx
      by_cases hxb : x = b
      · subst hxb; exact hx
      · exact ih hz (step x y hxy hxb hx)
  obtain ⟨p⟩ := hG.preconnected m b
  have := reach m b p rfl rfl
  linarith [hm v]

/-- Uniqueness: on a connected graph the hitting-time system has at most one solution. -/
theorem isHittingTimeVec_unique (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    {b : V} {h₁ h₂ : V → ℝ} (H₁ : IsHittingTimeVec G b h₁) (H₂ : IsHittingTimeVec G b h₂) :
    h₁ = h₂ := by
  have harm : ∀ g : V → ℝ, (g = fun v => h₁ v - h₂ v) ∨ (g = fun v => h₂ v - h₁ v) →
      ∀ v, g v ≤ 0 := by
    intro g hg
    apply harmonic_le_zero G hG b g
    · rcases hg with rfl | rfl <;> simp [H₁.1, H₂.1]
    · intro v hv
      rcases hg with rfl | rfl <;>
      · dsimp only; rw [H₁.2 v hv, H₂.2 v hv, sum_sub_distrib]; ring
  funext v
  linarith [harm _ (Or.inl rfl) v, harm _ (Or.inr rfl) v]

/-- Existence: on a connected graph the hitting-time system has a solution (the linear map
`h ↦ (h b, (h v - avg_{u~v} h u)_{v ≠ b})` is injective by uniqueness, hence surjective). -/
theorem exists_isHittingTimeVec (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (b : V) : ∃ h, IsHittingTimeVec G b h := by
  let L : (V → ℝ) →ₗ[ℝ] (V → ℝ) :=
    { toFun := fun h v => if v = b then h v else h v - (∑ u ∈ G.neighborFinset v, h u) / G.degree v
      map_add' := by
        intro h₁ h₂; funext v; by_cases hv : v = b <;> simp [hv, sum_add_distrib]; ring
      map_smul' := by
        intro c h; funext v; by_cases hv : v = b <;> simp [hv, ← mul_sum]; ring }
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro h hL
    have hval : ∀ v, L h v = 0 := fun v => by rw [hL]; rfl
    have hb : h b = 0 := by simpa [L] using hval b
    have hf : ∀ v, v ≠ b → h v = (∑ u ∈ G.neighborFinset v, h u) / G.degree v := by
      intro v hv; have := hval v; simp only [L, LinearMap.coe_mk, AddHom.coe_mk, hv,
        if_false] at this; linarith
    have hneg : ∀ v, v ≠ b → (-h) v = (∑ u ∈ G.neighborFinset v, (-h) u) / G.degree v := by
      intro v hv; simp only [Pi.neg_apply, sum_neg_distrib, neg_div, hf v hv]
    funext v
    have h1 := harmonic_le_zero G hG b h hb hf v
    have h2 := harmonic_le_zero G hG b (-h) (by simp [hb]) hneg v
    simp only [Pi.neg_apply] at h2
    simp only [Pi.zero_apply]; linarith
  obtain ⟨h, hh⟩ := (LinearMap.injective_iff_surjective.1 hinj) (fun v => if v = b then 0 else 1)
  refine ⟨h, ?_, ?_⟩
  · have := congrFun hh b; simpa [L] using this
  · intro v hv
    have := congrFun hh v
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk, hv, if_false] at this
    linarith

/-- The expected hitting time `H_G(a → b)` of the simple random walk on `G`: the value at `a`
of the (unique, on connected graphs) solution of the hitting-time system with target `b`. -/
def hittingTime (G : SimpleGraph V) [DecidableRel G.Adj] (a b : V) : ℝ :=
  Classical.epsilon (IsHittingTimeVec G b) a

theorem hittingTime_eq (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected) {b : V}
    {h : V → ℝ} (hh : IsHittingTimeVec G b h) (a : V) : hittingTime G a b = h a := by
  have hspec : IsHittingTimeVec G b (Classical.epsilon (IsHittingTimeVec G b)) :=
    Classical.epsilon_spec ⟨h, hh⟩
  rw [hittingTime, isHittingTimeVec_unique G hG hspec hh]

/-- `hittingTime` solves the hitting-time system on every connected graph. -/
theorem hittingTime_spec (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected) (b : V) :
    IsHittingTimeVec G b (fun a => hittingTime G a b) :=
  Classical.epsilon_spec (exists_isHittingTimeVec G hG b)

/-- The maximal hitting time `max_{a,b} H_G(a → b)`. -/
def maxHittingTime [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  (univ : Finset (V × V)).sup' univ_nonempty (fun p => hittingTime G p.1 p.2)

/-! ## The counterexample -/

/-- The path `P₅` (Mathlib's `pathGraph 5`), with a computable adjacency test. -/
instance : DecidableRel (SimpleGraph.pathGraph 5).Adj := fun u v =>
  decidable_of_iff (u.val + 1 = v.val ∨ v.val + 1 = u.val) SimpleGraph.pathGraph_adj.symm

/-- `P₅` with the single edge `{0,2}` added. -/
def P5chord : SimpleGraph (Fin 5) := SimpleGraph.pathGraph 5 ⊔ SimpleGraph.edge 0 2

instance : DecidableRel P5chord.Adj := fun u v =>
  decidable_of_iff (u.val + 1 = v.val ∨ v.val + 1 = u.val ∨ (u = 0 ∧ v = 2) ∨ (u = 2 ∧ v = 0)) (by
    simp only [P5chord, SimpleGraph.sup_adj, SimpleGraph.pathGraph_adj, SimpleGraph.edge_adj]
    fin_cases u <;> fin_cases v <;> decide)

theorem P5_connected : (SimpleGraph.pathGraph 5).Connected := SimpleGraph.pathGraph_connected 4

theorem P5_le_P5chord : SimpleGraph.pathGraph 5 ≤ P5chord := le_sup_left

theorem P5chord_connected : P5chord.Connected := P5_connected.mono P5_le_P5chord

theorem nbr_P5 (v : Fin 5) : (SimpleGraph.pathGraph 5).neighborFinset v =
    ![{1}, {0, 2}, {1, 3}, {2, 4}, {3}] v := by
  fin_cases v <;> decide

theorem nbr_P5chord (v : Fin 5) : P5chord.neighborFinset v =
    ![{1, 2}, {0, 2}, {0, 1, 3}, {2, 4}, {3}] v := by
  fin_cases v <;> decide

/-- Evaluate a first-step equation over an explicit neighbour set in `Fin 5`. -/
macro "eval5" : tactic => `(tactic| (
  repeat rw [Finset.sum_insert (by decide)]
  try rw [Finset.sum_singleton]
  repeat rw [Finset.card_insert_of_notMem (by decide)]
  try rw [Finset.card_singleton]
  (try simp only [Matrix.cons_val]) <;> norm_num))

/-- Explicit hitting-time vectors on `P₅`: target `j`, start `i`. -/
def hP5 : Fin 5 → Fin 5 → ℝ :=
  ![![0, 7, 12, 15, 16], ![1, 0, 5, 8, 9], ![4, 3, 0, 3, 4], ![9, 8, 5, 0, 1],
    ![16, 15, 12, 7, 0]]

theorem hP5_spec (b : Fin 5) : IsHittingTimeVec (SimpleGraph.pathGraph 5) b (hP5 b) := by
  refine ⟨by fin_cases b <;> rfl, fun v hv => ?_⟩
  rw [← SimpleGraph.card_neighborFinset_eq_degree, nbr_P5]
  fin_cases b <;> fin_cases v <;> first | exact absurd rfl hv | (norm_num [hP5] <;> eval5)

/-- Explicit hitting-time vector on `P₅ + {0,2}` with target `4`. -/
def hChord : Fin 5 → ℝ := ![18, 18, 16, 9, 0]

theorem hChord_spec : IsHittingTimeVec P5chord 4 hChord := by
  refine ⟨rfl, fun v hv => ?_⟩
  rw [← SimpleGraph.card_neighborFinset_eq_degree, nbr_P5chord]
  fin_cases v <;> first | exact absurd rfl hv | (norm_num [hChord]; eval5)

theorem hittingTime_P5 (a b : Fin 5) : hittingTime (SimpleGraph.pathGraph 5) a b = hP5 b a :=
  hittingTime_eq _ P5_connected (hP5_spec b) a

theorem hittingTime_P5_0_4 : hittingTime (SimpleGraph.pathGraph 5) 0 4 = 16 := by
  rw [hittingTime_P5]; rfl

theorem hittingTime_P5chord_0_4 : hittingTime P5chord 0 4 = 18 := by
  rw [hittingTime_eq _ P5chord_connected hChord_spec]; rfl

theorem maxHittingTime_P5 : maxHittingTime (SimpleGraph.pathGraph 5) = 16 := by
  apply le_antisymm
  · refine sup'_le _ _ fun p _ => ?_
    rw [hittingTime_P5]
    rcases p with ⟨a, b⟩
    fin_cases a <;> fin_cases b <;> simp [hP5] <;> norm_num
  · rw [← hittingTime_P5_0_4]
    exact le_sup' (fun p : Fin 5 × Fin 5 => hittingTime _ p.1 p.2) (mem_univ ((0 : Fin 5), 4))

theorem maxHittingTime_P5chord_ge : 18 ≤ maxHittingTime P5chord := by
  rw [← hittingTime_P5chord_0_4]
  exact le_sup' (fun p : Fin 5 × Fin 5 => hittingTime _ p.1 p.2) (mem_univ ((0 : Fin 5), 4))

/-- **Counterexample.** Adding the single edge `{0,2}` to the connected path `P₅` raises the
hitting time `H(0 → 4)` from `16` to `18`, and the maximal hitting time from `16` to `≥ 18`. -/
theorem adding_edge_increases_hittingTime :
    SimpleGraph.pathGraph 5 ≤ P5chord ∧ P5chord = SimpleGraph.pathGraph 5 ⊔ SimpleGraph.edge 0 2 ∧
      (SimpleGraph.pathGraph 5).Connected ∧
      hittingTime (SimpleGraph.pathGraph 5) 0 4 = 16 ∧ hittingTime P5chord 0 4 = 18 ∧
      maxHittingTime (SimpleGraph.pathGraph 5) = 16 ∧ 18 ≤ maxHittingTime P5chord :=
  ⟨P5_le_P5chord, rfl, P5_connected, hittingTime_P5_0_4, hittingTime_P5chord_0_4,
    maxHittingTime_P5, maxHittingTime_P5chord_ge⟩

/-- **Main theorem (pairwise reading).** It is false that adding edges to a connected graph
never increases a hitting time `H(a → b)`. -/
theorem not_edge_monotone_hittingTime :
    ¬ ∀ (G G' : SimpleGraph (Fin 5)) [DecidableRel G.Adj] [DecidableRel G'.Adj],
      G.Connected → G ≤ G' → ∀ a b, hittingTime G' a b ≤ hittingTime G a b := by
  intro h
  have := h (SimpleGraph.pathGraph 5) P5chord P5_connected P5_le_P5chord 0 4
  rw [hittingTime_P5_0_4, hittingTime_P5chord_0_4] at this
  norm_num at this

/-- **Main theorem (maximal-hitting-time reading).** It is false that adding edges to a
connected graph never increases the maximal hitting time `max_{a,b} H(a → b)`. -/
theorem not_edge_monotone_maxHittingTime :
    ¬ ∀ (G G' : SimpleGraph (Fin 5)) [DecidableRel G.Adj] [DecidableRel G'.Adj],
      G.Connected → G ≤ G' → maxHittingTime G' ≤ maxHittingTime G := by
  intro h
  have := h (SimpleGraph.pathGraph 5) P5chord P5_connected P5_le_P5chord
  rw [maxHittingTime_P5] at this
  linarith [maxHittingTime_P5chord_ge]

end C3423
