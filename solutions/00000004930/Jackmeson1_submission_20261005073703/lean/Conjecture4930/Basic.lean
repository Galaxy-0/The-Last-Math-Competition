import Mathlib

/-!
# Conjecture 00000004930

Discounted value and average reward are two layers of optimality measures. Conjecture: there
exist two MDPs with identical values for all discount factors but different average rewards, and
the separation is realized by an explicit construction concentrating the discount weights on
transients.

We formalize MDPs with arbitrary state and action types, stochastic transitions `P : S → A → PMF S`
and nonnegative rewards, and *history-dependent randomized* policies
`π : (past state-action pairs, current state) → PMF A`. The law of the history at time `t` is
built by the usual recursion, `expReward M π t` is the expected reward at time `t`,
`discValue M π β = ∑ₜ βᵗ E[r_t]`, `optValue M β = sup_π discValue M π β`, and
`avgReward M π T = (1/T) ∑_{t<T} E[r_t]` is the `T`-step average (computed with `toReal`, so it
matches the usual average when the expected rewards are finite, e.g. for bounded rewards; the
witnesses have rewards in `{0, 1}`). In `ℝ≥0∞`, `(1 - β)⁻¹` uses truncated subtraction: it is
`1/(1-β)` for `β < 1` and `∞` for `β ≥ 1`.

* `A`: one state, one action, reward `1`.
* `B`: a start state from which action `n ∈ ℕ` leads to a countdown `n, n-1, …, 0` and then to an
  absorbing sink; reward `1` off the sink and `0` on it. All reward is collected on transient
  states.

Main theorem `conjecture4930`: `optValue A β = optValue B β = (1-β)⁻¹` for every `β`, while under
every policy the average reward of `A` tends to `1` and that of `B` tends to `0`.
-/

namespace Conjecture4930

open Filter Topology ENNReal NNReal Finset

/-- A Markov decision process with initial state `s₀`, stochastic transitions and nonnegative
rewards. -/
structure MDP where
  S : Type
  Act : Type
  s₀ : S
  P : S → Act → PMF S
  r : S → Act → ℝ≥0

/-- A history: past state-action pairs and the current state. -/
abbrev Hist (M : MDP) := List (M.S × M.Act) × M.S

/-- History-dependent randomized policies. -/
abbrev Policy (M : MDP) := Hist M → PMF M.Act

/-- The law of the history at time `t`. -/
noncomputable def law (M : MDP) (π : Policy M) : ℕ → PMF (Hist M)
  | 0 => PMF.pure ([], M.s₀)
  | t + 1 => (law M π t).bind fun h => (π h).bind fun a =>
      (M.P h.2 a).map fun s => (h.1 ++ [(h.2, a)], s)

/-- Expected reward at time `t`. -/
noncomputable def expReward (M : MDP) (π : Policy M) (t : ℕ) : ℝ≥0∞ :=
  ∑' h, law M π t h * ∑' a, π h a * (M.r h.2 a : ℝ≥0∞)

/-- Discounted value of a policy. -/
noncomputable def discValue (M : MDP) (π : Policy M) (β : ℝ≥0∞) : ℝ≥0∞ :=
  ∑' t, β ^ t * expReward M π t

/-- Optimal discounted value (value of the MDP at its initial state). -/
noncomputable def optValue (M : MDP) (β : ℝ≥0∞) : ℝ≥0∞ := ⨆ π : Policy M, discValue M π β

/-- `T`-step average reward; the average reward of `π` is its limit as `T → ∞`. Each expected
reward is converted with `toReal` (which sends `∞` to `0`), so this is the usual average when the
expected rewards are finite, e.g. for bounded rewards. -/
noncomputable def avgReward (M : MDP) (π : Policy M) (T : ℕ) : ℝ :=
  (T : ℝ)⁻¹ * ∑ t ∈ range T, (expReward M π t).toReal

lemma expReward_le_one (M : MDP) (hr : ∀ s a, M.r s a ≤ 1) (π : Policy M) (t : ℕ) :
    expReward M π t ≤ 1 := by
  calc expReward M π t ≤ ∑' h, law M π t h * ∑' a, π h a * 1 := by
        refine ENNReal.tsum_le_tsum fun h => mul_le_mul_right ?_ _
        refine ENNReal.tsum_le_tsum fun a => mul_le_mul_right ?_ _
        exact_mod_cast hr _ _
    _ = 1 := by simp [PMF.tsum_coe]

lemma expReward_eq_one (M : MDP) (hr : ∀ s a, M.r s a = 1) (π : Policy M) (t : ℕ) :
    expReward M π t = 1 := by
  simp [expReward, hr, PMF.tsum_coe]

/-! ## The first MDP: constant reward 1 -/

/-- `A`: one state, one action, reward `1`. -/
noncomputable abbrev A : MDP where
  S := Unit
  Act := Unit
  s₀ := ()
  P := fun _ _ => PMF.pure ()
  r := fun _ _ => 1

lemma optValue_A (β : ℝ≥0∞) : optValue A β = (1 - β)⁻¹ := by
  have hv : ∀ π : Policy A, discValue A π β = (1 - β)⁻¹ := fun π => by
    simp [discValue, expReward_eq_one A (fun _ _ => rfl), ENNReal.tsum_geometric]
  have hne : Nonempty (Policy A) := ⟨fun _ => PMF.pure ()⟩
  simp only [optValue, hv, ciSup_const]

lemma avgReward_A (π : Policy A) : Tendsto (avgReward A π) atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ne_atTop 0] with T hT
  have hT' : (T : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hT
  simp [avgReward, expReward_eq_one A (fun _ _ => rfl), hT']

/-! ## The second MDP: a countdown of chosen length, then an absorbing sink -/

/-- States of `B`. -/
inductive BS
  | start
  | count (k : ℕ)
  | sink
  deriving DecidableEq

/-- Deterministic transitions of `B`; the action matters only at `start`. -/
def next : BS → ℕ → BS
  | .start, n => .count n
  | .count (k + 1), _ => .count k
  | .count 0, _ => .sink
  | .sink, _ => .sink

/-- `B`: from `start`, action `n` enters the countdown of length `n + 1`; reward `1` off the sink. -/
noncomputable abbrev B : MDP where
  S := BS
  Act := ℕ
  s₀ := .start
  P := fun s a => PMF.pure (next s a)
  r := fun s _ => if s = .sink then 0 else 1

lemma B_r_le (s : BS) (a : ℕ) : B.r s a ≤ 1 := by
  show (if s = .sink then 0 else 1 : ℝ≥0) ≤ 1
  split_ifs <;> simp

lemma next_indep {s : BS} (hs : s ≠ .start) (a b : ℕ) : next s a = next s b := by
  rcases s with _ | (_ | k) | _ <;> simp_all [next]

/-- The state at time `t` when action `n` is always played. -/
def st (n : ℕ) : ℕ → BS
  | 0 => .start
  | t + 1 => next (st n t) n

lemma st_succ_le (n k : ℕ) (hk : k ≤ n) : st n (k + 1) = .count (n - k) := by
  induction k with
  | zero => simp [st, next]
  | succ k ih =>
    rw [st, ih (by omega)]
    obtain ⟨m, hm⟩ : ∃ m, n - k = m + 1 := ⟨n - k - 1, by omega⟩
    rw [hm, next]
    congr 1; omega

lemma st_ne_start (n t : ℕ) (ht : t ≠ 0) : st n t ≠ .start := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht
  induction t with
  | zero => simp [st, next]
  | succ t ih =>
    have h := ih (by omega)
    rw [st]
    rcases hst : st n (t + 1) with _ | (_ | k) | _ <;> simp_all [next]

lemma st_sink (n t : ℕ) (ht : n + 2 ≤ t) : st n t = .sink := by
  induction t with
  | zero => omega
  | succ t ih =>
    rcases Nat.lt_or_ge t (n + 2) with h | h
    · have : t = n + 1 := by omega
      subst this
      rw [st, st_succ_le n n le_rfl, Nat.sub_self, next]
    · rw [st, ih h, next]

/-- The deterministic policy that always plays `n`. -/
noncomputable def detPol (n : ℕ) : Policy B := fun _ => PMF.pure n

lemma law_detPol (n t : ℕ) : ∃ h, law B (detPol n) t = PMF.pure h ∧ h.2 = st n t := by
  induction t with
  | zero => exact ⟨([], .start), rfl, rfl⟩
  | succ t ih =>
    obtain ⟨h, hl, hs⟩ := ih
    refine ⟨(h.1 ++ [(h.2, n)], next h.2 n), ?_, ?_⟩
    · simp [law, hl, detPol, B, PMF.pure_bind, PMF.pure_map]
    · simp [st, hs]

lemma expReward_detPol (n t : ℕ) (ht : t ≤ n + 1) : expReward B (detPol n) t = 1 := by
  obtain ⟨h, hl, hs⟩ := law_detPol n t
  have hne : st n t ≠ .sink := by
    rcases t with _ | t
    · simp [st]
    · rw [st_succ_le n t (by omega)]; simp
  simp [expReward, hl, detPol, B, hs, hne]

lemma optValue_B (β : ℝ≥0∞) : optValue B β = (1 - β)⁻¹ := by
  apply le_antisymm
  · refine iSup_le fun π => ?_
    rw [← ENNReal.tsum_geometric]
    refine ENNReal.tsum_le_tsum fun t => ?_
    calc β ^ t * expReward B π t ≤ β ^ t * 1 :=
          mul_le_mul_right (expReward_le_one B B_r_le π t) _
      _ = β ^ t := mul_one _
  · rw [← ENNReal.tsum_geometric, ENNReal.tsum_eq_iSup_nat]
    refine iSup_le fun n => ?_
    refine le_trans ?_ (le_iSup _ (detPol n))
    calc ∑ t ∈ range n, β ^ t = ∑ t ∈ range n, β ^ t * expReward B (detPol n) t := by
          refine Finset.sum_congr rfl fun t ht => ?_
          rw [expReward_detPol n t (by simp at ht; omega), mul_one]
      _ ≤ discValue B (detPol n) β := ENNReal.sum_le_tsum _

lemma bind_congr_support {α β : Type*} (p : PMF α) (f g : α → PMF β)
    (hfg : ∀ a ∈ p.support, f a = g a) : p.bind f = p.bind g := by
  ext b
  simp only [PMF.bind_apply]
  refine tsum_congr fun a => ?_
  by_cases ha : p a = 0
  · simp [ha]
  · rw [hfg a ((PMF.mem_support_iff p a).mpr ha)]

/-- Key invariant: for `t ≥ 1`, the state at time `t` is `st n t` with `n` the first action, whatever
the (randomized, history-dependent) policy does later. -/
lemma law_state (π : Policy B) (t : ℕ) (ht : t ≠ 0) :
    (law B π t).map Prod.snd = (π ([], .start)).map fun n => st n t := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht
  induction t with
  | zero =>
    simp only [law, PMF.pure_bind, PMF.map_bind, B, PMF.pure_map]
    rfl
  | succ t ih =>
    have ih := ih (by omega)
    have hsupp : ∀ h ∈ (law B π (t + 1)).support, h.2 ≠ .start := by
      intro h hh
      have : h.2 ∈ ((law B π (t + 1)).map Prod.snd).support :=
        (PMF.mem_support_map_iff _ _ _).mpr ⟨h, hh, rfl⟩
      rw [ih, PMF.mem_support_map_iff] at this
      obtain ⟨n, -, hn⟩ := this
      rw [← hn]
      exact st_ne_start n (t + 1) (by omega)
    calc (law B π (t + 1 + 1)).map Prod.snd
        = (law B π (t + 1)).bind fun h => (π h).bind fun a => PMF.pure (next h.2 a) := by
          simp only [law, PMF.map_bind, B, PMF.pure_map]
      _ = (law B π (t + 1)).bind fun h => PMF.pure (next h.2 0) := by
          refine bind_congr_support _ _ _ fun h hh => ?_
          simp_rw [next_indep (hsupp h hh) _ 0]
          exact PMF.bind_const _ _
      _ = ((law B π (t + 1)).map Prod.snd).map fun s => next s 0 := by
          rw [PMF.map_comp]; rfl
      _ = (π ([], .start)).map fun n => st n (t + 1 + 1) := by
          rw [ih, PMF.map_comp]
          congr 1
          funext n
          simp only [Function.comp, st]
          exact next_indep (st_ne_start n (t + 1) (by omega)) 0 n

lemma expReward_B_le (π : Policy B) (t : ℕ) :
    expReward B π (t + 1) ≤ ∑' k, π ([], .start) (k + t) := by
  set q := π ([], .start)
  have h1 : expReward B π (t + 1) =
      (law B π (t + 1)).toOuterMeasure (Prod.snd ⁻¹' {s | s ≠ .sink}) := by
    rw [PMF.toOuterMeasure_apply, expReward]
    refine tsum_congr fun h => ?_
    by_cases hs : h.2 = .sink
    · simp [B, hs]
    · simp [B, hs, Set.indicator, PMF.tsum_coe]
  rw [h1, ← PMF.toOuterMeasure_map_apply, law_state π (t + 1) (by omega),
    PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply]
  have hind : ∀ n, (((fun n => st n (t + 1)) ⁻¹' {s | s ≠ .sink}).indicator q n) =
      if t ≤ n then (if n < t then 0 else q n) else 0 := by
    intro n
    by_cases hn : t ≤ n
    · simp [Set.indicator, hn, not_lt.mpr hn]
      intro h; exact absurd h (by rw [st_succ_le n t hn]; simp)
    · simp [Set.indicator, hn, st_sink n (t + 1) (by omega)]
  calc ∑' n, ((fun n => st n (t + 1)) ⁻¹' {s | s ≠ .sink}).indicator q n
      ≤ ∑' n, (if n < t then 0 else q n) := by
        refine ENNReal.tsum_le_tsum fun n => ?_
        rw [hind n]; split_ifs <;> simp
    _ = ∑' k, q (k + t) := by
        rw [← Summable.sum_add_tsum_nat_add' (f := fun n => if n < t then (0 : ℝ≥0∞) else q n)
          (k := t) ENNReal.summable]
        have h0 : ∑ x ∈ range t, (if x < t then (0 : ℝ≥0∞) else q x) = 0 :=
          Finset.sum_eq_zero fun x hx => if_pos (Finset.mem_range.mp hx)
        rw [h0, zero_add]
        simp

lemma expReward_B_tendsto (π : Policy B) : Tendsto (expReward B π) atTop (𝓝 0) := by
  have htail := ENNReal.tendsto_sum_nat_add (fun k => π ([], .start) k)
    (by rw [PMF.tsum_coe]; exact one_ne_top)
  rw [← tendsto_add_atTop_iff_nat 1]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htail
    (fun _ => bot_le) (fun t => expReward_B_le π t)

lemma avgReward_B (π : Policy B) : Tendsto (avgReward B π) atTop (𝓝 0) := by
  have h := (ENNReal.tendsto_toReal zero_ne_top).comp (expReward_B_tendsto π)
  exact h.cesaro

/-- **Main theorem.** `A` and `B` have identical optimal discounted values for every discount
factor `β` (both equal `(1-β)⁻¹`), but under every history-dependent randomized policy the average
reward of `A` tends to `1` while that of `B` tends to `0`. In `B` the expected reward at time `t`
tends to `0` under every policy: all reward sits on the transient countdown states. -/
theorem conjecture4930 :
    (∀ β : ℝ≥0∞, optValue A β = optValue B β) ∧
    (∀ β : ℝ≥0∞, optValue A β = (1 - β)⁻¹) ∧
    (∀ π : Policy A, Tendsto (avgReward A π) atTop (𝓝 1)) ∧
    (∀ π : Policy B, Tendsto (avgReward B π) atTop (𝓝 0)) ∧
    (∀ π : Policy B, Tendsto (expReward B π) atTop (𝓝 0)) :=
  ⟨fun β => by rw [optValue_A, optValue_B], optValue_A, avgReward_A, avgReward_B,
    expReward_B_tendsto⟩

end Conjecture4930
