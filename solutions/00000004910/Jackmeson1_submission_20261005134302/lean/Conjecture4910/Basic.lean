import Mathlib

/-!
# Conjecture 00000004910

The optimal policy and the transition structure are two layers of model data. Conjecture: there
exist two MDPs with identical optimal policies and value functions but different transition
structures, and the separation is realized by an explicit construction merging redundant actions.

MDP framework adapted from the package for conjecture 00000004930: MDPs with stochastic
transitions `P : S → A → PMF S`, nonnegative rewards, and *history-dependent randomized* policies
`π : (past state-action pairs, current state) → PMF A`. Here the start state `s` is a parameter,
`discValue M π s β = ∑ₜ βᵗ E[r_t]`, the value function is `s ↦ optValue M s β = sup_π discValue`,
and `π` is optimal when it attains `optValue M s β` at every state `s`. Values live in `[0, ∞]`.

**Merging redundant actions.** Let `q : A → B` be onto with a section `g` (`q ∘ g = id`) such that
the actions in each fibre of `q` are duplicates (same transition law and reward at every state).
`quot M g` is the MDP with action type `B` in which each fibre is one action. A policy `π` of `M`
is sent to `push M q g π`, which plays at a merged history the conditional law of the merged
action given that merged history. Main facts, for every MDP and every `β`:
* `law_push`: the merged history process of `π` in `M` has the law of `push π` in `quot M g`;
* `discValue_push`, `discValue_lift`, `push_lift`: values are preserved, and `push` is onto;
* `optValue_quot`, `isOptimal_push`, `isOptimal_lift`: equal value functions, and the optimal
  policies of `M` are exactly the `push`-preimage of those of `quot M g`, which are exactly the
  `push`-images of those of `M`.

Witness: `M₂` (states `Bool`, actions `opt, red₁, red₂`), reward `1` for `opt` and `0` otherwise;
`opt` stays put, `red₁` and `red₂` both move to the other state. `M₃ = quot M₂ rep` (actions
`opt, red`). The kernel of `M₂` is not injective in the action; that of `M₃` is.
-/

namespace Conjecture4910

open ENNReal NNReal

/-- A Markov decision process: stochastic transitions and nonnegative rewards. -/
structure MDP (S A : Type) where
  P : S → A → PMF S
  r : S → A → ℝ≥0

variable {S A B : Type}

/-- A history: past state-action pairs and the current state. -/
abbrev Hist (S A : Type) := List (S × A) × S

/-- History-dependent randomized policies. -/
abbrev Policy (S A : Type) := Hist S A → PMF A

/-- The law of the history at time `t`, started at state `s`. -/
noncomputable def law (M : MDP S A) (π : Policy S A) (s : S) : ℕ → PMF (Hist S A)
  | 0 => PMF.pure ([], s)
  | t + 1 => (law M π s t).bind fun h => (π h).bind fun a =>
      (M.P h.2 a).map fun s' => (h.1 ++ [(h.2, a)], s')

/-- Expected reward at time `t`. -/
noncomputable def expReward (M : MDP S A) (π : Policy S A) (s : S) (t : ℕ) : ℝ≥0∞ :=
  ∑' h, law M π s t h * ∑' a, π h a * (M.r h.2 a : ℝ≥0∞)

/-- Discounted value of a policy from start state `s`. -/
noncomputable def discValue (M : MDP S A) (π : Policy S A) (s : S) (β : ℝ≥0∞) : ℝ≥0∞ :=
  ∑' t, β ^ t * expReward M π s t

/-- The optimal value function `V*(s) = sup_π discValue`. -/
noncomputable def optValue (M : MDP S A) (s : S) (β : ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ π : Policy S A, discValue M π s β

/-- `π` is optimal: it attains the optimal value at every state. -/
def IsOptimal (M : MDP S A) (β : ℝ≥0∞) (π : Policy S A) : Prop :=
  ∀ s, discValue M π s β = optValue M s β

/-- The policy that always plays `o`. -/
noncomputable def constPol (o : A) : Policy S A := fun _ => PMF.pure o

lemma avg_le_one {α : Type} (p : PMF α) (g : α → ℝ≥0∞) (hg : ∀ x, g x ≤ 1) :
    ∑' x, p x * g x ≤ 1 :=
  (ENNReal.tsum_le_tsum fun x => mul_le_mul_right (hg x) _).trans (by simp [PMF.tsum_coe])

lemma expReward_le_one (M : MDP S A) (hr : ∀ s a, M.r s a ≤ 1) (π : Policy S A) (s : S)
    (t : ℕ) : expReward M π s t ≤ 1 :=
  avg_le_one _ _ fun h => avg_le_one _ _ fun a => by exact_mod_cast hr _ _

lemma expReward_const (M : MDP S A) (o : A) (ho : ∀ s, M.r s o = 1) (s : S) (t : ℕ) :
    expReward M (constPol o) s t = 1 := by
  simp [expReward, constPol, ho, PMF.tsum_coe]

/-- `V*(s) = (1 - β)⁻¹` at every state (truncated subtraction in `[0,∞]`: this is `1/(1-β)` for
`β < 1` and `∞` for `β ≥ 1`), attained by `constPol o`. -/
lemma optValue_eq (M : MDP S A) (hr : ∀ s a, M.r s a ≤ 1) (o : A) (ho : ∀ s, M.r s o = 1)
    (s : S) (β : ℝ≥0∞) : optValue M s β = (1 - β)⁻¹ := by
  apply le_antisymm
  · refine iSup_le fun π => ?_
    rw [← ENNReal.tsum_geometric]
    exact ENNReal.tsum_le_tsum fun t =>
      (mul_le_mul_right (expReward_le_one M hr π s t) _).trans (mul_one _).le
  · refine le_trans ?_ (le_iSup _ (constPol o))
    simp [discValue, expReward_const M o ho, ENNReal.tsum_geometric]

lemma constPol_optimal (M : MDP S A) (hr : ∀ s a, M.r s a ≤ 1) (o : A) (ho : ∀ s, M.r s o = 1)
    (β : ℝ≥0∞) : IsOptimal M β (constPol o) := fun s => by
  rw [optValue_eq M hr o ho]; simp [discValue, expReward_const M o ho, ENNReal.tsum_geometric]

/-! ## Expectations of `PMF` constructions -/

lemma tsum_map_mul {α γ : Type} (q : PMF α) (g : α → γ) (φ : γ → ℝ≥0∞) :
    ∑' c, q.map g c * φ c = ∑' a, q a * φ (g a) := by
  simp_rw [PMF.map_apply, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun a => ?_
  simp [ite_mul]

lemma tsum_bind_mul {α γ : Type} (p : PMF α) (f : α → PMF γ) (φ : γ → ℝ≥0∞) :
    ∑' c, p.bind f c * φ c = ∑' a, p a * ∑' c, f a c * φ c := by
  simp_rw [PMF.bind_apply, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left, mul_assoc]
  exact ENNReal.tsum_comm

lemma tsum_pair {X Y : Type} (ν : PMF (X × Y)) (x : X) : ∑' y, ν (x, y) = ν.map Prod.fst x := by
  rw [PMF.map_apply, ENNReal.tsum_prod', tsum_eq_single x fun x' hx' => by simp [Ne.symm hx']]
  simp

lemma bind_pair_apply {X Y : Type} (m : PMF X) (k : X → PMF Y) (x : X) (y : Y) :
    (m.bind fun x' => (k x').map fun b => (x', b)) (x, y) = m x * k x y := by
  classical
  have hk : ∀ x', (k x').map (fun b => (x', b)) (x, y) = if x = x' then k x' y else 0 := by
    intro x'
    rw [PMF.map_apply, tsum_eq_single y fun b hb => by simp [Ne.symm hb]]
    by_cases h : x = x' <;> simp [h]
  simp only [PMF.bind_apply, hk, mul_ite, mul_zero]
  rw [tsum_eq_single x fun x' hx' => if_neg (Ne.symm hx'), if_pos rfl]

/-! ## Merging duplicate actions -/

/-- The MDP on the merged action type `B`, each class acting through its representative `g b`. -/
noncomputable def quot (M : MDP S A) (g : B → A) : MDP S B :=
  ⟨fun s b => M.P s (g b), fun s b => M.r s (g b)⟩

/-- Push a history through the merge map `f`. -/
def histMap (f : A → B) (h : Hist S A) : Hist S B := (h.1.map (Prod.map id f), h.2)

/-- Lift of a policy of the merged MDP: look at the merged history, play the representative. -/
noncomputable def lift (f : A → B) (g : B → A) (π : Policy S B) : Policy S A :=
  fun h => (π (histMap f h)).map g

/-- The start state of a history. -/
def start : Hist S A → S
  | ([], s) => s
  | (x :: _, _) => x.1

lemma law_support (M : MDP S A) (π : Policy S A) (s : S) (t : ℕ) (h : Hist S A)
    (hh : h ∈ (law M π s t).support) : start h = s ∧ h.1.length = t := by
  induction t generalizing h with
  | zero => simp [law] at hh; subst hh; simp [start]
  | succ t ih =>
    simp only [law, PMF.mem_support_bind_iff, PMF.support_map, Set.mem_image] at hh
    obtain ⟨h0, h0s, a, -, s', -, rfl⟩ := hh
    obtain ⟨h1, h2⟩ := ih h0 h0s
    refine ⟨?_, by simp [h2]⟩
    rcases h0 with ⟨_ | ⟨x, l⟩, c⟩ <;> simpa [start] using h1

/-- Joint law at time `t` of the merged history and the merged action. -/
noncomputable def joint (M : MDP S A) (q : A → B) (π : Policy S A) (s : S) (t : ℕ) :
    PMF (Hist S B × B) :=
  (law M π s t).bind fun h => (π h).map fun a => (histMap q h, q a)

lemma joint_fst (M : MDP S A) (q : A → B) (π : Policy S A) (s : S) (t : ℕ) :
    (joint M q π s t).map Prod.fst = (law M π s t).map (histMap q) := by
  rw [joint, PMF.map_bind, ← PMF.bind_pure_comp]
  congr 1; funext h
  rw [PMF.map_comp]; exact PMF.map_const _ _

lemma tsum_pair_ne_top {X Y : Type} (ν : PMF (X × Y)) (x : X) : ∑' y, ν (x, y) ≠ ∞ := by
  rw [tsum_pair]; exact PMF.apply_ne_top _ _

/-- **Pushforward of a policy along the merge map.** At a merged history `h'`, play the
conditional law of the merged action given the merged history `h'`, computed from the start state
and at the time recorded in `h'`; at merged histories of probability zero, play the merged image
of the action law at the representative history. -/
noncomputable def push (M : MDP S A) (q : A → B) (g : B → A) (π : Policy S A) : Policy S B :=
  fun h' => if h0 : ∑' b, joint M q π (start h') h'.1.length (h', b) = 0
    then (π (histMap g h')).map q
    else PMF.normalize _ h0 (tsum_pair_ne_top _ _)

/-- Disintegration: the joint law is the merged history law followed by `push π`. -/
lemma joint_eq (M : MDP S A) (q : A → B) (g : B → A) (π : Policy S A) (s : S) (t : ℕ) :
    joint M q π s t = ((law M π s t).map (histMap q)).bind
      fun h' => (push M q g π h').map fun b => (h', b) := by
  ext ⟨x, y⟩
  rw [bind_pair_apply]
  have hm := tsum_pair (joint M q π s t) x
  rw [joint_fst] at hm
  by_cases h0 : (law M π s t).map (histMap q) x = 0
  · rw [h0, zero_mul]
    exact nonpos_iff_eq_zero.1 ((ENNReal.le_tsum (f := fun b => joint M q π s t (x, b)) y).trans
      (hm.trans h0).le)
  · have hx : x ∈ histMap q '' (law M π s t).support :=
      PMF.support_map _ _ ▸ (PMF.mem_support_iff _ _).2 h0
    obtain ⟨h, hh, rfl⟩ := hx
    obtain ⟨h1, h2⟩ := law_support M π s t h hh
    have e1 : start (histMap q h) = s := by rcases h with ⟨_ | _, _⟩ <;> exact h1
    have e2 : (histMap q h).1.length = t := by simp [histMap, h2]
    have hne : ∑' b, joint M q π (start (histMap q h)) (histMap q h).1.length (histMap q h, b) ≠ 0
      := by rw [e1, e2, hm]; exact h0
    simp only [push, dif_neg hne, PMF.normalize_apply]
    rw [e1, e2, hm, mul_left_comm, ENNReal.mul_inv_cancel h0 (PMF.apply_ne_top _ _), mul_one]

/-- The merged history process of `π` in `M` is the history process of `push π` in `quot M g`. -/
lemma law_push (M : MDP S A) (q : A → B) (g : B → A) (hP : ∀ s a, M.P s (g (q a)) = M.P s a)
    (π : Policy S A) (s : S) (t : ℕ) :
    law (quot M g) (push M q g π) s t = (law M π s t).map (histMap q) := by
  induction t with
  | zero => simp [law, PMF.pure_map, histMap]
  | succ t ih =>
    rw [law, ih]
    calc _ = (joint M q π s t).bind fun p =>
          ((quot M g).P p.1.2 p.2).map fun s' => (p.1.1 ++ [(p.1.2, p.2)], s') := by
            rw [joint_eq M q g, PMF.bind_bind]; congr 1; funext h'; rw [PMF.bind_map]; rfl
      _ = _ := by
            rw [joint, PMF.bind_bind, law, PMF.map_bind]; congr 1; funext h
            rw [PMF.bind_map, PMF.map_bind]; congr 1; funext a
            simp [quot, hP, PMF.map_comp, histMap, Function.comp_def]

lemma discValue_push (M : MDP S A) (q : A → B) (g : B → A)
    (hP : ∀ s a, M.P s (g (q a)) = M.P s a) (hr : ∀ s a, M.r s (g (q a)) = M.r s a)
    (π : Policy S A) (s : S) (β : ℝ≥0∞) :
    discValue (quot M g) (push M q g π) s β = discValue M π s β := by
  refine tsum_congr fun t => ?_
  have key := congrArg (fun ν => ∑' p, ν p * (M.r p.1.2 (g p.2) : ℝ≥0∞)) (joint_eq M q g π s t)
  rw [expReward, expReward, law_push M q g hP π]
  simp only [joint, tsum_bind_mul, tsum_map_mul, histMap, hr, quot] at key ⊢
  rw [← key]

lemma law_lift (M : MDP S A) (f : A → B) (g : B → A) (hfg : ∀ b, f (g b) = b)
    (π : Policy S B) (s : S) (t : ℕ) :
    (law M (lift f g π) s t).map (histMap f) = law (quot M g) π s t := by
  induction t with
  | zero => simp [law, PMF.pure_map, histMap]
  | succ t ih =>
    rw [law, law, ← ih, PMF.map_bind, PMF.bind_map]
    congr 1; funext h
    simp only [Function.comp, lift, PMF.bind_map, PMF.map_bind, PMF.map_comp]
    congr 1; funext b
    simp [quot, histMap, hfg, Function.comp_def]

lemma discValue_lift (M : MDP S A) (f : A → B) (g : B → A) (hfg : ∀ b, f (g b) = b)
    (π : Policy S B) (s : S) (β : ℝ≥0∞) :
    discValue M (lift f g π) s β = discValue (quot M g) π s β := by
  refine tsum_congr fun t => ?_
  rw [expReward, expReward, ← law_lift M f g hfg, tsum_map_mul]
  congr 1; refine tsum_congr fun h => ?_
  rw [lift, tsum_map_mul]
  rfl

/-- `push` undoes `lift`; in particular `push` is onto. -/
lemma push_lift (M : MDP S A) (q : A → B) (g : B → A) (hqg : ∀ b, q (g b) = b)
    (π : Policy S B) : push M q g (lift q g π) = π := by
  funext x
  have hm := tsum_pair (joint M q (lift q g π) (start x) x.1.length) x
  rw [joint_fst] at hm
  by_cases h0 : (law M (lift q g π) (start x) x.1.length).map (histMap q) x = 0
  · have hx : histMap q (histMap g x) = x := by
      have e : Prod.map id q ∘ Prod.map id g = (id : S × B → S × B) := by
        funext ⟨a, b⟩; simp [hqg]
      simp [histMap, e]
    simp only [push, dif_pos (hm.trans h0), lift, hx, PMF.map_comp, Function.comp_def, hqg]
    exact PMF.map_id _
  · have hl : joint M q (lift q g π) (start x) x.1.length =
        ((law M (lift q g π) (start x) x.1.length).map (histMap q)).bind
          fun h' => (π h').map fun b => (h', b) := by
      rw [joint, PMF.bind_map]; congr 1; funext h
      simp only [Function.comp, lift, PMF.map_comp]; congr 1; funext b; simp [hqg]
    ext y
    have := congrArg (fun ν => ν (x, y)) ((joint_eq M q g _ _ _).symm.trans hl)
    simp only [bind_pair_apply] at this
    exact (ENNReal.mul_right_inj h0 (PMF.apply_ne_top _ _)).1 this

lemma optValue_quot (M : MDP S A) (q : A → B) (g : B → A) (hqg : ∀ b, q (g b) = b)
    (hP : ∀ s a, M.P s (g (q a)) = M.P s a) (hr : ∀ s a, M.r s (g (q a)) = M.r s a)
    (s : S) (β : ℝ≥0∞) : optValue (quot M g) s β = optValue M s β := by
  apply le_antisymm
  · refine iSup_le fun π => ?_
    rw [← discValue_lift M q g hqg]; exact le_iSup (fun π => discValue M π s β) _
  · refine iSup_le fun π => ?_
    rw [← discValue_push M q g hP hr]; exact le_iSup (fun π => discValue (quot M g) π s β) _

lemma isOptimal_push (M : MDP S A) (q : A → B) (g : B → A) (hqg : ∀ b, q (g b) = b)
    (hP : ∀ s a, M.P s (g (q a)) = M.P s a) (hr : ∀ s a, M.r s (g (q a)) = M.r s a)
    (β : ℝ≥0∞) (π : Policy S A) : IsOptimal M β π ↔ IsOptimal (quot M g) β (push M q g π) := by
  simp only [IsOptimal, discValue_push M q g hP hr, optValue_quot M q g hqg hP hr]

lemma isOptimal_lift (M : MDP S A) (q : A → B) (g : B → A) (hqg : ∀ b, q (g b) = b)
    (hP : ∀ s a, M.P s (g (q a)) = M.P s a) (hr : ∀ s a, M.r s (g (q a)) = M.r s a)
    (β : ℝ≥0∞) (π : Policy S B) : IsOptimal (quot M g) β π ↔ IsOptimal M β (lift q g π) := by
  simp only [IsOptimal, discValue_lift M q g hqg, optValue_quot M q g hqg hP hr]

/-! ## The witnesses -/

inductive Act3 | opt | red₁ | red₂
  deriving DecidableEq

inductive Act2 | opt | red
  deriving DecidableEq

/-- `opt` (reward `1`) stays put; the duplicates `red₁, red₂` (reward `0`) switch the state. -/
noncomputable def M₂ : MDP Bool Act3 :=
  ⟨fun s a => match a with
    | .opt => PMF.pure s
    | _ => PMF.pure (!s),
   fun _ a => match a with
    | .opt => 1
    | _ => 0⟩

/-- The merge map `red₁, red₂ ↦ red` and its section. -/
def mergeMap : Act3 → Act2
  | .opt => .opt
  | _ => .red

def rep : Act2 → Act3
  | .opt => .opt
  | .red => .red₁

/-- `M₂` with the duplicate actions `red₁, red₂` merged into one action `red`. -/
noncomputable def M₃ : MDP Bool Act2 := quot M₂ rep

lemma hqg (b : Act2) : mergeMap (rep b) = b := by cases b <;> rfl
lemma hP (s : Bool) (a : Act3) : M₂.P s (rep (mergeMap a)) = M₂.P s a := by cases a <;> rfl
lemma hr (s : Bool) (a : Act3) : M₂.r s (rep (mergeMap a)) = M₂.r s a := by cases a <;> rfl
lemma r₂_le (s : Bool) (a : Act3) : M₂.r s a ≤ 1 := by cases a <;> simp [M₂]
lemma r₃_le (s : Bool) (b : Act2) : M₃.r s b ≤ 1 := r₂_le s (rep b)

lemma not_injective (s : Bool) : ¬ Function.Injective (M₂.P s) := fun h => by
  cases h (show M₂.P s .red₁ = M₂.P s .red₂ from rfl)

lemma injective (s : Bool) : Function.Injective (M₃.P s) := by
  intro a b h
  cases a <;> cases b <;> first | rfl |
    (have := congrArg (fun p : PMF Bool => p s) h; simp [M₃, quot, M₂, rep] at this)

/-- **Main theorem.** `M₂` has the duplicate actions `red₁, red₂` and `M₃ = quot M₂ rep` merges
them. The transition structures differ: `M₂` has three actions and a kernel that is not injective
in the action, `M₃` has two actions and an injective kernel. For every discount factor `β`:
* the value functions agree, `V*(s) = (1 - β)⁻¹` (`= 1/(1-β)` for `β < 1`);
* `push` sends each policy `π` of `M₂` to a policy of `M₃` whose history process is the merged
  history process of `π`, with the same discounted value from every state, and `push` is onto;
* identical optimal policies, modulo identifying `red₁` with `red₂`: `π` is optimal in `M₂` iff
  `push π` is optimal in `M₃`, and the optimal policies of `M₃` are exactly the `push`-images of
  the optimal policies of `M₂`; both sets contain the policy always playing `opt`. -/
theorem conjecture4910 :
    (∀ s, M₂.P s .red₁ = M₂.P s .red₂ ∧ M₂.r s .red₁ = M₂.r s .red₂) ∧
    M₃ = quot M₂ rep ∧ (∀ b, mergeMap (rep b) = b) ∧
    (∀ s, ¬ Function.Injective (M₂.P s)) ∧ (∀ s, Function.Injective (M₃.P s)) ∧
    (∀ s β, optValue M₂ s β = optValue M₃ s β) ∧ (∀ s β, optValue M₂ s β = (1 - β)⁻¹) ∧
    (∀ π s t, law M₃ (push M₂ mergeMap rep π) s t = (law M₂ π s t).map (histMap mergeMap)) ∧
    (∀ π s β, discValue M₃ (push M₂ mergeMap rep π) s β = discValue M₂ π s β) ∧
    (∀ π, push M₂ mergeMap rep (lift mergeMap rep π) = π) ∧
    (∀ β, {π | IsOptimal M₂ β π} = push M₂ mergeMap rep ⁻¹' {π | IsOptimal M₃ β π}) ∧
    (∀ β, {π | IsOptimal M₃ β π} = push M₂ mergeMap rep '' {π | IsOptimal M₂ β π}) ∧
    (∀ β, IsOptimal M₂ β (constPol .opt) ∧ IsOptimal M₃ β (constPol .opt)) := by
  refine ⟨fun s => ⟨rfl, rfl⟩, rfl, hqg, not_injective, injective,
    fun s β => (optValue_quot M₂ mergeMap rep hqg hP hr s β).symm,
    optValue_eq M₂ r₂_le .opt fun _ => rfl, law_push M₂ mergeMap rep hP,
    discValue_push M₂ mergeMap rep hP hr, push_lift M₂ mergeMap rep hqg,
    fun β => Set.ext (isOptimal_push M₂ mergeMap rep hqg hP hr β), fun β => ?_,
    fun β => ⟨constPol_optimal M₂ r₂_le .opt (fun _ => rfl) β,
      constPol_optimal M₃ r₃_le .opt (fun _ => rfl) β⟩⟩
  ext π
  refine ⟨fun h => ⟨lift mergeMap rep π, (isOptimal_lift M₂ mergeMap rep hqg hP hr β π).1 h,
    push_lift M₂ mergeMap rep hqg π⟩, ?_⟩
  rintro ⟨π, hπ, rfl⟩
  exact (isOptimal_push M₂ mergeMap rep hqg hP hr β π).1 hπ

end Conjecture4910
