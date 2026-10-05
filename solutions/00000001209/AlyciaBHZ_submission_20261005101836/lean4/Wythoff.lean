/-
Conjecture 00000001209 (verbatim):
"Conjecture: For every t ≥ 1, the n-th P-position of t-Wythoff is asymptotic to (φn, φn + tn) with an explicit linear correction coefficient (t-Wythoff asymptotics)."

We use Fraenkel's standard game: remove a positive number from one heap,
or positive numbers k,l from both with |k-l| < t. Asymptotic to means
coordinatewise ratio tending to one. Indices start with the terminal position
at n=0 and positions are sorted by their smaller coordinate. We refute t=2.
For the alternative |k-l| ≤ t convention we prove the exact parameter
shift, giving the sqrt(2) slope and a refutation already at t=1.
-/
import Mathlib

/-!
Conjecture 00000001209 (verbatim):
"Conjecture: For every t ≥ 1, the n-th P-position of t-Wythoff is asymptotic to (φn, φn + tn) with an explicit linear correction coefficient (t-Wythoff asymptotics)."

We use Fraenkel's standard game: remove a positive number from one heap,
or positive numbers k,l from both with |k-l| < t. Asymptotic to means
coordinatewise ratio tending to one. Indices start with the terminal position
at n=0 and positions are sorted by their smaller coordinate. We refute t=2.
For the alternative |k-l| ≤ t convention we prove the exact parameter
shift, giving the sqrt(2) slope and a refutation already at t=1.
-/

noncomputable section
namespace Wythoff
open Filter Topology
open scoped symmDiff

abbrev Pos := ℕ × ℕ

/-- The inequalities in the last clause express |k-l| < t without subtraction in Z. -/
def Move (t : ℕ) (p q : Pos) : Prop :=
  (q.1 < p.1 ∧ q.2 = p.2) ∨ (q.1 = p.1 ∧ q.2 < p.2) ∨
  (q.1 < p.1 ∧ q.2 < p.2 ∧
    p.1 - q.1 < p.2 - q.2 + t ∧ p.2 - q.2 < p.1 - q.1 + t)

theorem move_decreases {t : ℕ} {p q : Pos} (h : Move t p q) :
    q.1 + q.2 < p.1 + p.2 := by
  rcases h with h | h | h <;> omega

/-- Normal-play losing positions, recursively on total heap size. -/
def isP (t : ℕ) (p : Pos) : Prop := ∀ q, Move t p q → ¬ isP t q
termination_by p.1 + p.2
decreasing_by exact move_decreases ‹Move t p q›

theorem isP_iff (t : ℕ) (p : Pos) :
    isP t p ↔ ∀ q, Move t p q → ¬ isP t q := by
  rw [isP]

/-- Alternative convention: positive removals from both heaps satisfy |k-l| ≤ t. -/
def MoveLE (t : ℕ) (p q : Pos) : Prop :=
  (q.1 < p.1 ∧ q.2 = p.2) ∨ (q.1 = p.1 ∧ q.2 < p.2) ∨
  (q.1 < p.1 ∧ q.2 < p.2 ∧
    p.1 - q.1 ≤ p.2 - q.2 + t ∧ p.2 - q.2 ≤ p.1 - q.1 + t)

/-- Integer removal amounts make the alternative convention an exact parameter shift. -/
theorem moveLE_iff_move_succ (t : ℕ) (p q : Pos) :
    MoveLE t p q ↔ Move (t+1) p q := by
  unfold MoveLE Move
  omega

/-- Normal-play P-positions defined directly from the alternative move relation. -/
def isPLE (t : ℕ) (p : Pos) : Prop := ∀ q, MoveLE t p q → ¬ isPLE t q
termination_by p.1 + p.2
decreasing_by exact move_decreases ((moveLE_iff_move_succ _ _ _).mp ‹MoveLE t p q›)

/-- The parameter shift preserves the complete recursively defined losing-position set. -/
theorem isPLE_iff_isP_succ (t : ℕ) (p : Pos) : isPLE t p ↔ isP (t+1) p := by
  have aux : ∀ n p, p.1 + p.2 = n → (isPLE t p ↔ isP (t+1) p) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p hp
      rw [isPLE, isP_iff]
      constructor
      · intro h q hq hqp
        have he := ih _ (by have := move_decreases hq; omega) q rfl
        exact h q ((moveLE_iff_move_succ t p q).mpr hq) (he.mpr hqp)
      · intro h q hq hqp
        have hq' := (moveLE_iff_move_succ t p q).mp hq
        have he := ih _ (by have := move_decreases hq'; omega) q rfl
        exact h q hq' (he.mp hqp)
  exact aux _ p rfl

instance moveDecidable (t : ℕ) (p q : Pos) : Decidable (Move t p q) := by
  unfold Move
  infer_instance

/-- A terminating finite search decides the recursively defined P-predicate. -/
def decideP (t : ℕ) (p : Pos) : Decidable (isP t p) := by
  letI step (x : Fin (p.1+1)) (y : Fin (p.2+1)) :
      Decidable (Move t p (x.val,y.val) → ¬ isP t (x.val,y.val)) :=
    if hm : Move t p (x.val,y.val) then
      haveI := decideP t (x.val,y.val)
      inferInstance
    else isTrue (fun h => False.elim (hm h))
  have he : isP t p ↔ ∀ x : Fin (p.1+1), ∀ y : Fin (p.2+1),
      Move t p (x.val,y.val) → ¬ isP t (x.val,y.val) := by
    rw [isP_iff]
    constructor
    · intro h x y; exact h _
    · intro h q hm
      have hx : q.1 < p.1+1 := by rcases hm with h | h | h <;> omega
      have hy : q.2 < p.2+1 := by rcases hm with h | h | h <;> omega
      exact h ⟨q.1,hx⟩ ⟨q.2,hy⟩ hm
  exact decidable_of_iff _ he.symm
termination_by p.1 + p.2
decreasing_by exact move_decreases ‹Move t p (x.val,y.val)›

def a (n : ℕ) : ℕ := ⌊(n : ℝ) * Real.sqrt 2⌋₊
def b (n : ℕ) : ℕ := a n + 2 * n

lemma root_gt_one : 1 < Real.sqrt 2 := by
  have := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have := Real.sqrt_nonneg (2 : ℝ)
  nlinarith

lemma a_nonneg_arg (n : ℕ) : 0 ≤ (n : ℝ) * Real.sqrt 2 := by positivity

@[simp] lemma a_zero : a 0 = 0 := by simp [a]
@[simp] lemma b_zero : b 0 = 0 := by simp [b]

lemma a_strict : StrictMono a := by
  apply strictMono_nat_of_lt_succ
  intro n
  have h := Nat.floor_mono (show (n : ℝ) * Real.sqrt 2 + 1 ≤
      ((n + 1 : ℕ) : ℝ) * Real.sqrt 2 by
    push_cast; nlinarith [root_gt_one])
  rw [Nat.floor_add_one (a_nonneg_arg n)] at h
  exact lt_of_lt_of_le (Nat.lt_succ_self (a n)) h

lemma b_strict : StrictMono b := by
  intro n m h
  have := a_strict h
  dsimp [b]; omega

lemma a_le_b (n : ℕ) : a n ≤ b n := by dsimp [b]; omega

lemma beatty_a (n : ℕ) : beattySeq (Real.sqrt 2) (n : ℤ) = (a n : ℤ) := by
  simp only [beattySeq, Int.cast_natCast, a]
  exact (Int.natCast_floor_eq_floor (a_nonneg_arg n)).symm

lemma beatty_b (n : ℕ) : beattySeq (Real.sqrt 2 + 2) (n : ℤ) = (b n : ℤ) := by
  simp only [beattySeq, Int.cast_natCast, b, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  rw [mul_add, show (n : ℝ) * 2 = ((2 * n : ℕ) : ℝ) by push_cast; ring]
  rw [Int.floor_add_natCast]
  rw [← beatty_a]
  rfl

lemma conjugate : (Real.sqrt 2).HolderConjugate (Real.sqrt 2 + 2) := by
  apply Real.holderConjugate_iff.mpr
  refine ⟨root_gt_one, ?_⟩
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hpos : 0 < Real.sqrt 2 := by linarith [root_gt_one]
  field_simp
  nlinarith

lemma partition_int (x : ℤ) (hx : 0 < x) :
    ((∃ n : ℤ, 0 < n ∧ beattySeq (Real.sqrt 2) n = x) ∧
      ¬ ∃ n : ℤ, 0 < n ∧ beattySeq (Real.sqrt 2 + 2) n = x) ∨
    ((∃ n : ℤ, 0 < n ∧ beattySeq (Real.sqrt 2 + 2) n = x) ∧
      ¬ ∃ n : ℤ, 0 < n ∧ beattySeq (Real.sqrt 2) n = x) := by
  have h := Irrational.beattySeq_symmDiff_beattySeq_pos conjugate irrational_sqrt_two
  have hx' : x ∈ ({beattySeq (Real.sqrt 2) k | k > 0} ∆
      {beattySeq (Real.sqrt 2 + 2) k | k > 0}) := by rw [h]; exact hx
  simpa only [Set.mem_symmDiff, Set.mem_ofPred_eq] using hx'

lemma exhaustive (x : ℕ) : (∃ n, x = a n) ∨ (∃ n, x = b n) := by
  by_cases hx : x = 0
  · left; exact ⟨0, by simp [hx]⟩
  have hp : (0 : ℤ) < x := by omega
  rcases partition_int x hp with ⟨⟨n, hn, he⟩, _⟩ | ⟨⟨n, hn, he⟩, _⟩
  · left; refine ⟨n.toNat, ?_⟩
    rw [← Int.toNat_of_nonneg (by omega : 0 ≤ n)] at he
    rw [beatty_a] at he
    exact_mod_cast he.symm
  · right; refine ⟨n.toNat, ?_⟩
    rw [← Int.toNat_of_nonneg (by omega : 0 ≤ n)] at he
    rw [beatty_b] at he
    exact_mod_cast he.symm

lemma a_eq_b (n m : ℕ) (h : a n = b m) : n = 0 ∧ m = 0 := by
  by_cases hn : n = 0
  · subst n; have := a_le_b m; have := a_strict; simp only [a_zero] at h
    have hm : m = 0 := by
      by_contra hm
      have hh := a_strict (show 0 < m by omega)
      simp only [a_zero] at hh
      omega
    exact ⟨rfl, hm⟩
  have han : 0 < a n := by simpa using a_strict (show 0 < n by omega)
  have hm : 0 < m := by
    by_contra hm
    have he : m = 0 := by omega
    subst m
    simp only [b_zero] at h
    omega
  have ia : ∃ k : ℤ, 0 < k ∧ beattySeq (Real.sqrt 2) k = (a n : ℤ) :=
    ⟨n, by exact_mod_cast (show 0 < n by omega), beatty_a n⟩
  have ib : ∃ k : ℤ, 0 < k ∧ beattySeq (Real.sqrt 2 + 2) k = (a n : ℤ) :=
    ⟨m, by exact_mod_cast hm, by rw [beatty_b, h]⟩
  rcases partition_int (a n) (by exact_mod_cast han) with h' | h'
  · exact False.elim (h'.2 ib)
  · exact False.elim (h'.2 ia)

/-- The unordered candidate positions, including both heap orientations. -/
def Candidate (p : Pos) : Prop :=
  ∃ n, (p = (a n, b n)) ∨ (p = (b n, a n))

lemma candidate_swap (x y : ℕ) : Candidate (x,y) ↔ Candidate (y,x) := by
  constructor <;> rintro ⟨n, h | h⟩ <;> refine ⟨n, ?_⟩
  · right; simpa using congrArg Prod.swap h
  · left; simpa using congrArg Prod.swap h
  · right; simpa using congrArg Prod.swap h
  · left; simpa using congrArg Prod.swap h

lemma move_swap (t x y u v : ℕ) : Move t (x,y) (u,v) ↔ Move t (y,x) (v,u) := by
  simp only [Move]
  tauto

lemma no_candidate_move {p q : Pos} (hp : Candidate p) (hq : Candidate q) :
    ¬ Move 2 p q := by
  obtain ⟨n, rfl | rfl⟩ := hp <;> obtain ⟨m, rfl | rfl⟩ := hq
  all_goals
    intro h
    rcases h with h | h | h
  · have he := b_strict.injective h.2; subst m; omega
  · have he := a_strict.injective h.1; subst m; omega
  · have hm : m < n := a_strict.lt_iff_lt.mp h.1
    dsimp [b] at h; omega
  · have he := a_eq_b m n h.2; rcases he with ⟨rfl,rfl⟩; simp at h
  · have he := a_eq_b n m h.1.symm; rcases he with ⟨rfl,rfl⟩; simp at h
  · have hn : n = 0 := by dsimp [b] at h; omega
    have hm : m = 0 := by dsimp [b] at h; omega
    subst n; subst m; simp at h
  · have he := a_eq_b n m h.2.symm; rcases he with ⟨rfl,rfl⟩; simp at h
  · have he := a_eq_b m n h.1; rcases he with ⟨rfl,rfl⟩; simp at h
  · have hn : n = 0 := by dsimp [b] at h; omega
    have hm : m = 0 := by dsimp [b] at h; omega
    subst n; subst m; simp at h
  · have he := a_strict.injective h.2; subst m; omega
  · have he := b_strict.injective h.1; subst m; omega
  · have hm : m < n := b_strict.lt_iff_lt.mp h.1
    dsimp [b] at h; omega

lemma reach_candidate_ordered (x y : ℕ) (hxy : x ≤ y) (hp : ¬ Candidate (x,y)) :
    ∃ q, Move 2 (x,y) q ∧ Candidate q := by
  rcases exhaustive x with ⟨n,rfl⟩ | ⟨n,rfl⟩
  · have hne : y ≠ b n := by intro he; apply hp; exact ⟨n, Or.inl (by simp [he])⟩
    by_cases hy : b n < y
    · exact ⟨(a n,b n), Or.inr (Or.inl ⟨rfl,hy⟩), n, Or.inl rfl⟩
    · let m := (y - a n) / 2
      have hm : m < n := by dsimp [m, b] at *; omega
      have ha : a m < a n := a_strict hm
      have hb : b m < y := by dsimp [m,b] at *; omega
      refine ⟨(a m,b m), Or.inr (Or.inr ?_), m, Or.inl rfl⟩
      dsimp [Move, b, m] at *
      exact ⟨ha,hb,by omega,by omega⟩
  · have hne : a n ≠ y := by
      intro he
      apply hp
      exact ⟨n, Or.inr (by simp [he])⟩
    have ha : a n < y := lt_of_le_of_ne ((a_le_b n).trans hxy) hne
    exact ⟨(b n,a n), Or.inr (Or.inl ⟨rfl,ha⟩), n, Or.inr rfl⟩

lemma reach_candidate {p : Pos} (hp : ¬ Candidate p) :
    ∃ q, Move 2 p q ∧ Candidate q := by
  obtain ⟨x,y⟩ := p
  by_cases hxy : x ≤ y
  · exact reach_candidate_ordered x y hxy hp
  · have hp' : ¬ Candidate (y,x) := fun h => hp ((candidate_swap x y).mpr h)
    obtain ⟨⟨u,v⟩,hm,hc⟩ := reach_candidate_ordered y x (by omega) hp'
    exact ⟨(v,u), (move_swap 2 x y v u).mpr hm, (candidate_swap v u).mpr hc⟩

/-- Exact characterization of the genuine recursively defined game. -/
theorem p_characterization (p : Pos) : isP 2 p ↔ Candidate p := by
  have aux : ∀ s, ∀ p : Pos, p.1 + p.2 = s → (isP 2 p ↔ Candidate p) := by
    intro s
    induction s using Nat.strong_induction_on with
    | h s ih =>
      intro p hs
      rw [isP_iff]
      constructor
      · intro hp
        by_contra hc
        obtain ⟨q,hm,hq⟩ := reach_candidate hc
        exact hp q hm ((ih _ (by have := move_decreases hm; omega) q rfl).mpr hq)
      · intro hc q hm hq
        have cq := (ih _ (by have := move_decreases hm; omega) q rfl).mp hq
        exact no_candidate_move hc cq hm
  exact aux _ p rfl

/-- Thus `(a n,b n)` enumerates every sorted P-position exactly once. -/
theorem sorted_p_positions (x y : ℕ) (hxy : x ≤ y) :
    isP 2 (x,y) ↔ ∃ n, x = a n ∧ y = b n := by
  rw [p_characterization]
  constructor
  · rintro ⟨n,h | h⟩
    · cases h; exact ⟨n,rfl,rfl⟩
    · cases h
      have he : n = 0 := by dsimp [b] at hxy; omega
      subst n; exact ⟨0,rfl,rfl⟩
  · rintro ⟨n,rfl,rfl⟩; exact ⟨n,Or.inl rfl⟩

/-- The actual n-th smaller heap, defined directly from the game's P-predicate. -/
def lower (t x : ℕ) : Prop := ∃ y, x ≤ y ∧ isP t (x,y)
def nthLower (t n : ℕ) : ℕ := Nat.nth (lower t) n

lemma lower_two (x : ℕ) : lower 2 x ↔ ∃ n, a n = x := by
  constructor
  · rintro ⟨y,hxy,hp⟩
    obtain ⟨n,hn,_⟩ := (sorted_p_positions x y hxy).mp hp
    exact ⟨n,hn.symm⟩
  · rintro ⟨n,rfl⟩
    exact ⟨b n,a_le_b n,(sorted_p_positions _ _ (a_le_b n)).mpr ⟨n,rfl,rfl⟩⟩

lemma nthLower_two (n : ℕ) : nthLower 2 n = a n := by
  have hinf : (Set.ofPred (lower 2)).Infinite := by
    have he : Set.ofPred (lower 2) = Set.range a := by ext x; exact lower_two x
    rw [he]; exact Set.infinite_range_of_injective a_strict.injective
  have h := Nat.nth_comp_of_strictMono (p := lower 2) (n := n) a_strict
    (fun k hk => (lower_two k).mp hk) (fun hf => False.elim (hinf hf))
  have he : (fun i => lower 2 (a i)) = (fun _ : ℕ => True) := by
    funext i; apply propext; exact ⟨fun _ => trivial, fun _ => (lower_two _).mpr ⟨i,rfl⟩⟩
  rw [he] at h
  simpa [nthLower] using h.symm

lemma floor_bounds (n : ℕ) :
    (a n : ℝ) ≤ (n : ℝ) * Real.sqrt 2 ∧
      (n : ℝ) * Real.sqrt 2 < (a n : ℝ) + 1 :=
  ⟨Nat.floor_le (a_nonneg_arg n), Nat.lt_floor_add_one _⟩

/-- The exact slope, with the floor error squeezed by 1/n. -/
theorem lower_slope : Tendsto (fun n => (a n : ℝ) / n) atTop (𝓝 (Real.sqrt 2)) := by
  have herr : Tendsto (fun n => Real.sqrt 2 - (a n : ℝ) / n) atTop (𝓝 0) := by
    apply squeeze_zero' (g := fun n : ℕ => 1 / (n : ℝ))
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hb := (floor_bounds n).1
      have hd : (a n : ℝ) / n ≤ Real.sqrt 2 := (div_le_iff₀ hp).mpr (by nlinarith)
      linarith
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hb := (floor_bounds n).2
      apply (le_div_iff₀ hp).mpr
      have hc : (a n : ℝ) / n * n = a n := div_mul_cancel₀ _ hp.ne'
      nlinarith
    · exact tendsto_one_div_atTop_nhds_zero_nat
  have h := (tendsto_const_nhds (x := Real.sqrt 2)).sub herr
  simpa using h

lemma root_ne_phi : Real.sqrt 2 ≠ Real.goldenRatio := by
  intro he
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hg := Real.goldenRatio_sq
  rw [← he] at hg
  have hr : Real.sqrt 2 = 1 := by nlinarith
  linarith [root_gt_one]

/-- The conjectured first-coordinate ratio cannot tend to one. -/
theorem t_two_refutation :
    ¬ Tendsto (fun n => (nthLower 2 n : ℝ) / (Real.goldenRatio * n)) atTop (𝓝 1) := by
  intro hc
  have hl : Tendsto (fun n => (nthLower 2 n : ℝ) / (Real.goldenRatio * n))
      atTop (𝓝 (Real.sqrt 2 / Real.goldenRatio)) := by
    simpa [nthLower_two, div_div, mul_comm] using lower_slope.div_const Real.goldenRatio
  have he : Real.sqrt 2 / Real.goldenRatio = 1 := tendsto_nhds_unique hl hc
  have he' : Real.sqrt 2 = Real.goldenRatio := by
    have := (div_eq_iff Real.goldenRatio_ne_zero).mp he
    simpa using this
  exact root_ne_phi he'

/-- Even the necessary first-coordinate part of the universal assertion is false. -/
theorem universal_refutation :
    ¬ (∀ t : ℕ, 1 ≤ t →
      Tendsto (fun n => (nthLower t n : ℝ) / (Real.goldenRatio * n)) atTop (𝓝 1)) := by
  intro h
  exact t_two_refutation (h 2 (by omega))

/-- Explicit linear correction under the expansion reading of the wording. -/
theorem correction_slope :
    Tendsto (fun n => ((a n : ℝ) - Real.goldenRatio * n) / n)
      atTop (𝓝 (Real.sqrt 2 - Real.goldenRatio)) := by
  have he : (fun n : ℕ => ((a n : ℝ) - Real.goldenRatio * n) / n) =ᶠ[atTop]
      (fun n => (a n : ℝ) / n - Real.goldenRatio) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    field_simp
  exact (lower_slope.sub_const Real.goldenRatio).congr' he.symm

/-- The actual n-th smaller heap for the non-strict convention. -/
def lowerLE (t x : ℕ) : Prop := ∃ y, x ≤ y ∧ isPLE t (x,y)
def nthLowerLE (t n : ℕ) : ℕ := Nat.nth (lowerLE t) n

theorem nthLowerLE_eq_succ (t n : ℕ) : nthLowerLE t n = nthLower (t+1) n := by
  have he : lowerLE t = lower (t+1) := by
    funext x
    apply propext
    simp only [lowerLE, lower, isPLE_iff_isP_succ]
  unfold nthLowerLE nthLower
  rw [he]

/-- Non-strict t=1 already has the sqrt(2) slope, rather than the golden-ratio slope. -/
theorem lowerLE_one_slope :
    Tendsto (fun n => (nthLowerLE 1 n : ℝ) / n) atTop (𝓝 (Real.sqrt 2)) := by
  simpa only [nthLowerLE_eq_succ, Nat.reduceAdd, nthLower_two] using lower_slope

theorem t_one_le_refutation :
    ¬ Tendsto (fun n => (nthLowerLE 1 n : ℝ) / (Real.goldenRatio * n))
      atTop (𝓝 1) := by
  simpa only [nthLowerLE_eq_succ, Nat.reduceAdd] using t_two_refutation

theorem universal_le_refutation :
    ¬ (∀ t : ℕ, 1 ≤ t →
      Tendsto (fun n => (nthLowerLE t n : ℝ) / (Real.goldenRatio * n)) atTop (𝓝 1)) := by
  intro h
  exact t_one_le_refutation (h 1 (by omega))

#print axioms correction_slope

#print axioms p_characterization
#print axioms sorted_p_positions
#print axioms nthLower_two
#print axioms lower_slope
#print axioms t_two_refutation
#print axioms universal_refutation

#print axioms moveLE_iff_move_succ
#print axioms isPLE_iff_isP_succ
#print axioms lowerLE_one_slope
#print axioms t_one_le_refutation
#print axioms universal_le_refutation

end Wythoff
