import Lean

/-!
A self-contained Lean 4 formalization of infinitude for the Ulam sequence U(1,n).
No Mathlib dependency. Indices begin at zero.

A representation is an unordered pair of DISTINCT earlier values, represented
canonically as a < b. Each next term is the LEAST integer above the current
maximum with exactly one such representation.
-/

namespace Ulam205Core

/-- Exactly one unordered representation by two distinct members of A. -/
def UniqueSum (A : Nat → Prop) (x : Nat) : Prop :=
  ∃ a b, a < b ∧ A a ∧ A b ∧ a + b = x ∧
    ∀ c d, c < d → A c → A d → c + d = x → c = a ∧ d = b

/-- A prefix together with its largest and second-largest elements. -/
structure Prefix where
  mem : Nat → Prop
  top : Nat
  second : Nat
  second_pos : 0 < second
  second_lt_top : second < top
  top_mem : mem top
  second_mem : mem second
  bound : ∀ x, mem x → x ≤ second ∨ x = top

def Admissible (p : Prefix) (x : Nat) : Prop :=
  p.top < x ∧ UniqueSum p.mem x

/-- The sum of the two largest elements has a unique representation. -/
theorem largest_pair_unique (p : Prefix) :
    UniqueSum p.mem (p.second + p.top) := by
  refine ⟨p.second, p.top, p.second_lt_top, p.second_mem, p.top_mem, rfl, ?_⟩
  intro c d hcd hc hd hsum
  rcases p.bound c hc with hc | hc
  · rcases p.bound d hd with hd | hd
    · have hst := p.second_lt_top
      omega
    · subst d
      constructor
      · omega
      · rfl
  · rcases p.bound d hd with hd | hd
    · have hst := p.second_lt_top
      omega
    · omega

theorem candidate_exists (p : Prefix) : ∃ x, Admissible p x := by
  refine ⟨p.second + p.top, ?_, largest_pair_unique p⟩
  have hp := p.second_pos
  omega

/-- A direct well-ordering argument, avoiding any dependency on Mathlib. -/
theorem least_exists (P : Nat → Prop) (h : ∃ x, P x) :
    ∃ x, P x ∧ ∀ y, P y → x ≤ y := by
  classical
  have aux : ∀ x, P x → ∃ z, P z ∧ ∀ y, P y → z ≤ y := by
    intro x
    induction x using Nat.strongRecOn with
    | ind x ih =>
      intro hx
      by_cases hs : ∃ y, y < x ∧ P y
      · obtain ⟨y, hy, hpy⟩ := hs
        exact ih y hy hpy
      · refine ⟨x, hx, ?_⟩
        intro y hpy
        by_cases hxy : x ≤ y
        · exact hxy
        · exact False.elim (hs ⟨y, by omega, hpy⟩)
  obtain ⟨x, hx⟩ := h
  exact aux x hx

noncomputable def next (p : Prefix) : Nat :=
  Classical.choose (least_exists (Admissible p) (candidate_exists p))

theorem next_spec (p : Prefix) :
    Admissible p (next p) ∧ ∀ x, Admissible p x → next p ≤ x :=
  Classical.choose_spec (least_exists (Admissible p) (candidate_exists p))

theorem next_gt (p : Prefix) : p.top < next p :=
  (next_spec p).1.1

theorem next_upper (p : Prefix) : next p ≤ p.second + p.top := by
  apply (next_spec p).2
  exact ⟨by have hp := p.second_pos; omega, largest_pair_unique p⟩

noncomputable def advance (p : Prefix) : Prefix where
  mem x := x = next p ∨ p.mem x
  top := next p
  second := p.top
  second_pos := by have hp := p.second_pos; have hs := p.second_lt_top; omega
  second_lt_top := next_gt p
  top_mem := Or.inl rfl
  second_mem := Or.inr p.top_mem
  bound := by
    intro x hx
    rcases hx with hx | hx
    · exact Or.inr hx
    · apply Or.inl
      rcases p.bound x hx with hx | hx
      · have hs := p.second_lt_top
        omega
      · omega

def seed (n : Nat) (hn : 2 ≤ n) : Prefix where
  mem x := x = 1 ∨ x = n
  top := n
  second := 1
  second_pos := by omega
  second_lt_top := by omega
  top_mem := Or.inr rfl
  second_mem := Or.inl rfl
  bound := by
    intro x hx
    rcases hx with hx | hx
    · exact Or.inl (by omega)
    · exact Or.inr hx

noncomputable def stage (n : Nat) (hn : 2 ≤ n) : Nat → Prefix
  | 0 => seed n hn
  | r + 1 => advance (stage n hn r)

/-- The actual recursively constructed sequence, beginning 1,n. -/
noncomputable def sequence (n : Nat) (hn : 2 ≤ n) : Nat → Nat
  | 0 => 1
  | r + 1 => (stage n hn r).top

@[simp] theorem sequence_zero (n : Nat) (hn : 2 ≤ n) :
    sequence n hn 0 = 1 := rfl

@[simp] theorem sequence_one (n : Nat) (hn : 2 ≤ n) :
    sequence n hn 1 = n := rfl

@[simp] theorem sequence_succ (n : Nat) (hn : 2 ≤ n) (r : Nat) :
    sequence n hn (r + 1) = (stage n hn r).top := rfl

def Earlier (u : Nat → Nat) (k x : Nat) : Prop :=
  ∃ i, i < k ∧ u i = x

/-- The state contains exactly the preceding terms, with no extra elements. -/
theorem stage_mem_iff (n : Nat) (hn : 2 ≤ n) (r x : Nat) :
    (stage n hn r).mem x ↔ Earlier (sequence n hn) (r + 2) x := by
  induction r with
  | zero =>
    change (x = 1 ∨ x = n) ↔ ∃ i, i < 2 ∧ sequence n hn i = x
    constructor
    · intro hx
      rcases hx with hx | hx
      · exact ⟨0, by omega, by simpa using hx.symm⟩
      · exact ⟨1, by omega, by exact hx.symm⟩
    · rintro ⟨i, hi, hx⟩
      have hcases : i = 0 ∨ i = 1 := by omega
      rcases hcases with rfl | rfl
      · exact Or.inl (by simpa using hx.symm)
      · exact Or.inr (by exact hx.symm)
  | succ r ih =>
    change (x = next (stage n hn r) ∨ (stage n hn r).mem x) ↔
      ∃ i, i < r + 1 + 2 ∧ sequence n hn i = x
    constructor
    · intro hx
      rcases hx with hx | hx
      · refine ⟨r + 2, by omega, ?_⟩
        exact hx.symm
      · obtain ⟨i, hi, hui⟩ := ih.mp hx
        exact ⟨i, by omega, hui⟩
    · rintro ⟨i, hi, hui⟩
      by_cases hlast : i = r + 2
      · subst i
        exact Or.inl hui.symm
      · exact Or.inr (ih.mpr ⟨i, by omega, hui⟩)

/-- The defining least-unique-sum rule, stated using earlier sequence terms. -/
def IsUlam (n : Nat) (u : Nat → Nat) : Prop :=
  u 0 = 1 ∧ u 1 = n ∧
  ∀ r,
    u (r + 1) < u (r + 2) ∧
    UniqueSum (Earlier u (r + 2)) (u (r + 2)) ∧
    ∀ x, u (r + 1) < x → UniqueSum (Earlier u (r + 2)) x → u (r + 2) ≤ x

/-- The construction obeys the entire Ulam rule, including minimality. -/
theorem sequence_isUlam (n : Nat) (hn : 2 ≤ n) : IsUlam n (sequence n hn) := by
  refine ⟨rfl, rfl, ?_⟩
  intro r
  have hsets : (stage n hn r).mem = Earlier (sequence n hn) (r + 2) := by
    funext x
    exact propext (stage_mem_iff n hn r x)
  have hs := next_spec (stage n hn r)
  change (stage n hn r).top < next (stage n hn r) ∧
    UniqueSum (Earlier (sequence n hn) (r + 2)) (next (stage n hn r)) ∧
    ∀ x, (stage n hn r).top < x →
      UniqueSum (Earlier (sequence n hn) (r + 2)) x → next (stage n hn r) ≤ x
  refine ⟨hs.1.1, ?_, ?_⟩
  · rw [← hsets]
    exact hs.1.2
  · intro x hx hsum
    apply hs.2 x
    rw [← hsets] at hsum
    exact ⟨hx, hsum⟩

theorem sequence_step_lt (n : Nat) (hn : 2 ≤ n) (k : Nat) :
    sequence n hn k < sequence n hn (k + 1) := by
  cases k with
  | zero => change 1 < n; omega
  | succ r => exact (sequence_isUlam n hn).2.2 r |>.1

theorem sequence_strictMono (n : Nat) (hn : 2 ≤ n) :
    ∀ i j, i < j → sequence n hn i < sequence n hn j := by
  intro i j
  induction j with
  | zero => intro hij; omega
  | succ j ih =>
    intro hij
    by_cases heq : i = j
    · subst i
      exact sequence_step_lt n hn j
    · have hij' : i < j := by omega
      exact Nat.lt_trans (ih hij') (sequence_step_lt n hn j)

theorem sequence_injective (n : Nat) (hn : 2 ≤ n) :
    Function.Injective (sequence n hn) := by
  intro i j heq
  by_cases he : i = j
  · exact he
  have hcases : i < j ∨ j < i := by omega
  rcases hcases with hij | hji
  · have := sequence_strictMono n hn i j hij
    omega
  · have := sequence_strictMono n hn j i hji
    omega

theorem index_lower_bound (n : Nat) (hn : 2 ≤ n) (k : Nat) :
    k + 1 ≤ sequence n hn k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hs := sequence_step_lt n hn k
    omega

theorem sequence_unbounded (n : Nat) (hn : 2 ≤ n) :
    ∀ B, ∃ k, B < sequence n hn k := by
  intro B
  exact ⟨B, by have h := index_lower_bound n hn B; omega⟩

/-- Membership in the full infinite range, not a truncated state. -/
def InSequence (n : Nat) (hn : 2 ≤ n) (x : Nat) : Prop :=
  ∃ i, sequence n hn i = x

/-- Every full-range value below a term already belongs to its earlier prefix. -/
theorem range_below_is_earlier (n : Nat) (hn : 2 ≤ n) (k x : Nat)
    (hx : InSequence n hn x) (hlt : x < sequence n hn k) :
    Earlier (sequence n hn) k x := by
  obtain ⟨i, hi⟩ := hx
  refine ⟨i, ?_, hi⟩
  by_cases h : i < k
  · exact h
  apply False.elim
  have hki : k ≤ i := by omega
  by_cases he : k = i
  · subst i
    omega
  · have hs := sequence_strictMono n hn k i (by omega)
    omega

/-- Each selected non-seed term has exactly one distinct-pair representation
    even when all values in the final infinite sequence are allowed. -/
theorem sequence_global_uniqueSum (n : Nat) (hn : 2 ≤ n) (r : Nat) :
    UniqueSum (InSequence n hn) (sequence n hn (r + 2)) := by
  obtain ⟨a, b, hab, ha, hb, hsum, huniq⟩ :=
    (sequence_isUlam n hn).2.2 r |>.2.1
  have lift : ∀ x, Earlier (sequence n hn) (r + 2) x → InSequence n hn x := by
    rintro x ⟨i, _, hi⟩
    exact ⟨i, hi⟩
  refine ⟨a, b, hab, lift a ha, lift b hb, hsum, ?_⟩
  intro c d hcd hc hd hsum'
  have pos : ∀ x, InSequence n hn x → 0 < x := by
    rintro x ⟨i, hi⟩
    have hp := index_lower_bound n hn i
    omega
  have hcpos := pos c hc
  have hdpos := pos d hd
  exact huniq c d hcd
    (range_below_is_earlier n hn (r + 2) c hc (by omega))
    (range_below_is_earlier n hn (r + 2) d hd (by omega)) hsum'

/-- A finite-list bound, used to state infinitude without a set library. -/
def listBound : List Nat → Nat
  | [] => 0
  | a :: as => a + listBound as

theorem mem_le_listBound (x : Nat) (xs : List Nat) (hx : x ∈ xs) :
    x ≤ listBound xs := by
  induction xs with
  | nil => simp at hx
  | cons a as ih =>
    simp only [List.mem_cons] at hx
    change x ≤ a + listBound as
    rcases hx with hx | hx
    · omega
    · have hb := ih hx
      omega

/-- Infinitude: no finite list contains the range of the Ulam sequence. -/
theorem sequence_infinite (n : Nat) (hn : 2 ≤ n) :
    ¬ ∃ xs : List Nat, ∀ k, sequence n hn k ∈ xs := by
  rintro ⟨xs, hxs⟩
  obtain ⟨k, hk⟩ := sequence_unbounded n hn (listBound xs)
  have hb := mem_le_listBound (sequence n hn k) xs (hxs k)
  omega

/-- Quantitative growth estimate: the (r+2)-nd term is at most n*2^r. -/
theorem exponential_upper_bound (n : Nat) (hn : 2 ≤ n) (r : Nat) :
    sequence n hn (r + 1) ≤ n * 2 ^ r := by
  change (stage n hn r).top ≤ n * 2 ^ r
  induction r with
  | zero => simp [stage, seed]
  | succ r ih =>
    change next (stage n hn r) ≤ n * 2 ^ (r + 1)
    have hu := next_upper (stage n hn r)
    have hs := (stage n hn r).second_lt_top
    have heq : n * 2 ^ (r + 1) = n * 2 ^ r + n * 2 ^ r := by
      simp only [Nat.pow_succ, Nat.mul_two, Nat.mul_add]
    rw [heq]
    omega

/-- All of the first r+2 terms lie at or below n*2^r. -/
theorem first_terms_bounded (n : Nat) (hn : 2 ≤ n) (r i : Nat) (hi : i < r + 2) :
    sequence n hn i ≤ n * 2 ^ r := by
  have hu := exponential_upper_bound n hn r
  by_cases heq : i = r + 1
  · simpa [heq] using hu
  · have hlt : i < r + 1 := by omega
    have hs := sequence_strictMono n hn i (r + 1) hlt
    omega

/-- A precise counting lower bound: r+2 DISTINCT Ulam values up to n*2^r. -/
theorem counting_lower_bound (n : Nat) (hn : 2 ≤ n) (r : Nat) :
    ∃ f : Fin (r + 2) → Nat,
      Function.Injective f ∧
      (∀ i, ∃ k, sequence n hn k = f i) ∧
      (∀ i, f i ≤ n * 2 ^ r) := by
  refine ⟨fun i => sequence n hn i.val, ?_, ?_, ?_⟩
  · intro i j hij
    apply Fin.ext
    exact sequence_injective n hn hij
  · intro i
    exact ⟨i.val, rfl⟩
  · intro i
    exact first_terms_bounded n hn r i.val i.isLt

/-- Full existence and infinitude theorem for every seed n ≥ 2. -/
theorem conjecture205 (n : Nat) (hn : 2 ≤ n) :
    ∃ u : Nat → Nat,
      IsUlam n u ∧
      (∀ i j, i < j → u i < u j) ∧
      (¬ ∃ xs : List Nat, ∀ k, u k ∈ xs) ∧
      (∀ r, u (r + 1) ≤ n * 2 ^ r) := by
  exact ⟨sequence n hn, sequence_isUlam n hn, sequence_strictMono n hn,
    sequence_infinite n hn, exponential_upper_bound n hn⟩

/-- The least-choice rule determines at most one sequence. -/
theorem sequence_unique (n : Nat) (u v : Nat → Nat)
    (hu : IsUlam n u) (hv : IsUlam n v) : u = v := by
  funext j
  induction j using Nat.strongRecOn with
  | ind j ih =>
    cases j with
    | zero => exact hu.1.trans hv.1.symm
    | succ j =>
      cases j with
      | zero => exact hu.2.1.trans hv.2.1.symm
      | succ k =>
        have hp : u (k + 1) = v (k + 1) := ih (k + 1) (by omega)
        have hsets : Earlier u (k + 2) = Earlier v (k + 2) := by
          funext x
          apply propext
          constructor
          · rintro ⟨i, hi, hui⟩
            exact ⟨i, hi, (ih i hi).symm.trans hui⟩
          · rintro ⟨i, hi, hvi⟩
            exact ⟨i, hi, (ih i hi).trans hvi⟩
        have hru := hu.2.2 k
        have hrv := hv.2.2 k
        rw [hp, hsets] at hru
        exact Nat.le_antisymm
          (hru.2.2 _ hrv.1 hrv.2.1) (hrv.2.2 _ hru.1 hru.2.1)

/-- Full infinitude and quantitative counting conclusion in a single theorem. -/
theorem conjecture_00000000205 (n : Nat) (hn : 2 ≤ n) :
    ∃ u : Nat → Nat,
      IsUlam n u ∧
      (∀ i j, i < j → u i < u j) ∧
      (¬ ∃ xs : List Nat, ∀ k, u k ∈ xs) ∧
      (∀ r, u (r + 1) ≤ n * 2 ^ r) ∧
      (∀ r, ∃ f : Fin (r + 2) → Nat,
        Function.Injective f ∧
        (∀ i, ∃ k, u k = f i) ∧
        (∀ i, f i ≤ n * 2 ^ r)) := by
  exact ⟨sequence n hn, sequence_isUlam n hn, sequence_strictMono n hn,
    sequence_infinite n hn, exponential_upper_bound n hn, counting_lower_bound n hn⟩

#print axioms sequence_global_uniqueSum
#print axioms conjecture205
#print axioms counting_lower_bound
#print axioms sequence_unique
#print axioms conjecture_00000000205

end Ulam205Core
