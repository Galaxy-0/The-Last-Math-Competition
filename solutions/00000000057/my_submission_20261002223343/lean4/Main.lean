/-
  Disproof of TLMC conjecture 00000000057.

  Conjecture: "Every n-vertex graph of minimum degree at least 3 contains
  Omega(log n / log log n) cycles of pairwise distinct prime lengths."

  Counterexample family, for ALL k >= 1 (hence for arbitrarily large
  n = 6k): the disjoint union G_k of k copies of K_{3,3}.

    * G_k is 3-regular: every vertex has three pairwise distinct
      neighbors (kernel-certified for every k);
    * G_k is bipartite: each vertex gets color 0 (left part of its
      K_{3,3}) or 1 (right part), and every edge joins opposite colors,
      i.e. the two endpoint colors sum to 1;
    * any cycle of G_k, read in order, returns to its start, so its
      length p is even (kernel-certified by an even-steps induction for
      every k and every such cycle);
    * a cycle has length >= 3 by definition, and the only even prime
      is 2, so G_k contains NO cycle of prime length: the number of
      distinct prime cycle lengths is exactly 0 for every k;
    * since log n / log log n -> infinity, any Omega(log n / log log n)
      lower bound demands a positive count for all sufficiently large
      n; the family G_k (n = 6k -> infinity) has count 0 for every k,
      refuting the conjecture.  (This last standard calculus reduction
      is the only non-kernel step and is stated in prose; everything
      about the graphs is uniform in k — no finite instance is used as
      evidence for the asymptotic claim.)

  Definitions used: `Prime` is the standard primality predicate; a
  cycle of length p is a sequence of p >= 3 pairwise distinct vertices
  with consecutive vertices adjacent, and the last vertex adjacent to
  the first.

  The proofs are structural (case analyses and inductions over Nat),
  with closed numeric facts by `decide`; no axioms are used anywhere.
-/

namespace Tlmc0057

/-! ## The graph family `G_k` : k disjoint copies of K_{3,3}. -/

/-- Vertices: (copy, position); position 0-2 = left part, 3-5 = right
    part of the bipartition of that copy.  `G_k` has 6k vertices. -/
def Vtx (k : Nat) := Fin k × Fin 6

/-- A vertex's color: 0 = left part, 1 = right part. -/
def col {k : Nat} (v : Vtx k) : Nat := if v.2.val < 3 then 0 else 1

/-- Adjacency: same copy, opposite sides of the bipartition. -/
def adj {k : Nat} (a b : Vtx k) : Prop :=
  a.1 = b.1 ∧ ((a.2.val < 3 ∧ 3 ≤ b.2.val) ∨ (3 ≤ a.2.val ∧ b.2.val < 3))

/-- Every edge joins opposite colors: the endpoint colors sum to 1. -/
theorem adj_sum {k : Nat} {a b : Vtx k} (h : adj a b) : col a + col b = 1 := by
  unfold col
  rcases h.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [if_pos h1, if_neg (fun hlt => Nat.lt_irrefl 3 (Nat.lt_of_le_of_lt h2 hlt))]
  · rw [if_neg (fun hlt => Nat.lt_irrefl 3 (Nat.lt_of_le_of_lt h1 hlt)), if_pos h2]

/-! ## Minimum degree three, for every k. -/

/-- Every vertex of G_k has three pairwise distinct neighbors, so the
    minimum degree is at least 3 (indeed G_k is 3-regular). -/
theorem three_distinct_neighbors {k : Nat} (v : Vtx k) :
    ∃ a b c : Vtx k, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ adj v a ∧ adj v b ∧ adj v c := by
  rcases Nat.lt_or_ge v.2.val 3 with h | h
  · refine ⟨(v.1, (⟨3, by decide⟩ : Fin 6)), (v.1, (⟨4, by decide⟩ : Fin 6)),
      (v.1, (⟨5, by decide⟩ : Fin 6)), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro he; exact absurd (congrArg (fun x => x.2.val) he) (by show ¬ ((3:Nat) = 4); decide)
    · intro he; exact absurd (congrArg (fun x => x.2.val) he) (by show ¬ ((3:Nat) = 5); decide)
    · intro he; exact absurd (congrArg (fun x => x.2.val) he) (by show ¬ ((4:Nat) = 5); decide)
    · exact ⟨rfl, Or.inl ⟨h, by show (3:Nat) ≤ 3; decide⟩⟩
    · exact ⟨rfl, Or.inl ⟨h, by show (3:Nat) ≤ 4; decide⟩⟩
    · exact ⟨rfl, Or.inl ⟨h, by show (3:Nat) ≤ 5; decide⟩⟩
  · refine ⟨(v.1, (⟨0, by decide⟩ : Fin 6)), (v.1, (⟨1, by decide⟩ : Fin 6)),
      (v.1, (⟨2, by decide⟩ : Fin 6)), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro he; exact absurd (congrArg (fun x => x.2.val) he) (by show ¬ ((0:Nat) = 1); decide)
    · intro he; exact absurd (congrArg (fun x => x.2.val) he) (by show ¬ ((0:Nat) = 2); decide)
    · intro he; exact absurd (congrArg (fun x => x.2.val) he) (by show ¬ ((1:Nat) = 2); decide)
    · exact ⟨rfl, Or.inr ⟨h, by show (0:Nat) < 3; decide⟩⟩
    · exact ⟨rfl, Or.inr ⟨h, by show (1:Nat) < 3; decide⟩⟩
    · exact ⟨rfl, Or.inr ⟨h, by show (2:Nat) < 3; decide⟩⟩

/-! ## Cycles and primality. -/

/-- Standard primality. -/
def Prime (p : Nat) : Prop := 2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p

/-- `HasPrimeCycle k` : G_k contains a cycle of prime length.  A cycle
    of length p is a sequence of p >= 3 PAIRWISE DISTINCT vertices with
    consecutive vertices adjacent, and the last adjacent to the first. -/
def HasPrimeCycle (k : Nat) : Prop :=
  ∃ (p : Nat) (w : Nat → Vtx k), 3 ≤ p ∧ Prime p ∧
    (∀ i j, i < p → j < p → w i = w j → i = j) ∧
    (∀ i, i + 1 < p → adj (w i) (w (i + 1))) ∧
    adj (w (p - 1)) (w 0)

/-! ## Parity machinery, axiom-free. -/

/-- Right cancellation for Nat addition, by induction (the core lemma
    `Nat.add_right_cancel` is proved with `propext`, so we reprove it). -/
theorem add_right_cancel' (c : Nat) {n m : Nat} (h : n + c = m + c) : n = m := by
  induction c with
  | zero => exact h
  | succ c' ih =>
      have h' : n + Nat.succ c' = m + Nat.succ c' := h
      exact ih (Nat.succ.inj h')

/-- Transitivity of `<`, via `≤` (the core lemma `Nat.lt_trans` may be
    tainted; this reproof uses only clean order lemmas). -/
theorem lt_trans' {a b c : Nat} (h1 : a < b) (h2 : b < c) : a < c :=
  Nat.le_trans (Nat.le_trans h1 (Nat.le_succ b)) h2

/-- Two steps along a walk return to the same color: the two color-sum
    equations share a summand, and Nat addition is cancellative. -/
theorem two_step_same {k : Nat} {p : Nat} (v : Nat → Vtx k)
    (hadj : ∀ i, i + 1 < p → adj (v i) (v (i + 1))) :
    ∀ i, i + 2 < p → col (v (i + 2)) = col (v i) := by
  intro i hi
  have h1 : i + 1 < p := lt_trans' (Nat.lt_succ_self (i + 1)) hi
  have e1 := adj_sum (hadj i h1)
  have e2 := adj_sum (hadj (i + 1) hi)
  have h12 : col (v i) + col (v (i+1)) = col (v (i+2)) + col (v (i+1)) :=
    Eq.trans (Eq.trans e1 e2.symm)
      (Nat.add_comm (col (v (i+1))) (col (v (i+2))))
  exact (add_right_cancel' _ h12).symm

/-- Even-indexed vertices of a walk lie on the same color. -/
theorem even_steps_same {k : Nat} {p : Nat} (v : Nat → Vtx k)
    (hadj : ∀ i, i + 1 < p → adj (v i) (v (i + 1))) :
    ∀ m, 2 * m < p → col (v (2 * m)) = col (v 0) := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
      intro hlt
      have h2 : 2 * m + 2 < p := hlt
      have hprev : 2 * m < p :=
        Nat.lt_trans (Nat.lt_trans (Nat.lt_succ_self (2*m))
          (Nat.lt_succ_self (2*m+1))) h2
      have ts := two_step_same v hadj (2 * m) h2
      rw [Nat.mul_succ, ts, ih hprev]

/-- Transport of colors along equal indices. -/
theorem col_transport {k : Nat} {x y : Nat} (h : x = y) (v : Nat → Vtx k) :
    col (v x) = col (v y) := by
  rw [h]

/-- Parity dichotomy without arithmetic automation. -/
theorem parity (p : Nat) : (∃ m, p = 2 * m) ∨ (∃ m, p = 2 * m + 1) := by
  induction p with
  | zero => exact Or.inl ⟨0, rfl⟩
  | succ p ih =>
      rcases ih with ⟨m, hm⟩ | ⟨m, hm⟩
      · exact Or.inr ⟨m, by rw [hm]⟩
      · exact Or.inl ⟨m + 1, by rw [hm, Nat.mul_succ]⟩

/-- `c + c = 1` is impossible in Nat. -/
theorem add_self_ne_one (c : Nat) : ¬ (c + c = 1) := by
  intro h
  have hle : c ≤ c + c := Nat.le_add_right c c
  rw [h] at hle
  cases c with
  | zero => exact Nat.zero_ne_one h
  | succ c' =>
      have hle0 : c' = 0 := Nat.le_zero.mp (Nat.le_of_succ_le_succ hle)
      subst hle0
      exact absurd h (by show ¬ ((1:Nat) + 1 = 1); decide)

/-! ## Main graph-theoretic theorem: no prime cycle, for every k. -/

theorem no_prime_cycle (k : Nat) : ¬ HasPrimeCycle k := by
  rintro ⟨p, w, hp3, hprime, _hdist, hadj, hclose⟩
  rcases parity p with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- p = 2m is even: a prime divisible by 2 must be 2 < 3
    have hdvd : 2 ∣ p := ⟨m, hm⟩
    rcases hprime.2 2 hdvd with h | h
    · exact absurd h (by decide)
    · have hle : (3:Nat) ≤ 2 := by rw [h]; exact hp3
      exact absurd hle (by decide)
  · -- p = 2m+1 is odd: the closing edge contradicts color alternation
    have hlt : 2 * m < p := by rw [hm]; exact Nat.lt_succ_self (2 * m)
    have hstart : col (w (2*m)) = col (w 0) := even_steps_same w hadj m hlt
    have hpm : p - 1 = 2 * m := by rw [hm]; rfl
    have hc : col (w (p-1)) = col (w (2*m)) := col_transport hpm w
    have hfull : col (w (p-1)) = col (w 0) := hc.trans hstart
    have e : col (w (p-1)) + col (w 0) = 1 := adj_sum hclose
    have step1 : col (w (p-1)) + col (w 0) = col (w 0) + col (w 0) :=
      congrArg (fun t => t + col (w 0)) hfull
    exact add_self_ne_one (col (w 0)) (Eq.trans step1.symm e)

/-! ## The refutation: the family is unbounded in n. -/

/-- For every bound N there is a member of the family beyond it: a
    graph on 6k >= 6(N+1) vertices, of minimum degree at least 3, with
    ZERO cycles of prime length.  Since log n / log log n -> infinity,
    an Omega(log n / log log n) lower bound on the number of distinct
    prime cycle lengths would in particular be positive for all large
    n; it is 0 for every member of this family. -/
theorem conjecture_refuted : ∀ N : Nat,
    ∃ k, N ≤ k ∧
      (∀ v : Vtx k, ∃ a b c : Vtx k, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
        adj v a ∧ adj v b ∧ adj v c) ∧
      ¬ HasPrimeCycle k := by
  intro N
  exact ⟨N + 1, Nat.le_succ N, fun v => three_distinct_neighbors v,
    no_prime_cycle _⟩

end Tlmc0057
