import Mathlib

/-!
# Conjecture 00000000502 is false

Conjecture 00000000502 reads:

> Definition: For the edge ideal `I(G)` of a graph `G`, the regularity of powers `reg I(G)^t` is
> eventually linear in `t`, with slope denoted `a(G)`. Conjecture: For every bipartite graph `G`,
> `a(G) = max{ν(G)−1, ⌈(m(G)+1)/3⌉}`, where `ν(G)` is the matching number and `m(G)` the induced
> matching number; moreover, for chordal bipartite graphs the formula simplifies to `a(G) = ν(G)−1`.

Counterexample: `G = K₂` (one edge), which is bipartite and chordal bipartite (it has no cycles).
`I(K₂)^t = ((x₀x₁)^t)` is free of rank one, generated in degree `2t`, so `reg I(K₂)^t = 2t` for
every `t` and `a(K₂) = 2`. But `ν(K₂) = m(K₂) = 1`, so `max{ν−1, ⌈(m+1)/3⌉} = max{0, 1} = 1 ≠ 2`
and `ν − 1 = 0 ≠ 2`. Both parts fail, over every field `k`.

Definitions (made from scratch where Mathlib has none):
* `edgeIdeal k G = (x_i x_j : G.Adj i j)` in `MvPolynomial V k` (standard grading).
* `GradedFreeRes J`: a finite graded free resolution of the ideal `J` by matrices of homogeneous
  polynomials, exact at `J` and at every `F_i`; `IsMinimal`: all matrix entries lie in `(x_v)`.
* `reg J = max{j − i : β_{i,j}(J) ≠ 0}` read off a minimal graded free resolution, written as the
  infimum over minimal resolutions (all of which have the same shifts) of `max (shift − i)`.
  For `K₂` we prove `reg = 2t` outright: the infimum is attained by `0 → S(−2t) → I^t → 0`, and
  every graded free resolution (minimal or not) has a generator of degree `≥ 2t`.
* `matchingNumber`, `inducedMatchingNumber`: maxima over Mathlib's `Subgraph.IsMatching`
  (with `Subgraph.IsInduced` for induced matchings) of the number of edges.
* Bipartite: Mathlib's `SimpleGraph.IsBipartite` (`Colorable 2`). Chordal bipartite: bipartite and
  every cycle of length `≥ 6` has a chord.
* `HasEventualSlope f a`: `∃ b, ∀ᶠ t, f t = a t + b`.

Main theorem: `C502.conjecture_00000000502_false`.
-/

open MvPolynomial Filter

namespace C502

section Defs

variable {V : Type*} {k : Type*} [Field k]

/-- The edge ideal `I(G) = (x_i x_j : ij ∈ E(G))` of `k[x_v : v ∈ V]`. -/
noncomputable def edgeIdeal (k : Type*) [Field k] (G : SimpleGraph V) : Ideal (MvPolynomial V k) :=
  Ideal.span {p | ∃ i j, G.Adj i j ∧ p = X i * X j}

/-- `p` is homogeneous of integer degree `d` (standard grading, `deg x_v = 1`); the zero polynomial
is homogeneous of every degree, and a nonzero polynomial has no negative degree. -/
def HomogDeg (p : MvPolynomial V k) (d : ℤ) : Prop :=
  p = 0 ∨ ∃ n : ℕ, (n : ℤ) = d ∧ p.IsHomogeneous n

/-- A finite graded free resolution `0 → F_L → ⋯ → F₁ → F₀ → J → 0` of an ideal `J` of
`S = k[x_v]`, with `F_i = ⊕_{b < rank i} S(-shift i b)`. `gen b` is the image in `J` of the `b`-th
basis vector of `F₀`, and `d i` is the matrix of `F_{i+1} → F_i` (entry `(a,b)` homogeneous of
degree `shift (i+1) b - shift i a`). Exactness is required at `J` and at every `F_i`. -/
structure GradedFreeRes (J : Ideal (MvPolynomial V k)) where
  rank : ℕ → ℕ
  shift : (i : ℕ) → Fin (rank i) → ℤ
  gen : Fin (rank 0) → MvPolynomial V k
  d : (i : ℕ) → Matrix (Fin (rank i)) (Fin (rank (i + 1))) (MvPolynomial V k)
  gen_homog : ∀ b, HomogDeg (gen b) (shift 0 b)
  d_homog : ∀ i a b, HomogDeg (d i a b) (shift (i + 1) b - shift i a)
  span_gen : Ideal.span (Set.range gen) = J
  exact_zero : ∀ v : Fin (rank 0) → MvPolynomial V k,
    ∑ b, v b * gen b = 0 ↔ ∃ w, (d 0).mulVec w = v
  exact_succ : ∀ i (v : Fin (rank (i + 1)) → MvPolynomial V k),
    (d i).mulVec v = 0 ↔ ∃ w, (d (i + 1)).mulVec w = v
  finite_length : ∃ L, ∀ i, L < i → rank i = 0

/-- Minimality: every entry of every differential lies in the maximal ideal `(x_v)`. -/
def GradedFreeRes.IsMinimal {J : Ideal (MvPolynomial V k)} (F : GradedFreeRes J) : Prop :=
  ∀ i a b, constantCoeff (F.d i a b) = 0

/-- Castelnuovo–Mumford regularity `reg J = max { j - i : β_{i,j}(J) ≠ 0 }`, read off a minimal
graded free resolution (`β_{i,j}` = number of basis vectors of `F_i` of degree `j`). All minimal
resolutions have the same shifts; the infimum makes the definition choice-free. -/
noncomputable def reg (J : Ideal (MvPolynomial V k)) : ℤ :=
  sInf {r : ℤ | ∃ F : GradedFreeRes J, F.IsMinimal ∧ ∀ i b, F.shift i b - i ≤ r}

/-- Matching number `ν(G)`: the largest number of edges of a matching (Mathlib's
`Subgraph.IsMatching`). -/
noncomputable def matchingNumber (G : SimpleGraph V) : ℕ :=
  sSup {n | ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.ncard = n}

/-- Induced matching number `m(G)`: the largest number of edges of an induced matching, i.e. a
matching that is an induced subgraph. -/
noncomputable def inducedMatchingNumber (G : SimpleGraph V) : ℕ :=
  sSup {n | ∃ M : G.Subgraph, M.IsMatching ∧ M.IsInduced ∧ M.edgeSet.ncard = n}

/-- Chordal bipartite: bipartite, and every cycle of length at least 6 has a chord. -/
def IsChordalBipartite (G : SimpleGraph V) : Prop :=
  G.IsBipartite ∧ ∀ (u : V) (c : G.Walk u u), c.IsCycle → 6 ≤ c.length →
    ∃ x ∈ c.support, ∃ y ∈ c.support, G.Adj x y ∧ s(x, y) ∉ c.edges

/-- `f` is eventually linear in `t` with slope `a`. -/
def HasEventualSlope (f : ℕ → ℤ) (a : ℝ) : Prop :=
  ∃ b : ℝ, ∀ᶠ t in atTop, (f t : ℝ) = a * t + b

end Defs

/-! ### The graph `K₂` -/

section K2

variable (k : Type*) [Field k]

/-- `K₂`: two vertices joined by one edge. -/
abbrev K2 : SimpleGraph (Fin 2) := ⊤

/-- The generator `(x₀ x₁)^t` of `I(K₂)^t`. -/
noncomputable def g (t : ℕ) : MvPolynomial (Fin 2) k := (X 0 * X 1) ^ t

lemma g_ne_zero (t : ℕ) : g k t ≠ 0 :=
  pow_ne_zero _ (mul_ne_zero (X_ne_zero _) (X_ne_zero _))

lemma g_homog (t : ℕ) : (g k t).IsHomogeneous (2 * t) := by
  have := ((isHomogeneous_X k (0 : Fin 2)).mul (isHomogeneous_X k (1 : Fin 2))).pow t
  simpa [g, mul_comm] using this

lemma edgeIdeal_K2 : edgeIdeal k K2 = Ideal.span {X 0 * X 1} := by
  unfold edgeIdeal
  congr 1
  ext p
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, SimpleGraph.top_adj]
  constructor
  · rintro ⟨i, j, hij, rfl⟩
    fin_cases i <;> fin_cases j <;> simp_all [mul_comm]
  · rintro rfl
    exact ⟨0, 1, by decide, rfl⟩

lemma edgeIdeal_K2_pow (t : ℕ) : edgeIdeal k K2 ^ t = Ideal.span {g k t} := by
  rw [edgeIdeal_K2, Ideal.span_singleton_pow, g]

/-- Ranks of the resolution `0 → S(-2t) → I(K₂)^t → 0`. -/
def resRank : ℕ → ℕ
  | 0 => 1
  | _ + 1 => 0

/-- The minimal graded free resolution `0 → S(-2t) → (g) → 0`, `1 ↦ g = (x₀x₁)^t`. -/
noncomputable def res (t : ℕ) : GradedFreeRes (Ideal.span {g k t}) where
  rank := resRank
  shift := fun _ _ => 2 * t
  gen := fun _ => g k t
  d := fun _ _ _ => 0
  gen_homog := fun _ => Or.inr ⟨2 * t, by push_cast; ring, g_homog k t⟩
  d_homog := fun _ _ _ => Or.inl rfl
  span_gen := by
    have : Nonempty (Fin (resRank 0)) := ⟨⟨0, by decide⟩⟩
    rw [show Set.range (fun _ : Fin (resRank 0) => g k t) = {g k t} from Set.range_const]
  exact_zero := by
    intro v
    change (∑ b : Fin 1, v b * g k t = 0) ↔
      ∃ w : Fin 0 → MvPolynomial (Fin 2) k, Matrix.mulVec (fun _ _ => 0) w = v
    rw [Fin.sum_univ_one]
    constructor
    · intro h
      refine ⟨fun b => b.elim0, ?_⟩
      funext b
      fin_cases b
      simp only [Matrix.mulVec, dotProduct, Finset.univ_eq_empty, Finset.sum_empty]
      exact ((mul_eq_zero.1 h).resolve_right (g_ne_zero k t)).symm
    · rintro ⟨w, rfl⟩
      simp [Matrix.mulVec, dotProduct]
  exact_succ := by
    intro i v
    constructor
    · intro _; exact ⟨fun b => b.elim0, funext fun b => b.elim0⟩
    · intro _; funext a; simp [Matrix.mulVec, dotProduct]
  finite_length := ⟨0, fun i hi => by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hi; rfl⟩

lemma res_minimal (t : ℕ) : (res k t).IsMinimal := fun _ _ _ => by simp [res]

/-- Lower bound: in every graded free resolution of `(g)`, `F₀` has a basis vector of degree
`≥ 2t`, because `(g)` has no nonzero homogeneous element of degree `< 2t`. -/
lemma shift_lower_bound (t : ℕ) (F : GradedFreeRes (Ideal.span {g k t})) :
    ∃ b, 2 * (t : ℤ) ≤ F.shift 0 b := by
  by_contra hcon
  simp only [not_exists, not_le] at hcon
  have hzero : ∀ b, F.gen b = 0 := by
    intro b
    rcases F.gen_homog b with h | ⟨n, hn, hh⟩
    · exact h
    by_contra hne
    have hmem := Ideal.subset_span (α := MvPolynomial (Fin 2) k) (s := Set.range F.gen) ⟨b, rfl⟩
    rw [F.span_gen] at hmem
    have hdvd : g k t ∣ F.gen b := Ideal.mem_span_singleton.1 hmem
    have h1 := totalDegree_le_of_dvd_of_isDomain hdvd hne
    rw [(g_homog k t).totalDegree (g_ne_zero k t), hh.totalDegree hne] at h1
    have := hcon b
    omega
  have : Ideal.span {g k t} = ⊥ := by
    rw [← F.span_gen, Ideal.span_eq_bot]
    rintro _ ⟨b, rfl⟩
    exact hzero b
  exact g_ne_zero k t (by
    have hm : g k t ∈ Ideal.span {g k t} := Ideal.subset_span rfl
    rw [this] at hm
    exact hm)

/-- `reg I(K₂)^t = 2t` for every `t`. -/
theorem reg_K2_pow (t : ℕ) : reg (edgeIdeal k K2 ^ t) = 2 * t := by
  rw [edgeIdeal_K2_pow]
  apply IsLeast.csInf_eq
  refine ⟨⟨res k t, res_minimal k t, fun i b => by simp [res]⟩, ?_⟩
  rintro r ⟨F, -, hF⟩
  obtain ⟨b, hb⟩ := shift_lower_bound k t F
  have := hF 0 b
  simp at this
  omega

/-! ### Graph invariants of `K₂` -/

lemma K2_edgeSet : K2.edgeSet = {s(0, 1)} := by
  ext e
  induction e using Sym2.ind with
  | h x y => fin_cases x <;> fin_cases y <;> simp [Sym2.eq_swap]

lemma K2_edgeSet_ncard : K2.edgeSet.ncard = 1 := by
  rw [K2_edgeSet, Set.ncard_singleton]

lemma top_isMatching : (⊤ : K2.Subgraph).IsMatching := by
  intro v _
  fin_cases v
  · exact ⟨1, by simp, fun y hy => by fin_cases y <;> simp_all⟩
  · exact ⟨0, by simp, fun y hy => by fin_cases y <;> simp_all⟩

lemma top_isInduced : (⊤ : K2.Subgraph).IsInduced := fun _ _ _ _ h => by simpa using h

lemma ncard_le_one (M : K2.Subgraph) : M.edgeSet.ncard ≤ 1 :=
  K2_edgeSet_ncard ▸ Set.ncard_le_ncard M.edgeSet_subset (Set.toFinite _)

lemma top_ncard : (⊤ : K2.Subgraph).edgeSet.ncard = 1 := by
  rw [SimpleGraph.Subgraph.edgeSet_top, K2_edgeSet_ncard]

/-- `ν(K₂) = 1`. -/
theorem matchingNumber_K2 : matchingNumber K2 = 1 :=
  IsGreatest.csSup_eq ⟨⟨⊤, top_isMatching, top_ncard⟩, by
    rintro n ⟨M, -, rfl⟩; exact ncard_le_one M⟩

/-- `m(K₂) = 1`. -/
theorem inducedMatchingNumber_K2 : inducedMatchingNumber K2 = 1 :=
  IsGreatest.csSup_eq ⟨⟨⊤, top_isMatching, top_isInduced, top_ncard⟩, by
    rintro n ⟨M, -, -, rfl⟩; exact ncard_le_one M⟩

/-- `K₂` is bipartite (a proper 2-colouring is the identity). -/
theorem K2_isBipartite : K2.IsBipartite :=
  ⟨SimpleGraph.Coloring.mk id fun h => by simpa using h⟩

/-- `K₂` has no cycles at all (a cycle has `≥ 3` distinct vertices), so it is chordal
bipartite. -/
theorem K2_isChordalBipartite : IsChordalBipartite K2 := by
  refine ⟨K2_isBipartite, fun u c hc _ => ?_⟩
  exfalso
  have h3 := hc.three_le_length
  have hnd := hc.support_nodup
  have hlen := hnd.length_le_card
  rw [List.length_tail, SimpleGraph.Walk.length_support, Fintype.card_fin] at hlen
  omega

/-- `I(K₂) ≠ 0`. -/
theorem edgeIdeal_K2_ne_bot : edgeIdeal k K2 ≠ ⊥ := by
  rw [edgeIdeal_K2, Ne, Ideal.span_singleton_eq_bot]
  exact mul_ne_zero (X_ne_zero _) (X_ne_zero _)

/-! ### Slopes -/

/-- If `f t = 2t` for all `t`, then the eventual slope of `f` is `2` and nothing else. -/
lemma hasEventualSlope_iff_of_eq (f : ℕ → ℤ) (hf : ∀ t, f t = 2 * t) (a : ℝ) :
    HasEventualSlope f a ↔ a = 2 := by
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨N, hN⟩ := eventually_atTop.1 hb
    have h1 := hN N le_rfl
    have h2 := hN (N + 1) (Nat.le_succ N)
    rw [hf] at h1 h2
    push_cast at h1 h2
    linarith
  · rintro rfl
    exact ⟨0, Eventually.of_forall fun t => by rw [hf]; push_cast; ring⟩

/-- `reg I(K₂)^t` is eventually linear with slope exactly `2`: `a(K₂) = 2`. -/
theorem slope_K2 (a : ℝ) : HasEventualSlope (fun t => reg (edgeIdeal k K2 ^ t)) a ↔ a = 2 :=
  hasEventualSlope_iff_of_eq _ (reg_K2_pow k) a

end K2

/-! ### The conjecture and its refutation -/

/-- The general formula: for every finite bipartite graph `G` with `I(G) ≠ 0`, the eventual slope
`a(G)` of `t ↦ reg I(G)^t` equals `max{ν(G) - 1, ⌈(m(G)+1)/3⌉}`. -/
def GeneralFormula (k : Type) [Field k] : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.IsBipartite → edgeIdeal k G ≠ ⊥ →
    HasEventualSlope (fun t => reg (edgeIdeal k G ^ t))
      (max ((matchingNumber G : ℝ) - 1) (⌈((inducedMatchingNumber G : ℝ) + 1) / 3⌉ : ℝ))

/-- The chordal bipartite specialization: for every finite chordal bipartite graph `G` with
`I(G) ≠ 0`, `a(G) = ν(G) - 1`. -/
def ChordalFormula (k : Type) [Field k] : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), IsChordalBipartite G → edgeIdeal k G ≠ ⊥ →
    HasEventualSlope (fun t => reg (edgeIdeal k G ^ t)) ((matchingNumber G : ℝ) - 1)

/-- Conjecture 00000000502: both formulas, over the field `k`. -/
def Conjecture (k : Type) [Field k] : Prop := GeneralFormula k ∧ ChordalFormula k

lemma formula_K2 :
    max ((matchingNumber K2 : ℝ) - 1) (⌈((inducedMatchingNumber K2 : ℝ) + 1) / 3⌉ : ℝ) = 1 := by
  rw [matchingNumber_K2, inducedMatchingNumber_K2]
  norm_num [show ⌈(2:ℝ) / 3⌉ = 1 by rw [Int.ceil_eq_iff]; norm_num]

/-- The general formula fails (at `G = K₂`, `a = 2 ≠ 1`), over every field. -/
theorem generalFormula_false (k : Type) [Field k] : ¬ GeneralFormula k := by
  intro h
  have := h (Fin 2) K2 K2_isBipartite (edgeIdeal_K2_ne_bot k)
  rw [formula_K2, slope_K2] at this
  norm_num at this

/-- The chordal bipartite formula fails (at `G = K₂`, `a = 2 ≠ 0 = ν - 1`), over every field. -/
theorem chordalFormula_false (k : Type) [Field k] : ¬ ChordalFormula k := by
  intro h
  have := h (Fin 2) K2 K2_isChordalBipartite (edgeIdeal_K2_ne_bot k)
  rw [matchingNumber_K2, slope_K2] at this
  norm_num at this

/-- **Main theorem.** Conjecture 00000000502 is false over every field `k`: for the bipartite (and
chordal bipartite) graph `K₂` one has `reg I(K₂)^t = 2t` for all `t`, so `a(K₂) = 2`, while
`max{ν - 1, ⌈(m+1)/3⌉} = 1` and `ν - 1 = 0`. Both parts fail separately. -/
theorem conjecture_00000000502_false (k : Type) [Field k] :
    ¬ GeneralFormula k ∧ ¬ ChordalFormula k ∧ ¬ Conjecture k :=
  ⟨generalFormula_false k, chordalFormula_false k, fun h => generalFormula_false k h.1⟩

/-- The general formula also fails if `a(G)` is misread as the constant term `b` in
`reg I(G)^t = 2t + b` (eventually): for `K₂`, `b = 0 ≠ 1`. -/
theorem constant_term_reading_false (k : Type) [Field k] :
    ¬ ∀ᶠ t : ℕ in atTop, (reg (edgeIdeal k K2 ^ t) : ℝ) = 2 * (t : ℝ) +
      max ((matchingNumber K2 : ℝ) - 1) (⌈((inducedMatchingNumber K2 : ℝ) + 1) / 3⌉ : ℝ) := by
  rw [formula_K2]
  intro h
  obtain ⟨t, ht⟩ := h.exists
  rw [reg_K2_pow] at ht
  push_cast at ht
  linarith

end C502
