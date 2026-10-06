import Mathlib

/-!
# Conjecture 00000004515: no `(log n)^{1/4}` factor for the planar random Euclidean MST

The conjecture says that the expected total length `E[W_n]` of the Euclidean minimum spanning
tree of `n` iid points of a planar unit region is a constant times `√n (log n)^{1/4}`.

We prove the deterministic strip bound `W_n ≤ 3√n + 2` for any `n ≥ 1` points of `[0,1]²`
(scaled: `W_n ≤ 2R(3√n + 2)` inside `[-R,R]²`), hence `E[W_n] = O(√n)` for every law
concentrated on a bounded set, and `E[W_n] / (c √n (log n)^β) → 0` for every `c` and `β > 0`.
-/

open MeasureTheory Filter Topology Real

namespace C4515

/-- Euclidean distance in the plane `ℝ × ℝ`, written out (Mathlib's `dist` on `ℝ × ℝ` is the
sup metric, so we do not use it). -/
noncomputable def edist2 (p q : ℝ × ℝ) : ℝ := √((p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2)

lemma edist2_comm (p q : ℝ × ℝ) : edist2 p q = edist2 q p := by
  unfold edist2; ring_nf

lemma edist2_nonneg (p q : ℝ × ℝ) : 0 ≤ edist2 p q := Real.sqrt_nonneg _

/-- Length of the edge `s(i, j)` of the complete graph on the labelled points `x`. -/
noncomputable def edgeLen {n : ℕ} (x : Fin n → ℝ × ℝ) : Sym2 (Fin n) → ℝ :=
  Sym2.lift ⟨fun i j => edist2 (x i) (x j), fun _ _ => edist2_comm _ _⟩

lemma edgeLen_nonneg {n : ℕ} (x : Fin n → ℝ × ℝ) (e : Sym2 (Fin n)) : 0 ≤ edgeLen x e := by
  induction e using Sym2.ind with | h i j => exact edist2_nonneg _ _

/-- Total Euclidean length of a graph on the vertex set `Fin n` (vertex `i` sits at `x i`). -/
noncomputable def graphLen {n : ℕ} (x : Fin n → ℝ × ℝ) (G : SimpleGraph (Fin n)) : ℝ := by
  classical exact ∑ e ∈ G.edgeFinset, edgeLen x e

/-- The Euclidean minimum spanning tree length: the minimum, over all spanning trees `T` of the
complete graph on the `n` points, of the total Euclidean length of `T`. -/
noncomputable def mstLen {n : ℕ} (x : Fin n → ℝ × ℝ) : ℝ :=
  ⨅ T : {T : SimpleGraph (Fin n) // T.IsTree}, graphLen x T.1

/-- Expected MST length of `n` iid points with law `μ` (the product measure `μ^n`). -/
noncomputable def expMST (μ : Measure (ℝ × ℝ)) (n : ℕ) : ℝ :=
  ∫ x, mstLen x ∂(Measure.pi fun _ : Fin n => μ)

/-- The conjectured growth profile `√n (log n)^{1/4}` (`Real.log` is the natural logarithm). -/
noncomputable def prof (n : ℕ) : ℝ := √(n : ℝ) * Real.log n ^ (1 / 4 : ℝ)

/-- Reading (asymptotic equivalence): `E[W_n] ~ c √n (log n)^{1/4}`. -/
def AsympReading (μ : Measure (ℝ × ℝ)) (c : ℝ) : Prop :=
  Tendsto (fun n : ℕ => expMST μ n / (c * prof n)) atTop (𝓝 1)

/-- Reading (exact formula): `E[W_n] = c √n (log n)^{1/4}` for all large `n`. -/
def EqReading (μ : Measure (ℝ × ℝ)) (c : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, expMST μ n = c * prof n

/-- Reading (order of growth, exponent `1/4` exact): `E[W_n] = Θ(√n (log n)^{1/4})`. -/
def ThetaReading (μ : Measure (ℝ × ℝ)) : Prop :=
  ∃ c₁ > 0, ∃ c₂ > 0, ∀ᶠ n : ℕ in atTop, c₁ * prof n ≤ expMST μ n ∧ expMST μ n ≤ c₂ * prof n

/-- Weakest lower-bound reading: `E[W_n] ≥ c √n (log n)^{1/4}` for infinitely many `n`. -/
def LowerIOReading (μ : Measure (ℝ × ℝ)) (c : ℝ) : Prop :=
  ∃ᶠ n : ℕ in atTop, c * prof n ≤ expMST μ n

lemma graphLen_nonneg {n : ℕ} (x : Fin n → ℝ × ℝ) (G : SimpleGraph (Fin n)) :
    0 ≤ graphLen x G := by
  classical
  unfold graphLen; exact Finset.sum_nonneg fun e _ => edgeLen_nonneg x e

lemma mstLen_nonneg {n : ℕ} (x : Fin n → ℝ × ℝ) : 0 ≤ mstLen x :=
  Real.iInf_nonneg fun T => graphLen_nonneg x T.1

/-- For `n ≥ 1` the infimum is attained: `mstLen` is a genuine minimum over spanning trees. -/
lemma mstLen_attained {n : ℕ} (hn : 1 ≤ n) (x : Fin n → ℝ × ℝ) :
    ∃ T : SimpleGraph (Fin n), T.IsTree ∧ graphLen x T = mstLen x := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨T, -, hT⟩ := (SimpleGraph.pathGraph_connected m).exists_isTree_le
  have : Nonempty {T : SimpleGraph (Fin (m + 1)) // T.IsTree} := ⟨⟨T, hT⟩⟩
  obtain ⟨T', hT'⟩ := exists_eq_ciInf_of_finite (f := fun T : {T : SimpleGraph (Fin (m + 1)) //
    T.IsTree} => graphLen x T.1)
  exact ⟨T'.1, T'.2, hT'⟩

/-- Any connected graph on the points bounds the MST length (it contains a spanning tree). -/
lemma mstLen_le_of_connected {n : ℕ} (x : Fin n → ℝ × ℝ) {G : SimpleGraph (Fin n)}
    (hG : G.Connected) : mstLen x ≤ graphLen x G := by
  classical
  obtain ⟨T, hle, hT⟩ := hG.exists_isTree_le
  refine (ciInf_le ⟨0, ?_⟩ (⟨T, hT⟩ : {T : SimpleGraph (Fin n) // T.IsTree})).trans ?_
  · rintro _ ⟨T, rfl⟩; exact graphLen_nonneg x T.1
  · unfold graphLen
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun e _ _ => edgeLen_nonneg x e
    intro e he
    rw [SimpleGraph.mem_edgeFinset] at he ⊢
    exact SimpleGraph.edgeSet_mono hle he

/-! ## The strip bound -/

/-- Index of the horizontal strip `[s/k, (s+1)/k]` containing height `y ∈ [0,1]`. -/
noncomputable def strip (k : ℕ) (y : ℝ) : ℕ := min ⌊(k : ℝ) * y⌋₊ (k - 1)

lemma strip_bounds {k : ℕ} (hk : 1 ≤ k) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    (strip k y : ℝ) ≤ k * y ∧ k * y ≤ strip k y + 1 ∧ (strip k y : ℝ) ≤ k - 1 := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h0 : 0 ≤ (k : ℝ) * y := by positivity
  have h1 := Nat.floor_le h0
  have h2 := Nat.lt_floor_add_one ((k : ℝ) * y)
  have hc : ((k - 1 : ℕ) : ℝ) = k - 1 := by push_cast [Nat.cast_sub hk]; ring
  unfold strip
  rcases le_total ⌊(k : ℝ) * y⌋₊ (k - 1) with h | h
  · rw [min_eq_left h]
    have : (⌊(k : ℝ) * y⌋₊ : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by exact_mod_cast h
    exact ⟨h1, h2.le, by linarith⟩
  · rw [min_eq_right h, hc]
    have : ((k - 1 : ℕ) : ℝ) ≤ ⌊(k : ℝ) * y⌋₊ := by exact_mod_cast h
    refine ⟨by linarith, by nlinarith, le_rfl⟩

/-- Sort key: strip index first, then abscissa (`x/2 ∈ [0,1/2]` does not cross strips). -/
noncomputable def key (k : ℕ) (p : ℝ × ℝ) : ℝ := strip k p.2 + p.1 / 2

/-- Unit square `[0,1]²`. -/
def unitSq : Set (ℝ × ℝ) := Set.Icc 0 1 ×ˢ Set.Icc 0 1

lemma edist2_le (p q : ℝ × ℝ) {A B : ℝ} (ha : |q.1 - p.1| ≤ A) (hb : |q.2 - p.2| ≤ B) :
    edist2 p q ≤ A + B := by
  have hA : 0 ≤ A := (abs_nonneg _).trans ha
  have hB : 0 ≤ B := (abs_nonneg _).trans hb
  have h1 : (p.1 - q.1) ^ 2 ≤ A ^ 2 := by
    rw [← sq_abs, abs_sub_comm]; exact pow_le_pow_left₀ (abs_nonneg _) ha 2
  have h2 : (p.2 - q.2) ^ 2 ≤ B ^ 2 := by
    rw [← sq_abs, abs_sub_comm]; exact pow_le_pow_left₀ (abs_nonneg _) hb 2
  exact (Real.sqrt_le_left (by positivity)).2 (by nlinarith [mul_nonneg hA hB])

/-- One step of the sorted path costs at most the increment of `x + (2 + 1/k) s` plus `1/k`. -/
lemma step_le {k : ℕ} (hk : 1 ≤ k) {p q : ℝ × ℝ} (hp : p ∈ unitSq) (hq : q ∈ unitSq)
    (hpq : key k p ≤ key k q) :
    edist2 p q ≤ (q.1 - p.1) + (2 + 1 / k) * ((strip k q.2 : ℝ) - strip k p.2) + 1 / k := by
  obtain ⟨⟨hp1, hp1'⟩, hp2, hp2'⟩ := hp
  obtain ⟨⟨hq1, hq1'⟩, hq2, hq2'⟩ := hq
  have hK : (0 : ℝ) < k := by exact_mod_cast hk
  obtain ⟨a1, a2, -⟩ := strip_bounds hk hp2 hp2'
  obtain ⟨b1, b2, -⟩ := strip_bounds hk hq2 hq2'
  unfold key at hpq
  set s := strip k p.2; set t := strip k q.2
  have hst : s ≤ t := by
    by_contra h
    have : (t : ℝ) + 1 ≤ s := by exact_mod_cast (show t + 1 ≤ s by omega)
    linarith
  have hst' : (s : ℝ) ≤ t := by exact_mod_cast hst
  have hx : |q.1 - p.1| ≤ (q.1 - p.1) + 2 * ((t : ℝ) - s) := by
    rcases eq_or_lt_of_le hst with h | h
    · rw [h] at hpq; rw [h, sub_self, mul_zero, add_zero, abs_of_nonneg (by linarith)]
    · have : (s : ℝ) + 1 ≤ t := by exact_mod_cast h
      rw [abs_le]; constructor <;> linarith
  have hy : |q.2 - p.2| ≤ (((t : ℝ) - s) + 1) / k := by
    rw [le_div_iff₀ hK, ← abs_of_pos hK, ← abs_mul, abs_le]; constructor <;> nlinarith
  calc edist2 p q ≤ ((q.1 - p.1) + 2 * ((t : ℝ) - s)) + (((t : ℝ) - s) + 1) / k :=
        edist2_le p q hx hy
    _ = _ := by field_simp; ring

/-- Arithmetic of the strip bound with `k = ⌊√n⌋ + 1`. -/
lemma strip_arith (m : ℕ) :
    1 + (2 + 1 / ((Nat.sqrt (m + 1) + 1 : ℕ) : ℝ)) * (((Nat.sqrt (m + 1) + 1 : ℕ) : ℝ) - 1) +
      (m : ℝ) / ((Nat.sqrt (m + 1) + 1 : ℕ) : ℝ) ≤ 3 * √((m + 1 : ℕ) : ℝ) + 2 := by
  set K : ℝ := ((Nat.sqrt (m + 1) + 1 : ℕ) : ℝ) with hKdef
  have hK1 : K ≤ √((m + 1 : ℕ) : ℝ) + 1 := by
    have := Real.nat_sqrt_le_real_sqrt (a := m + 1)
    rw [hKdef]; push_cast at this ⊢; linarith
  have hK2 : √((m + 1 : ℕ) : ℝ) ≤ K := by
    have := (Real.real_sqrt_lt_nat_sqrt_succ (a := m + 1)).le
    rw [hKdef]; push_cast at this ⊢; linarith
  have hK0 : 1 ≤ K := by rw [hKdef]; push_cast; linarith [(Nat.sqrt (m + 1)).cast_nonneg (α := ℝ)]
  have hsq : (√((m + 1 : ℕ) : ℝ)) ^ 2 = (m : ℝ) + 1 := by
    rw [Real.sq_sqrt (by positivity)]; push_cast; ring
  have hr0 : 0 ≤ √((m + 1 : ℕ) : ℝ) := Real.sqrt_nonneg _
  rw [← sub_nonneg]
  have : 3 * √((m + 1 : ℕ) : ℝ) + 2 - (1 + (2 + 1 / K) * (K - 1) + m / K) =
      (3 * √((m + 1 : ℕ) : ℝ) * K + 2 * K - (K + (2 * K + 1) * (K - 1) + m)) / K := by
    field_simp
  rw [this]
  apply div_nonneg _ (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left hK1 (by linarith : (0 : ℝ) ≤ K),
    mul_le_mul_of_nonneg_left hK2 hr0]

/-- **Strip bound.** Any `n ≥ 1` points of `[0,1]²` are joined by a connected graph (a path
through the points sorted by strip, then abscissa) of total Euclidean length `≤ 3√n + 2`. -/
theorem exists_connected_short {n : ℕ} (hn : 1 ≤ n) (x : Fin n → ℝ × ℝ)
    (hx : ∀ i, x i ∈ unitSq) :
    ∃ G : SimpleGraph (Fin n), G.Connected ∧ graphLen x G ≤ 3 * √(n : ℝ) + 2 := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  set k := Nat.sqrt (m + 1) + 1 with hk
  have hk1 : 1 ≤ k := by omega
  have hK : (0 : ℝ) < k := by exact_mod_cast hk1
  set σ := Tuple.sort (fun i => key k (x i))
  have hmono := Tuple.monotone_sort (fun i => key k (x i))
  let pos : ℕ → Fin (m + 1) := fun j => ⟨min j m, by omega⟩
  let q : ℕ → ℝ × ℝ := fun j => x (σ (pos j))
  let G := (SimpleGraph.pathGraph (m + 1)).map σ
  refine ⟨G, (SimpleGraph.Iso.map σ _).connected_iff.mp (SimpleGraph.pathGraph_connected m), ?_⟩
  -- every edge of `G` joins two consecutive points of the sorted order
  have hsub : G.edgeFinset ⊆
      (Finset.range m).image (fun j => s(σ (pos j), σ (pos (j + 1)))) := by
    intro e he
    rw [SimpleGraph.mem_edgeFinset] at he
    induction e using Sym2.ind with
    | h u v =>
      rw [SimpleGraph.mem_edgeSet, SimpleGraph.map_adj'] at he
      obtain ⟨-, a, b, hab, rfl, rfl⟩ := he
      rw [SimpleGraph.pathGraph_adj] at hab
      rw [Finset.mem_image]
      rcases hab with h | h
      · refine ⟨a.val, Finset.mem_range.2 (by omega), ?_⟩
        have e1 : pos a.val = a := Fin.ext (by simp [pos]; omega)
        have e2 : pos (a.val + 1) = b := Fin.ext (by simp [pos]; omega)
        rw [e1, e2]
      · refine ⟨b.val, Finset.mem_range.2 (by omega), ?_⟩
        have e1 : pos b.val = b := Fin.ext (by simp [pos]; omega)
        have e2 : pos (b.val + 1) = a := Fin.ext (by simp [pos]; omega)
        rw [e1, e2, Sym2.eq_swap]
  let F : ℕ → ℝ := fun j => (q j).1 + (2 + 1 / k) * (strip k (q j).2 : ℝ) + j / k
  have hstep : ∀ j, edist2 (q j) (q (j + 1)) ≤ F (j + 1) - F j := by
    intro j
    have hle : key k (q j) ≤ key k (q (j + 1)) :=
      hmono (show pos j ≤ pos (j + 1) from Fin.le_iff_val_le_val.2 (by simp [pos]))
    have := step_le hk1 (hx _) (hx _) hle
    simp only [F, q] at this ⊢; push_cast; field_simp at this ⊢; linarith
  calc graphLen x G = ∑ e ∈ G.edgeFinset, edgeLen x e := by
        unfold graphLen; congr 1; ext e; simp only [SimpleGraph.mem_edgeFinset]
    _ ≤ ∑ e ∈ (Finset.range m).image (fun j => s(σ (pos j), σ (pos (j + 1)))), edgeLen x e :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun e _ _ => edgeLen_nonneg x e
    _ ≤ ∑ j ∈ Finset.range m, edgeLen x s(σ (pos j), σ (pos (j + 1))) :=
        Finset.sum_image_le_of_nonneg fun e _ => edgeLen_nonneg x e
    _ = ∑ j ∈ Finset.range m, edist2 (q j) (q (j + 1)) := rfl
    _ ≤ ∑ j ∈ Finset.range m, (F (j + 1) - F j) := Finset.sum_le_sum fun j _ => hstep j
    _ = F m - F 0 := Finset.sum_range_sub F m
    _ ≤ 1 + (2 + 1 / (k : ℝ)) * ((k : ℝ) - 1) + (m : ℝ) / k := by
        obtain ⟨⟨h1, h1'⟩, h2, h2'⟩ := hx (σ (pos m))
        obtain ⟨⟨h3, h3'⟩, h4, h4'⟩ := hx (σ (pos 0))
        obtain ⟨-, -, hs⟩ := strip_bounds hk1 h2 h2'
        have hs0 : (0 : ℝ) ≤ strip k (q 0).2 := Nat.cast_nonneg _
        have hc : (0 : ℝ) ≤ 2 + 1 / k := by positivity
        simp only [F, Nat.cast_zero, zero_div, add_zero]
        nlinarith [mul_le_mul_of_nonneg_left hs hc, mul_nonneg hc hs0]
    _ ≤ 3 * √((m + 1 : ℕ) : ℝ) + 2 := strip_arith m

/-- The deterministic bound: `W_n ≤ 3√n + 2` for any `n ≥ 1` points of the unit square. -/
theorem mstLen_le_unitSq {n : ℕ} (hn : 1 ≤ n) (x : Fin n → ℝ × ℝ) (hx : ∀ i, x i ∈ unitSq) :
    mstLen x ≤ 3 * √(n : ℝ) + 2 := by
  obtain ⟨G, hG, hlen⟩ := exists_connected_short hn x hx
  exact (mstLen_le_of_connected x hG).trans hlen

/-! ## Any bounded region, by translation and scaling -/

/-- The affine map sending the square `[-R,R]²` onto `[0,1]²`. -/
noncomputable def sc (R : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := ((p.1 + R) / (2 * R), (p.2 + R) / (2 * R))

lemma edist2_sc {R : ℝ} (hR : 0 < R) (p q : ℝ × ℝ) :
    edist2 p q = 2 * R * edist2 (sc R p) (sc R q) := by
  unfold edist2 sc
  nth_rewrite 1 [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2 * R)]
  rw [← Real.sqrt_mul (sq_nonneg _)]; congr 1; field_simp; ring

lemma graphLen_sc {R : ℝ} (hR : 0 < R) {n : ℕ} (x : Fin n → ℝ × ℝ) (G : SimpleGraph (Fin n)) :
    graphLen x G = 2 * R * graphLen (fun i => sc R (x i)) G := by
  classical
  unfold graphLen
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  induction e using Sym2.ind with | h i j => exact edist2_sc hR _ _

lemma bounded_sc {S : Set (ℝ × ℝ)} (hS : Bornology.IsBounded S) :
    ∃ R > 0, ∀ p ∈ S, sc R p ∈ unitSq := by
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ × ℝ)).1 hS
  refine ⟨max r 1, by positivity, fun p hp => ?_⟩
  have h := hr hp
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_le, abs_le] at h
  have hR : r ≤ max r 1 := le_max_left _ _
  have hR1 : (0 : ℝ) < max r 1 := by positivity
  unfold sc unitSq
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  all_goals first
    | exact div_nonneg (by linarith) (by positivity)
    | exact (div_le_one (by positivity)).2 (by linarith)

/-- The deterministic bound on a bounded region: `W_n ≤ C (3√n + 2)` with `C` depending only
on the region. -/
theorem mstLen_le_bounded {S : Set (ℝ × ℝ)} (hS : Bornology.IsBounded S) :
    ∃ C, 0 ≤ C ∧ ∀ n, 1 ≤ n → ∀ x : Fin n → ℝ × ℝ, (∀ i, x i ∈ S) →
      mstLen x ≤ C * (3 * √(n : ℝ) + 2) := by
  obtain ⟨R, hR, hsc⟩ := bounded_sc hS
  refine ⟨2 * R, by positivity, fun n hn x hx => ?_⟩
  obtain ⟨G, hG, hlen⟩ := exists_connected_short hn (fun i => sc R (x i)) fun i => hsc _ (hx i)
  calc mstLen x ≤ graphLen x G := mstLen_le_of_connected x hG
    _ = 2 * R * graphLen (fun i => sc R (x i)) G := graphLen_sc hR x G
    _ ≤ 2 * R * (3 * √(n : ℝ) + 2) := mul_le_mul_of_nonneg_left hlen (by positivity)

/-! ## Expectation -/

lemma measurable_mstLen (n : ℕ) : Measurable (fun x : Fin n → ℝ × ℝ => mstLen x) := by
  classical
  unfold mstLen
  refine Measurable.iInf fun T => ?_
  unfold graphLen
  refine Finset.measurable_sum _ fun e _ => ?_
  induction e using Sym2.ind with
  | h i j =>
    simp only [edgeLen, Sym2.lift_mk, edist2]
    exact (by fun_prop : Continuous fun x : Fin n → ℝ × ℝ =>
      √(((x i).1 - (x j).1) ^ 2 + ((x i).2 - (x j).2) ^ 2)).measurable

section Expect

variable (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ] {S : Set (ℝ × ℝ)}
  (hS : Bornology.IsBounded S) (hμ : ∀ᵐ p ∂μ, p ∈ S)
include hS hμ

omit hS in
lemma ae_mem {n : ℕ} : ∀ᵐ x ∂(Measure.pi fun _ : Fin n => μ), ∀ i, x i ∈ S :=
  ae_all_iff.2 fun i => (Measure.quasiMeasurePreserving_eval (fun _ : Fin n => μ) i).ae hμ

/-- `W_n` is integrable, so `expMST μ n` is a genuine (finite) expectation. -/
theorem integrable_mstLen {n : ℕ} (hn : 1 ≤ n) :
    Integrable (fun x : Fin n → ℝ × ℝ => mstLen x) (Measure.pi fun _ : Fin n => μ) := by
  obtain ⟨C, -, hC⟩ := mstLen_le_bounded hS
  refine Integrable.of_bound (measurable_mstLen n).aestronglyMeasurable (C * (3 * √(n : ℝ) + 2)) ?_
  filter_upwards [ae_mem μ hμ] with x hx
  rw [Real.norm_of_nonneg (mstLen_nonneg x)]
  exact hC n hn x hx

/-- `0 ≤ E[W_n] ≤ C (3√n + 2)`. -/
theorem expMST_le : ∃ C, 0 ≤ C ∧ ∀ n, 1 ≤ n →
    0 ≤ expMST μ n ∧ expMST μ n ≤ C * (3 * √(n : ℝ) + 2) := by
  obtain ⟨C, hC0, hC⟩ := mstLen_le_bounded hS
  refine ⟨C, hC0, fun n hn => ⟨integral_nonneg fun x => mstLen_nonneg x, ?_⟩⟩
  have h := integral_mono_of_nonneg (Eventually.of_forall fun x => mstLen_nonneg x)
    (integrable_const (C * (3 * √(n : ℝ) + 2)) (μ := Measure.pi fun _ : Fin n => μ))
    ((ae_mem μ hμ).mono fun x hx => hC n hn x hx)
  simpa [expMST] using h

/-- For every `c` and every exponent `β > 0`, `E[W_n] / (c √n (log n)^β) → 0`. -/
theorem ratio_tendsto_zero {β : ℝ} (hβ : 0 < β) (c : ℝ) :
    Tendsto (fun n : ℕ => expMST μ n / (c * (√(n : ℝ) * Real.log n ^ β))) atTop (𝓝 0) := by
  by_cases hc : c = 0
  · simp [hc]
  obtain ⟨C, hC0, hC⟩ := expMST_le μ hS hμ
  have hL : Tendsto (fun n : ℕ => Real.log n ^ β) atTop atTop :=
    (tendsto_rpow_atTop hβ).comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hlim : Tendsto (fun n : ℕ => (5 * C / |c|) * (Real.log n ^ β)⁻¹) atTop (𝓝 0) := by
    simpa using hL.inv_tendsto_atTop.const_mul (5 * C / |c|)
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 3] with n hn
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hsq : 1 ≤ √(n : ℝ) := Real.one_le_sqrt.2 hn1.le
  have hLβ : 0 < Real.log n ^ β := Real.rpow_pos_of_pos (Real.log_pos hn1) β
  have hca : 0 < |c| := abs_pos.2 hc
  obtain ⟨h0, h1⟩ := hC n (by omega)
  rw [norm_div, Real.norm_of_nonneg h0, norm_mul, norm_mul, Real.norm_eq_abs,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_of_nonneg hLβ.le,
    div_le_iff₀ (by positivity)]
  have : 5 * C / |c| * (Real.log n ^ β)⁻¹ * (|c| * (√(n : ℝ) * Real.log n ^ β)) =
      5 * C * √(n : ℝ) := by field_simp
  rw [this]; nlinarith

/-- The lower bound `E[W_n] ≥ c √n (log n)^β` (`c > 0`, `β > 0`) fails for all large `n`;
it does not even hold for infinitely many `n`. -/
theorem not_frequently_lower {β : ℝ} (hβ : 0 < β) :
    ¬ ∃ c > 0, ∃ᶠ n : ℕ in atTop, c * (√(n : ℝ) * Real.log n ^ β) ≤ expMST μ n := by
  rintro ⟨c, hc, hfr⟩
  have hev := (ratio_tendsto_zero μ hS hμ hβ c).eventually (gt_mem_nhds one_pos)
  obtain ⟨n, hle, hlt, hn⟩ := (hfr.and_eventually (hev.and (eventually_ge_atTop 2))).exists
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hden : 0 < c * (√(n : ℝ) * Real.log n ^ β) :=
    mul_pos hc (mul_pos (Real.sqrt_pos.2 (by linarith)) (Real.rpow_pos_of_pos (Real.log_pos hn1) β))
  rw [div_lt_one hden] at hlt
  linarith

/-- **Main theorem.** For iid points with any law `μ` concentrated on a bounded planar region:
(1) `E[W_n] ~ c √n (log n)^{1/4}` fails for every real `c`;
(2) `E[W_n] = c √n (log n)^{1/4}` for all large `n` fails for every `c > 0`;
(3) `E[W_n] = Θ(√n (log n)^{1/4})` fails;
(4) `E[W_n] ≥ c √n (log n)^{1/4}` for infinitely many `n` fails for every `c > 0`. -/
theorem conjecture_4515_false :
    (∀ c : ℝ, ¬ AsympReading μ c) ∧ (∀ c > 0, ¬ EqReading μ c) ∧ ¬ ThetaReading μ ∧
      (∀ c > 0, ¬ LowerIOReading μ c) := by
  have h4 : ∀ c > 0, ¬ LowerIOReading μ c := fun c hc h =>
    not_frequently_lower μ hS hμ (β := 1 / 4) (by norm_num) ⟨c, hc, h⟩
  refine ⟨fun c h => one_ne_zero (tendsto_nhds_unique h
      (ratio_tendsto_zero μ hS hμ (by norm_num) c)), ?_, ?_, h4⟩
  · intro c hc h; exact h4 c hc (h.mono fun n hn => hn.ge).frequently
  · rintro ⟨c, hc, _, _, h⟩; exact h4 c hc (h.mono fun n hn => hn.1).frequently

end Expect

/-! ## The uniform distribution on the unit square -/

/-- The uniform probability law on `[0,1]²`. -/
noncomputable def uniformSq : Measure (ℝ × ℝ) := volume.restrict unitSq

instance : IsProbabilityMeasure uniformSq :=
  ⟨by
    simp only [uniformSq, unitSq, Measure.restrict_apply_univ, Measure.volume_eq_prod,
      Measure.prod_prod, Real.volume_Icc]
    norm_num⟩

/-- The same four readings fail for `n` iid uniform points of the unit square. -/
theorem conjecture_4515_false_uniform :
    (∀ c : ℝ, ¬ AsympReading uniformSq c) ∧ (∀ c > 0, ¬ EqReading uniformSq c) ∧
      ¬ ThetaReading uniformSq ∧ (∀ c > 0, ¬ LowerIOReading uniformSq c) :=
  conjecture_4515_false uniformSq ((Metric.isBounded_Icc 0 1).prod (Metric.isBounded_Icc 0 1))
    (ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc))

end C4515
