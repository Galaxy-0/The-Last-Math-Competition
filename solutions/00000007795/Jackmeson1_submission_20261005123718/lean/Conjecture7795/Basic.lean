import Mathlib

/-!
# Conjecture 00000007795: the Lipschitz clause is false

Conjecture (verbatim): "Definition: Regularity stratification of lattice counting: the error
E(t) = |tP intersect Z^n| - t^n vol(P) for the dilation tP. Conjecture: The optimal error for
Lipschitz boundaries is O(t^{n-2+1/3}) and for C^2 boundaries O(t^{n-2}); no intermediate regularity
exists between the exponents 1/3 and 0 (...), the jump location being jointly determined by Fourier
damping and the Diophantine properties of the lattice."

We refute the first conjunct (the Lipschitz clause). The witness is the closed unit square
`P = [0,1]²` in the Euclidean plane: it is compact and convex, has nonempty interior and a Lipschitz
boundary, and for every integer `m ≥ 1` the lattice count is `(m+1)²` and `vol P = 1`, so
`E(m) = 2m + 1`, which is not `O(m^{1/3})`.

**Lipschitz boundary** (local Lipschitz-graph definition, with a rotated frame allowed): for every
boundary point `x₀` there are `r > 0`, a unit vector `v` (the last axis of an orthonormal frame) and a
Lipschitz function `φ` of the coordinates orthogonal to `v` with
`P ∩ B(x₀, r) = {x ∈ B(x₀, r) : ⟪x, v⟫ ≤ φ(x)}`. "Function of the orthogonal coordinates" is
encoded as `φ : ℝⁿ → ℝ` that is constant along `v`: `φ (x + s • v) = φ x`.
-/

open MeasureTheory Filter Asymptotics Set
open scoped RealInnerProductSpace NNReal Pointwise

namespace C7795

/-- Euclidean space `ℝⁿ`. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- `P` has Lipschitz boundary: near each boundary point, `P` is the region below the graph of a
Lipschitz function over the hyperplane orthogonal to some unit vector `v`. -/
def HasLipschitzBoundary {n : ℕ} (P : Set (E n)) : Prop :=
  ∀ x₀ ∈ frontier P, ∃ r > (0 : ℝ), ∃ v : E n, ‖v‖ = 1 ∧ ∃ L : ℝ≥0, ∃ φ : E n → ℝ,
    LipschitzWith L φ ∧ (∀ x : E n, ∀ s : ℝ, φ (x + s • v) = φ x) ∧
    P ∩ Metric.ball x₀ r = {x | x ∈ Metric.ball x₀ r ∧ ⟪x, v⟫ ≤ φ x}

/-- The number of points of `ℤⁿ` in `S`. -/
noncomputable def latticeCount {n : ℕ} (S : Set (E n)) : ℕ :=
  Set.ncard {z : Fin n → ℤ | WithLp.toLp 2 (fun i => (z i : ℝ)) ∈ S}

/-- The lattice-point error `E(t) = |tP ∩ ℤⁿ| - tⁿ vol(P)`. -/
noncomputable def discrepancy {n : ℕ} (P : Set (E n)) (t : ℝ) : ℝ :=
  (latticeCount (t • P) : ℝ) - t ^ n * (volume P).toReal

/-- The Lipschitz clause, for real dilation parameter `t → ∞`: every compact body with nonempty
interior and Lipschitz boundary has `E(t) = O(t^{n-2+1/3})`. -/
def LipschitzClause : Prop :=
  ∀ n : ℕ, ∀ P : Set (E n), IsCompact P → (interior P).Nonempty → HasLipschitzBoundary P →
    discrepancy P =O[atTop] fun t : ℝ => t ^ ((n : ℝ) - 2 + 1 / 3)

/-- The Lipschitz clause for integer dilations `t = m ∈ ℕ`, `m → ∞`. -/
def LipschitzClauseNat : Prop :=
  ∀ n : ℕ, ∀ P : Set (E n), IsCompact P → (interior P).Nonempty → HasLipschitzBoundary P →
    (fun m : ℕ => discrepancy P m) =O[atTop] fun m : ℕ => (m : ℝ) ^ ((n : ℝ) - 2 + 1 / 3)

/-- The closed unit square `[0,1]²`. -/
def unitSquare : Set (E 2) := {x | ∀ i, 0 ≤ x i ∧ x i ≤ 1}

lemma mem_unitSquare (x : E 2) :
    x ∈ unitSquare ↔ (0 ≤ x 0 ∧ x 0 ≤ 1) ∧ (0 ≤ x 1 ∧ x 1 ≤ 1) := by
  simp [unitSquare, Fin.forall_fin_two]

lemma abs_coord_sub_le (x y : E 2) (i : Fin 2) : |x i - y i| ≤ dist x y := by
  have := PiLp.dist_apply_le x y i
  rwa [Real.dist_eq] at this

/-! ### The square is a compact convex body with nonempty interior -/

lemma unitSquare_eq_image :
    unitSquare = WithLp.toLp 2 '' (Set.pi univ fun _ : Fin 2 => Icc (0 : ℝ) 1) := by
  ext x
  constructor
  · intro hx; exact ⟨WithLp.ofLp x, fun i _ => hx i, rfl⟩
  · rintro ⟨f, hf, rfl⟩ i; exact hf i (mem_univ i)

lemma isCompact_unitSquare : IsCompact unitSquare := by
  rw [unitSquare_eq_image]
  exact (isCompact_univ_pi fun _ => isCompact_Icc).image (PiLp.continuous_toLp 2 _)

lemma convex_unitSquare : Convex ℝ unitSquare := by
  intro x hx y hy a b ha hb hab i
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  obtain ⟨hx0, hx1⟩ := hx i
  obtain ⟨hy0, hy1⟩ := hy i
  constructor <;> nlinarith

lemma interior_unitSquare_nonempty : (interior unitSquare).Nonempty := by
  refine ⟨WithLp.toLp 2 (fun _ => (1 / 2 : ℝ)), mem_interior_iff_mem_nhds.mpr ?_⟩
  refine Metric.mem_nhds_iff.mpr ⟨1 / 2, by norm_num, fun x hx i => ?_⟩
  have h := abs_coord_sub_le x (WithLp.toLp 2 (fun _ => (1 / 2 : ℝ))) i
  rw [Metric.mem_ball] at hx
  simp only at h
  constructor <;> linarith [abs_le.mp (h.trans hx.le)]

/-! ### The square has Lipschitz boundary -/

/-- A corner chart: if, inside `B(x₀, r)`, the constraints of the square reduce to `a x₀ ≤ cA` and
`b x₁ ≤ cB` with `a, b = ±1`, then the square is a Lipschitz subgraph in direction `(a, b)/√2`. -/
lemma corner_chart (x₀ : E 2) (r : ℝ) (a b cA cB : ℝ) (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (hA : ∀ x ∈ Metric.ball x₀ r, (0 ≤ x 0 ∧ x 0 ≤ 1 ↔ a * x 0 ≤ cA))
    (hB : ∀ x ∈ Metric.ball x₀ r, (0 ≤ x 1 ∧ x 1 ≤ 1 ↔ b * x 1 ≤ cB)) :
    ∃ v : E 2, ‖v‖ = 1 ∧ ∃ L : ℝ≥0, ∃ φ : E 2 → ℝ,
      LipschitzWith L φ ∧ (∀ x : E 2, ∀ s : ℝ, φ (x + s • v) = φ x) ∧
      unitSquare ∩ Metric.ball x₀ r = {x | x ∈ Metric.ball x₀ r ∧ ⟪x, v⟫ ≤ φ x} := by
  have hs : 0 < √2 := by positivity
  have hs2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs1 : 1 ≤ √2 := by rw [Real.one_le_sqrt]; norm_num
  let v : E 2 := WithLp.toLp 2 ![a / √2, b / √2]
  let φ : E 2 → ℝ := fun x => (cA + cB - |a * x 0 - b * x 1 - cA + cB|) / √2
  have ha' : |a| = 1 := by
    have := sq_abs a; rw [ha] at this; nlinarith [abs_nonneg a]
  have hb' : |b| = 1 := by
    have := sq_abs b; rw [hb] at this; nlinarith [abs_nonneg b]
  refine ⟨v, ?_, 2, φ, ?_, ?_, ?_⟩
  · rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one]
    simp only [v, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Real.norm_eq_abs, sq_abs, div_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), ha, hb]
    norm_num
  · refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq]
    have h0 := abs_coord_sub_le x y 0
    have h1 := abs_coord_sub_le x y 1
    have key : |(a * x 0 - b * x 1 - cA + cB) - (a * y 0 - b * y 1 - cA + cB)| ≤ 2 * dist x y := by
      have : (a * x 0 - b * x 1 - cA + cB) - (a * y 0 - b * y 1 - cA + cB)
          = a * (x 0 - y 0) - b * (x 1 - y 1) := by ring
      rw [this]
      calc |a * (x 0 - y 0) - b * (x 1 - y 1)| ≤ |a * (x 0 - y 0)| + |b * (x 1 - y 1)| :=
            abs_sub _ _
        _ = |x 0 - y 0| + |x 1 - y 1| := by rw [abs_mul, abs_mul, ha', hb', one_mul, one_mul]
        _ ≤ 2 * dist x y := by linarith
    have e : φ x - φ y = (|a * y 0 - b * y 1 - cA + cB| - |a * x 0 - b * x 1 - cA + cB|) / √2 := by
      simp only [φ]; ring
    rw [e, abs_div, abs_of_pos hs, div_le_iff₀ hs]
    have h3 := abs_abs_sub_abs_le_abs_sub (a * y 0 - b * y 1 - cA + cB) (a * x 0 - b * x 1 - cA + cB)
    rw [abs_sub_comm (a * y 0 - b * y 1 - cA + cB)] at h3
    have hd : 0 ≤ dist x y := dist_nonneg
    push_cast
    nlinarith
  · intro x s
    simp only [φ, v, PiLp.add_apply, PiLp.smul_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, smul_eq_mul]
    congr 3
    have : a * (s * (a / √2)) - b * (s * (b / √2)) = s * (a ^ 2 - b ^ 2) / √2 := by ring
    rw [show a * (x 0 + s * (a / √2)) - b * (x 1 + s * (b / √2)) - cA + cB
        = (a * x 0 - b * x 1 - cA + cB) + (a * (s * (a / √2)) - b * (s * (b / √2))) by ring,
      this, ha, hb]
    simp
  · ext x
    simp only [mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hxP, hxB⟩
      refine ⟨hxB, ?_⟩
      rw [mem_unitSquare] at hxP
      have hX := (hA x hxB).mp hxP.1
      have hY := (hB x hxB).mp hxP.2
      have hin : ⟪x, v⟫ = (a * x 0 + b * x 1) / √2 := by
        simp only [v, PiLp.inner_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
          Matrix.cons_val_one, RCLike.inner_apply, conj_trivial]
        ring
      rw [hin]
      apply div_le_div_of_nonneg_right _ hs.le
      have := abs_le.mpr (⟨by linarith, by linarith⟩ :
        -(cA + cB - (a * x 0 + b * x 1)) ≤ a * x 0 - b * x 1 - cA + cB ∧
          a * x 0 - b * x 1 - cA + cB ≤ cA + cB - (a * x 0 + b * x 1))
      linarith
    · rintro ⟨hxB, hle⟩
      refine ⟨?_, hxB⟩
      have hin : ⟪x, v⟫ = (a * x 0 + b * x 1) / √2 := by
        simp only [v, PiLp.inner_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
          Matrix.cons_val_one, RCLike.inner_apply, conj_trivial]
        ring
      rw [hin] at hle
      have hle' := (div_le_div_iff_of_pos_right hs).mp hle
      have h2 := le_abs_self (a * x 0 - b * x 1 - cA + cB)
      have h3 := neg_abs_le (a * x 0 - b * x 1 - cA + cB)
      rw [mem_unitSquare]
      exact ⟨(hA x hxB).mpr (by linarith), (hB x hxB).mpr (by linarith)⟩

lemma coord_chart (x₀ : E 2) (i : Fin 2) :
    ∃ a c : ℝ, a ^ 2 = 1 ∧
      ∀ x ∈ Metric.ball x₀ (1 / 4), (0 ≤ x i ∧ x i ≤ 1 ↔ a * x i ≤ c) := by
  rcases le_or_gt (x₀ i) (1 / 2) with h | h
  · refine ⟨-1, 0, by norm_num, fun x hx => ?_⟩
    have := abs_le.mp ((abs_coord_sub_le x x₀ i).trans (Metric.mem_ball.mp hx).le)
    constructor
    · rintro ⟨h1, -⟩; linarith
    · intro h1; constructor <;> linarith
  · refine ⟨1, 1, by norm_num, fun x hx => ?_⟩
    have := abs_le.mp ((abs_coord_sub_le x x₀ i).trans (Metric.mem_ball.mp hx).le)
    constructor
    · rintro ⟨-, h1⟩; linarith
    · intro h1; constructor <;> linarith

theorem unitSquare_hasLipschitzBoundary : HasLipschitzBoundary unitSquare := by
  intro x₀ _
  obtain ⟨a, cA, ha, hA⟩ := coord_chart x₀ 0
  obtain ⟨b, cB, hb, hB⟩ := coord_chart x₀ 1
  exact ⟨1 / 4, by norm_num, corner_chart x₀ (1 / 4) a b cA cB ha hb hA hB⟩

/-! ### Lattice count, volume and the error -/

lemma volume_unitSquare : volume unitSquare = 1 := by
  have hpre : unitSquare = WithLp.ofLp ⁻¹' (Icc (0 : Fin 2 → ℝ) 1) := by
    ext x; simp [unitSquare, Pi.le_def, forall_and]
  rw [hpre, (PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage
    measurableSet_Icc.nullMeasurableSet, Real.volume_Icc_pi]
  simp

lemma latticeCount_unitSquare (m : ℕ) (hm : 0 < m) :
    latticeCount ((m : ℝ) • unitSquare) = (m + 1) ^ 2 := by
  have hm' : (m : ℝ) ≠ 0 := by positivity
  have hset : {z : Fin 2 → ℤ | WithLp.toLp 2 (fun i => (z i : ℝ)) ∈ (m : ℝ) • unitSquare}
      = ↑(Fintype.piFinset fun _ : Fin 2 => Finset.Icc (0 : ℤ) m) := by
    ext z
    rw [Set.mem_ofPred_eq, Set.mem_smul_set_iff_inv_smul_mem₀ hm', Finset.mem_coe,
      Fintype.mem_piFinset]
    change (∀ i, 0 ≤ _ ∧ _ ≤ 1) ↔ _
    refine forall_congr' fun i => ?_
    rw [Finset.mem_Icc]
    simp only [PiLp.smul_apply, smul_eq_mul]
    have hmpos : (0 : ℝ) < m := by positivity
    rw [mul_nonneg_iff_of_pos_left (inv_pos.mpr hmpos), inv_mul_le_iff₀ hmpos, mul_one]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  rw [latticeCount, hset, Set.ncard_coe_finset, Fintype.card_piFinset]
  simp only [Int.card_Icc, sub_zero, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [show ((m : ℤ) + 1).toNat = m + 1 by omega]

lemma discrepancy_unitSquare (m : ℕ) (hm : 0 < m) :
    discrepancy unitSquare m = 2 * m + 1 := by
  rw [discrepancy, latticeCount_unitSquare m hm, volume_unitSquare, ENNReal.toReal_one]
  push_cast
  ring

/-! ### `2m + 1` is not `O(m^{1/3})` -/

lemma not_isBigO_nat :
    ¬ (fun m : ℕ => discrepancy unitSquare m) =O[atTop] fun m : ℕ => (m : ℝ) ^ ((1 : ℝ) / 3) := by
  intro h
  obtain ⟨C, hC⟩ := h.bound
  rw [eventually_atTop] at hC
  obtain ⟨N, hN⟩ := hC
  set m : ℕ := N + ⌈C ^ 3⌉₊ + 1 with hmdef
  have hm : 0 < m := by omega
  have hb := hN m (by omega)
  rw [discrepancy_unitSquare m hm] at hb
  set u : ℝ := (m : ℝ) ^ ((1 : ℝ) / 3) with hu
  have hu0 : 0 ≤ u := Real.rpow_nonneg (Nat.cast_nonneg m) _
  have hu3 : u ^ 3 = m := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg m)]; norm_num
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmC : C ^ 3 < m := by
    have h1 := Nat.le_ceil (C ^ 3)
    have h2 : ((N + ⌈C ^ 3⌉₊ + 1 : ℕ) : ℝ) = N + ⌈C ^ 3⌉₊ + 1 := by push_cast; ring
    have h3 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    rw [hmdef, h2]; linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hu0, abs_of_pos (by positivity)] at hb
  have hu1 : 1 ≤ u := by
    by_contra hlt; rw [not_le] at hlt
    have : u ^ 3 < 1 := by
      calc u ^ 3 ≤ u := by nlinarith [mul_nonneg hu0 hu0]
        _ < 1 := hlt
    linarith
  have hCu : C < u := by
    by_contra hle; rw [not_lt] at hle
    have : u ^ 3 ≤ C ^ 3 := pow_le_pow_left₀ hu0 hle 3
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hu1 hu0]

/-! ### Main theorem -/

lemma exponent_two : ((2 : ℕ) : ℝ) - 2 + 1 / 3 = (1 : ℝ) / 3 := by norm_num

/-- **Main theorem.** The Lipschitz clause of the conjecture is false, both for real dilations
`t → ∞` and for integer dilations `m → ∞`: the closed unit square in `ℝ²` is a compact convex
body with nonempty interior and Lipschitz boundary, and its lattice error is `E(m) = 2m + 1` for
every integer `m ≥ 1`, which is not `O(m^{2-2+1/3})`. -/
theorem conjecture7795_false :
    IsCompact unitSquare ∧ Convex ℝ unitSquare ∧ (interior unitSquare).Nonempty ∧
      HasLipschitzBoundary unitSquare ∧
      (∀ m : ℕ, 0 < m → discrepancy unitSquare m = 2 * m + 1) ∧
      ¬ LipschitzClauseNat ∧ ¬ LipschitzClause := by
  refine ⟨isCompact_unitSquare, convex_unitSquare, interior_unitSquare_nonempty,
    unitSquare_hasLipschitzBoundary, discrepancy_unitSquare, fun h => ?_, fun h => ?_⟩
  · have := h 2 unitSquare isCompact_unitSquare interior_unitSquare_nonempty
      unitSquare_hasLipschitzBoundary
    rw [exponent_two] at this
    exact not_isBigO_nat this
  · have := h 2 unitSquare isCompact_unitSquare interior_unitSquare_nonempty
      unitSquare_hasLipschitzBoundary
    rw [exponent_two] at this
    exact not_isBigO_nat (this.comp_tendsto tendsto_natCast_atTop_atTop)

end C7795
