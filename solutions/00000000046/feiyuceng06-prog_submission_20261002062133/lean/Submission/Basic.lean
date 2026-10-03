import Mathlib

/-!
# Conjecture 00000000046 is false

Let `G_n` be the prime-sum graph of conjecture 00000000045: vertices `1, …, n`, with
`i ~ j` iff `i ≠ j` and `i + j` is prime. Conjecture 00000000046 asserts that `G_n`
converges, in the sense of graph limits (cut distance), to the constant graphon
`W ≡ 1/2`. It does not: `δ□(W_{G_n}, 1/2) ≥ 1/8` for every `n ≥ 1`.

Everything is set up on `[0,1]` with Lebesgue measure (`unitInterval` with its
`volume`):

* the cut norm `‖U‖□ = sup_{S,T} |∫_{S×T} U|`, over measurable `S, T ⊆ [0,1]`;
* the cut distance `δ□(U, W) = inf_φ ‖U - W^φ‖□`, over invertible
  measure-preserving maps `φ : [0,1] → [0,1]`, where `W^φ(x,y) = W(φ x, φ y)`;
* the step graphon `W_{G_n}(x, y) = 1` if the vertices carrying `x` and `y` are
  adjacent and `0` otherwise, vertex `i` carrying the `i`-th interval of the
  partition `[0, 1/n], (1/n, 2/n], …, ((n-1)/n, 1]`.

The argument. The constant graphon is invariant under relabelling, so
`δ□(W_{G_n}, 1/2) = ‖W_{G_n} - 1/2‖□`. Two distinct odd numbers have an even sum
`≥ 4`, which is not prime, so the odd vertices of `G_n` are pairwise
non-adjacent: `W_{G_n}` vanishes on `S × S`, where `S ⊆ [0,1]` is the union of
the intervals of the odd vertices. `S` has measure `⌈n/2⌉/n ≥ 1/2`, so

  `‖W_{G_n} - 1/2‖□ ≥ |∫_{S×S} (W_{G_n} - 1/2)| = (1/2)·|S|² ≥ 1/8`.
-/

namespace Submission00000000046

open MeasureTheory Set Filter Topology unitInterval

/-! ## Graphons, the cut norm and the cut distance on `[0,1]` -/

/-- A graphon: a measurable symmetric function `[0,1]² → [0,1]`. -/
def IsGraphon (W : I × I → ℝ) : Prop :=
  Measurable W ∧ (∀ x y, W (x, y) = W (y, x)) ∧ ∀ p, 0 ≤ W p ∧ W p ≤ 1

/-- The cut norm `‖U‖□ = sup_{S,T} |∫_{S×T} U|`, the supremum over measurable
`S, T ⊆ [0,1]`. -/
noncomputable def cutNorm (U : I × I → ℝ) : ℝ :=
  ⨆ ST : {S : Set I // MeasurableSet S} × {T : Set I // MeasurableSet T},
    |∫ p in ST.1.1 ×ˢ ST.2.1, U p|

/-- The relabelled kernel `W^φ(x, y) = W(φ x, φ y)`. -/
def relabel (W : I × I → ℝ) (φ : I ≃ᵐ I) : I × I → ℝ :=
  fun p => W (φ p.1, φ p.2)

/-- The cut distance `δ□(U, W) = inf_φ ‖U - W^φ‖□`, the infimum over invertible
measure-preserving maps `φ` of `[0,1]`. -/
noncomputable def cutDist (U W : I × I → ℝ) : ℝ :=
  ⨅ φ : {φ : I ≃ᵐ I // MeasurePreserving φ volume volume}, cutNorm (U - relabel W φ.1)

/-! ## The prime-sum graphs and their step graphons -/

/-- The vertex of `[n] = {1, …, n}` whose interval contains `x ∈ [0,1]`, for the
partition `[0, 1/n], (1/n, 2/n], …, ((n-1)/n, 1]`: it is `max 1 ⌈n x⌉`. -/
noncomputable def vtx (n : ℕ) (x : I) : ℕ := max 1 ⌈(n : ℝ) * x⌉₊

/-- Adjacency in the prime-sum graph `G_n` on `{1, …, n}`: `i ≠ j` and `i + j` is
prime. -/
def PrimeSumAdj (i j : ℕ) : Prop := i ≠ j ∧ (i + j).Prime

instance : DecidableRel PrimeSumAdj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

/-- The step graphon `W_{G_n}` of the prime-sum graph `G_n`. -/
noncomputable def W (n : ℕ) : I × I → ℝ :=
  fun p => if PrimeSumAdj (vtx n p.1) (vtx n p.2) then 1 else 0

/-- The constant graphon `1/2`. -/
noncomputable def half : I × I → ℝ := fun _ => 1 / 2

/-- Conjecture 00000000046: `G_n` converges to the constant graphon `1/2` in cut
distance, i.e. `δ□(W_{G_n}, 1/2) → 0`. -/
def ConjectureHolds : Prop :=
  Tendsto (fun n => cutDist (W n) half) atTop (𝓝 0)

/-! ## The objects are graphons -/

theorem measurable_vtx (n : ℕ) : Measurable (vtx n) :=
  (measurable_from_nat (f := fun k : ℕ => max 1 k)).comp
    (measurable_const.mul measurable_subtype_coe).nat_ceil

theorem isGraphon_W (n : ℕ) : IsGraphon (W n) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (measurable_of_countable
      (fun ij : ℕ × ℕ => if PrimeSumAdj ij.1 ij.2 then (1 : ℝ) else 0)).comp
        ((measurable_vtx n).prodMap (measurable_vtx n))
  · intro x y
    have h : PrimeSumAdj (vtx n x) (vtx n y) ↔ PrimeSumAdj (vtx n y) (vtx n x) := by
      unfold PrimeSumAdj
      rw [ne_comm, add_comm]
    exact if_congr h rfl rfl
  · intro p
    unfold W
    split_ifs <;> norm_num

theorem isGraphon_half : IsGraphon half :=
  ⟨measurable_const, fun _ _ => rfl, fun _ => by norm_num [half]⟩

/-! ## The cells of the vertices -/

theorem one_le_vtx (n : ℕ) (x : I) : 1 ≤ vtx n x := le_max_left _ _

theorem vtx_le {n : ℕ} (hn : 1 ≤ n) (x : I) : vtx n x ≤ n := by
  refine max_le hn (Nat.ceil_le.2 ?_)
  have := x.2.2
  have h0 : (0 : ℝ) ≤ n := by positivity
  nlinarith

/-- Each vertex of `[n]` carries an interval of length `1/n`. -/
theorem volume_vtx_preimage {n : ℕ} (hn : 1 ≤ n) {i : ℕ} (hi₁ : 1 ≤ i) (hin : i ≤ n) :
    volume (vtx n ⁻¹' {i}) = ENNReal.ofReal (1 / n) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  rcases Nat.eq_or_lt_of_le hi₁ with rfl | hi₂
  · -- vertex `1` carries `[0, 1/n]`
    have hmem : (1 / n : ℝ) ∈ I := ⟨by positivity, by
      rw [div_le_one hnpos]; exact_mod_cast hn⟩
    have hset : vtx n ⁻¹' {1} = Iic (⟨1 / n, hmem⟩ : I) := by
      ext x
      simp only [mem_preimage, mem_singleton_iff, mem_Iic, vtx]
      rw [max_eq_left_iff, Nat.ceil_le, Nat.cast_one, ← Subtype.coe_le_coe,
        Subtype.coe_mk, le_div_iff₀ hnpos, mul_comm]
    rw [hset, volume_Iic]
  · -- vertex `i ≥ 2` carries `((i-1)/n, i/n]`
    have hlo : ((i - 1 : ℕ) / n : ℝ) ∈ I := ⟨by positivity, by
      rw [div_le_one hnpos]; exact_mod_cast (Nat.sub_le i 1).trans hin⟩
    have hhi : ((i : ℕ) / n : ℝ) ∈ I := ⟨by positivity, by
      rw [div_le_one hnpos]; exact_mod_cast hin⟩
    have hset : vtx n ⁻¹' {i} = Ioc (⟨_, hlo⟩ : I) ⟨_, hhi⟩ := by
      ext x
      simp only [mem_preimage, mem_singleton_iff, mem_Ioc, vtx]
      rw [← Subtype.coe_lt_coe, ← Subtype.coe_le_coe, Subtype.coe_mk, Subtype.coe_mk,
        div_lt_iff₀ hnpos, le_div_iff₀ hnpos, mul_comm (x : ℝ)]
      constructor
      · intro h
        have hc : ⌈(n : ℝ) * x⌉₊ = i := by
          rcases le_total 1 ⌈(n : ℝ) * x⌉₊ with h1 | h1
          · rwa [max_eq_right h1] at h
          · rw [max_eq_left h1] at h; omega
        exact (Nat.ceil_eq_iff (by omega)).1 hc
      · intro h
        have hc : ⌈(n : ℝ) * x⌉₊ = i := (Nat.ceil_eq_iff (by omega)).2 h
        rw [hc, max_eq_right (by omega)]
    rw [hset, volume_Ioc]
    congr 1
    push_cast [Nat.cast_sub (by omega : 1 ≤ i)]
    ring

/-- The distribution of `vtx n` is uniform on `{1, …, n}`. -/
theorem map_vtx {n : ℕ} (hn : 1 ≤ n) :
    Measure.map (vtx n) volume =
      ∑ i ∈ Finset.Icc 1 n, ENNReal.ofReal (1 / n) • Measure.dirac i := by
  refine Measure.ext_of_singleton fun i => ?_
  rw [Measure.map_apply (measurable_vtx n) (measurableSet_singleton i)]
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    Measure.dirac_apply, smul_eq_mul]
  by_cases hi : i ∈ Finset.Icc 1 n
  · rw [Finset.mem_Icc] at hi
    rw [volume_vtx_preimage hn hi.1 hi.2, Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      simp [Set.indicator, hb]
    · intro h; exact absurd (Finset.mem_Icc.2 hi) h
  · have hempty : vtx n ⁻¹' {i} = ∅ := by
      ext x
      simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
      intro hx
      exact hi (Finset.mem_Icc.2 ⟨hx ▸ one_le_vtx n x, hx ▸ vtx_le hn x⟩)
    rw [hempty, measure_empty, eq_comm]
    refine Finset.sum_eq_zero fun b hb => ?_
    have : b ≠ i := fun h => hi (h ▸ hb)
    simp [Set.indicator, this]

/-- The odd vertices `1, 3, 5, …` of `[n]` number `⌈n/2⌉ = (n+1)/2`. -/
theorem card_odd_Icc (n : ℕ) :
    ((Finset.Icc 1 n).filter Odd).card = (n + 1) / 2 := by
  have h : (Finset.Icc 1 n).filter Odd =
      (Finset.range ((n + 1) / 2)).image (fun k => 2 * k + 1) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image, Finset.mem_range,
      Nat.odd_iff]
    constructor
    · rintro ⟨⟨h₁, h₂⟩, h₃⟩
      exact ⟨x / 2, by omega, by omega⟩
    · rintro ⟨k, hk, rfl⟩
      omega
  rw [h, Finset.card_image_of_injective _ (fun a b hab => by omega),
    Finset.card_range]

/-- The set of points of `[0,1]` carried by odd vertices. -/
noncomputable def oddCells (n : ℕ) : Set I := vtx n ⁻¹' {i | Odd i}

theorem measurableSet_oddCells (n : ℕ) : MeasurableSet (oddCells n) :=
  measurable_vtx n (MeasurableSet.of_discrete)

/-- The odd vertices carry at least half of `[0,1]`. -/
theorem half_le_volume_oddCells {n : ℕ} (hn : 1 ≤ n) :
    1 / 2 ≤ volume.real (oddCells n) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hvol : volume (oddCells n) = ((n + 1) / 2 : ℕ) * ENNReal.ofReal (1 / n) := by
    rw [oddCells, ← Measure.map_apply (measurable_vtx n) (MeasurableSet.of_discrete),
      map_vtx hn]
    simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
      Measure.dirac_apply, smul_eq_mul]
    rw [← card_odd_Icc n, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul,
      Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : Odd i <;> simp [Set.indicator, hi]
  rw [measureReal_def, hvol, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  simp only [ENNReal.toReal_natCast]
  have h2 : (n : ℝ) ≤ 2 * (((n + 1) / 2 : ℕ) : ℝ) := by
    have : n ≤ 2 * ((n + 1) / 2) := by omega
    exact_mod_cast this
  rw [mul_one_div, le_div_iff₀ hnpos]
  linarith

/-! ## The odd vertices are pairwise non-adjacent -/

/-- Two distinct odd numbers have an even sum `≥ 4`, which is not prime. -/
theorem not_primeSumAdj_of_odd {i j : ℕ} (hi : Odd i) (hj : Odd j) : ¬ PrimeSumAdj i j := by
  rintro ⟨hne, hp⟩
  have h2 : i + j = 2 := hp.even_iff.1 (hi.add_odd hj)
  rcases hi with ⟨a, rfl⟩
  rcases hj with ⟨b, rfl⟩
  omega

/-- `W_{G_n}` vanishes on `S × S`, where `S` is carried by the odd vertices. -/
theorem W_eq_zero_of_mem {n : ℕ} {p : I × I} (hp : p ∈ oddCells n ×ˢ oddCells n) :
    W n p = 0 :=
  if_neg (not_primeSumAdj_of_odd hp.1 hp.2)

theorem measureReal_oddCells_prod (n : ℕ) :
    volume.real (oddCells n ×ˢ oddCells n) = volume.real (oddCells n) ^ 2 := by
  rw [measureReal_def, Measure.volume_eq_prod, Measure.prod_prod, ENNReal.toReal_mul, sq,
    measureReal_def]

theorem setIntegral_oddCells (n : ℕ) :
    ∫ p in oddCells n ×ˢ oddCells n, (W n - half) p =
      -(1 / 2) * volume.real (oddCells n) ^ 2 := by
  have hS := (measurableSet_oddCells n).prod (measurableSet_oddCells n)
  rw [setIntegral_congr_fun hS (g := fun _ => -(1 / 2 : ℝ))
      (fun p hp => by simp [W_eq_zero_of_mem hp, half]),
    setIntegral_const, smul_eq_mul, measureReal_oddCells_prod]
  ring

/-! ## The cut distance to `1/2` stays at least `1/8` -/

/-- `|W_{G_n} - 1/2| ≤ 1/2`, so its integral over any box is at most `1` in absolute
value; this makes the supremum in the cut norm a genuine (bounded) supremum. -/
theorem abs_setIntegral_le_one (n : ℕ) (S T : Set I) :
    |∫ p in S ×ˢ T, (W n - half) p| ≤ 1 := by
  have hb : ∀ p ∈ S ×ˢ T, ‖(W n - half) p‖ ≤ 1 := by
    intro p _
    simp only [Pi.sub_apply, W, half, Real.norm_eq_abs]
    split_ifs <;> norm_num [abs_le]
  have h := norm_setIntegral_le_of_norm_le_const (measure_lt_top volume (S ×ˢ T)) hb
  rw [Real.norm_eq_abs, one_mul] at h
  exact h.trans measureReal_le_one

theorem eighth_le_cutNorm {n : ℕ} (hn : 1 ≤ n) : 1 / 8 ≤ cutNorm (W n - half) := by
  unfold cutNorm
  have hbdd : BddAbove (Set.range fun ST :
      {S : Set I // MeasurableSet S} × {T : Set I // MeasurableSet T} =>
        |∫ p in ST.1.1 ×ˢ ST.2.1, (W n - half) p|) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨ST, rfl⟩
    exact abs_setIntegral_le_one n _ _
  have hS := measurableSet_oddCells n
  refine le_trans ?_ (le_ciSup hbdd ⟨⟨oddCells n, hS⟩, ⟨oddCells n, hS⟩⟩)
  show 1 / 8 ≤ |∫ p in oddCells n ×ˢ oddCells n, (W n - half) p|
  rw [setIntegral_oddCells]
  have hv := half_le_volume_oddCells hn
  have hv2 : 1 / 4 ≤ volume.real (oddCells n) ^ 2 := by nlinarith
  rw [abs_of_nonpos (by nlinarith)]
  linarith

/-- Relabelling does not change a constant kernel. -/
theorem relabel_half (φ : I ≃ᵐ I) : relabel half φ = half := rfl

/-- Against a constant kernel the infimum over relabellings is attained by every `φ`:
`δ□(U, 1/2) = ‖U - 1/2‖□`. -/
theorem cutDist_half (U : I × I → ℝ) : cutDist U half = cutNorm (U - half) := by
  have : Nonempty {φ : I ≃ᵐ I // MeasurePreserving φ volume volume} :=
    ⟨⟨MeasurableEquiv.refl I, MeasurePreserving.id volume⟩⟩
  simp only [cutDist, relabel_half, ciInf_const]

/-- `δ□(W_{G_n}, 1/2) ≥ 1/8` for every `n ≥ 1`. -/
theorem eighth_le_cutDist {n : ℕ} (hn : 1 ≤ n) : 1 / 8 ≤ cutDist (W n) half := by
  rw [cutDist_half]
  exact eighth_le_cutNorm hn

/-- Conjecture 00000000046 is false: `δ□(W_{G_n}, 1/2) ≥ 1/8` for all `n ≥ 1`, so
it does not tend to `0`. -/
theorem conjecture_00000000046_false : ¬ ConjectureHolds := by
  intro h
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 h).2 (1 / 8) (by norm_num))
  have h₁ := hN (max N 1) (le_max_left _ _)
  have h₂ := eighth_le_cutDist (le_max_right N 1)
  linarith

end Submission00000000046

#print axioms Submission00000000046.conjecture_00000000046_false
