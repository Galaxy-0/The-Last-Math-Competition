import Mathlib

/-!
# Conjecture 00000000745 (disproof)

Statement: "The Julia set (repelling points) of x^2 - 1 on Z_2 has Hausdorff dimension 1,
and its complement is open and dense (2-adic Julia topology)."

We work on the space the statement names, the 2-adic integers `ℤ_[2]` with their 2-adic metric,
and the map `f x = x ^ 2 - 1`.  We consider four Julia-set readings:

* `juliaSet`: complement of the Fatou set, where the Fatou set is the set of points having a
  neighbourhood on which the iterates `f^[n]` are equicontinuous;
* `juliaSetPt`: points at which the family of iterates is not equicontinuous;
* `repellingPeriodicPts`: periodic points `x` (some period `n > 0`) whose multiplier
  `(g^[n])'(x)` (derivative in `ℚ_[2]` of the same polynomial `g z = z ^ 2 - 1`) has norm `> 1`;
* `juliaRep`: the closure of `repellingPeriodicPts`.

All four are empty: `f` is 1-Lipschitz on `ℤ_[2]` (since `f x - f y = (x - y) (x + y)` and
`‖x + y‖ ≤ 1`), so the iterates are uniformly equicontinuous; and the multiplier of every point of
`ℤ_[2]` for every `n` has norm at most `2 ^ (-n)`.  Hence the Hausdorff dimension is
`dimH ∅ = 0 ≠ 1`, while the complement (all of `ℤ_[2]`) is open and dense.
-/

open Set Filter Topology

namespace C745

/-- The map named by the conjecture, on the 2-adic integers. -/
noncomputable def f (x : ℤ_[2]) : ℤ_[2] := x ^ 2 - 1

/-- The same polynomial on the field `ℚ_[2]`, where derivatives are taken. -/
noncomputable def g (z : ℚ_[2]) : ℚ_[2] := z ^ 2 - 1

/-- Fatou set: points with a neighbourhood on which the iterates of `f` are equicontinuous. -/
def fatouSet : Set ℤ_[2] := {x | ∃ U ∈ 𝓝 x, EquicontinuousOn (fun n : ℕ => f^[n]) U}

/-- Julia set: the complement of the Fatou set. -/
def juliaSet : Set ℤ_[2] := fatouSetᶜ

/-- Pointwise variant: points at which the iterates of `f` are not equicontinuous. -/
def juliaSetPt : Set ℤ_[2] := {x | ¬ EquicontinuousAt (fun n : ℕ => f^[n]) x}

/-- Multiplier of `x` for the iterate `n`: the derivative of `g^[n]` at `x` in `ℚ_[2]`. -/
noncomputable def multiplier (n : ℕ) (x : ℤ_[2]) : ℚ_[2] := deriv (g^[n]) (x : ℚ_[2])

/-- Repelling periodic points: `f^[n] x = x` for some `n > 0` with multiplier of norm `> 1`. -/
def repellingPeriodicPts : Set ℤ_[2] :=
  {x | ∃ n : ℕ, 0 < n ∧ Function.IsPeriodicPt f n x ∧ 1 < ‖multiplier n x‖}

/-- Julia set as the closure of the repelling periodic points. -/
def juliaRep : Set ℤ_[2] := closure repellingPeriodicPts

/-! ## The iterates are uniformly equicontinuous -/

lemma f_sub (x y : ℤ_[2]) : f x - f y = (x - y) * (x + y) := by
  unfold f; ring

/-- `f` is 1-Lipschitz for the 2-adic metric. -/
theorem lipschitz_f : LipschitzWith 1 f := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [dist_eq_norm, dist_eq_norm, f_sub, norm_mul]
  have h1 := PadicInt.norm_le_one (x + y)
  have h0 := norm_nonneg (x - y)
  simp only [NNReal.coe_one, one_mul]
  nlinarith

theorem lipschitz_iterate (n : ℕ) : LipschitzWith 1 (f^[n]) := by
  simpa using lipschitz_f.iterate n

theorem uniformEquicontinuous_iterates : UniformEquicontinuous (fun n : ℕ => f^[n]) :=
  LipschitzWith.uniformEquicontinuous _ 1 lipschitz_iterate

theorem fatouSet_eq_univ : fatouSet = univ := by
  ext x
  simp only [mem_univ, iff_true]
  exact ⟨univ, univ_mem, uniformEquicontinuous_iterates.equicontinuous.equicontinuousOn _⟩

theorem juliaSet_eq_empty : juliaSet = ∅ := by
  simp [juliaSet, fatouSet_eq_univ]

theorem juliaSetPt_eq_empty : juliaSetPt = ∅ := by
  ext x
  simp only [juliaSetPt, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_not]
  exact uniformEquicontinuous_iterates.equicontinuous x

/-! ## No repelling points -/

lemma coe_f (x : ℤ_[2]) : ((f x : ℤ_[2]) : ℚ_[2]) = g x := by
  simp [f, g]

lemma coe_iterate (n : ℕ) (x : ℤ_[2]) : ((f^[n] x : ℤ_[2]) : ℚ_[2]) = g^[n] x :=
  (Function.Semiconj.iterate_right (f := ((↑) : ℤ_[2] → ℚ_[2])) coe_f n) x

/-- Chain rule: `(g^[n])'(z) = ∏_{i<n} g'(g^[i] z) = ∏_{i<n} 2 g^[i](z)`. -/
theorem hasDerivAt_iterate (n : ℕ) (z : ℚ_[2]) :
    HasDerivAt (g^[n]) (∏ i ∈ Finset.range n, 2 * g^[i] z) z := by
  induction n with
  | zero => simpa using hasDerivAt_id z
  | succ n ih =>
    rw [Function.iterate_succ', Finset.prod_range_succ]
    have hg : HasDerivAt g (2 * g^[n] z) (g^[n] z) := by
      have h := (hasDerivAt_pow 2 (g^[n] z)).sub_const 1
      have e : (fun x : ℚ_[2] => x ^ 2 - 1) = g := rfl
      rw [e] at h
      exact h.congr_deriv (by norm_num)
    have := hg.comp z ih
    rw [mul_comm]
    exact this

theorem multiplier_eq (n : ℕ) (x : ℤ_[2]) :
    multiplier n x = ∏ i ∈ Finset.range n, 2 * ((f^[i] x : ℤ_[2]) : ℚ_[2]) := by
  rw [multiplier, (hasDerivAt_iterate n x).deriv]
  simp [coe_iterate]

lemma norm_two : ‖(2 : ℚ_[2])‖ = 2⁻¹ := by
  simpa using Padic.norm_p (p := 2)

/-- Every point of `ℤ_[2]` is contracted by every iterate: `‖(g^[n])'(x)‖ ≤ 2 ^ (-n)`. -/
theorem norm_multiplier_le (n : ℕ) (x : ℤ_[2]) : ‖multiplier n x‖ ≤ (1 / 2 : ℝ) ^ n := by
  rw [multiplier_eq, norm_prod]
  calc ∏ i ∈ Finset.range n, ‖2 * ((f^[i] x : ℤ_[2]) : ℚ_[2])‖
      ≤ ∏ _i ∈ Finset.range n, (1 / 2 : ℝ) := by
        apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
        intro i _
        rw [norm_mul, norm_two, PadicInt.padic_norm_e_of_padicInt]
        have := PadicInt.norm_le_one (f^[i] x)
        have h0 := norm_nonneg (f^[i] x)
        nlinarith
    _ = (1 / 2 : ℝ) ^ n := by simp

/-- In particular no point of `ℤ_[2]` is expanding for any positive iterate. -/
theorem norm_multiplier_lt_one (n : ℕ) (hn : 0 < n) (x : ℤ_[2]) : ‖multiplier n x‖ < 1 :=
  (norm_multiplier_le n x).trans_lt (pow_lt_one₀ (by norm_num) (by norm_num) hn.ne')

theorem repellingPeriodicPts_eq_empty : repellingPeriodicPts = ∅ := by
  ext x
  simp only [repellingPeriodicPts, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_exists,
    not_and]
  intro n hn _ h
  exact absurd h (not_lt.mpr (norm_multiplier_lt_one n hn x).le)

theorem juliaRep_eq_empty : juliaRep = ∅ := by
  simp [juliaRep, repellingPeriodicPts_eq_empty]

/-! ## The chordal metric on `ℤ_[2]` is the 2-adic metric -/

/-- Chordal distance between affine points `[x:1], [y:1]` of `P^1(ℚ_[2])`. -/
noncomputable def chordal (x y : ℚ_[2]) : ℝ := ‖x - y‖ / (max 1 ‖x‖ * max 1 ‖y‖)

theorem chordal_eq_dist (x y : ℤ_[2]) : chordal x y = dist x y := by
  have hx : ‖(x : ℚ_[2])‖ ≤ 1 := by rw [PadicInt.padic_norm_e_of_padicInt]; exact x.norm_le_one
  have hy : ‖(y : ℚ_[2])‖ ≤ 1 := by rw [PadicInt.padic_norm_e_of_padicInt]; exact y.norm_le_one
  rw [chordal, max_eq_left hx, max_eq_left hy, dist_eq_norm, PadicInt.norm_def]
  simp

/-! ## The conjecture fails -/

/-- Under each of the four readings, the Julia set is empty, its Hausdorff dimension is `0`,
and its complement is open and dense. -/
theorem julia_facts :
    (juliaSet = ∅ ∧ juliaSetPt = ∅ ∧ repellingPeriodicPts = ∅ ∧ juliaRep = ∅) ∧
    (dimH juliaSet = 0 ∧ dimH juliaSetPt = 0 ∧ dimH repellingPeriodicPts = 0 ∧
      dimH juliaRep = 0) ∧
    (IsOpen juliaSetᶜ ∧ Dense juliaSetᶜ) ∧ (IsOpen juliaSetPtᶜ ∧ Dense juliaSetPtᶜ) ∧
    (IsOpen repellingPeriodicPtsᶜ ∧ Dense repellingPeriodicPtsᶜ) ∧
    (IsOpen juliaRepᶜ ∧ Dense juliaRepᶜ) := by
  simp only [juliaSet_eq_empty, juliaSetPt_eq_empty, repellingPeriodicPts_eq_empty,
    juliaRep_eq_empty, dimH_empty, compl_empty, isOpen_univ, dense_univ, and_self]

/-- **Main theorem.** For each reading `J` of "the Julia set (repelling points) of `x^2 - 1` on
`ℤ_[2]`", the conjunction "`dimH J = 1` and `Jᶜ` is open and dense" is false (the first
conjunct fails, the second holds). -/
theorem conjecture745_false :
    ¬ (dimH juliaSet = 1 ∧ IsOpen juliaSetᶜ ∧ Dense juliaSetᶜ) ∧
    ¬ (dimH juliaSetPt = 1 ∧ IsOpen juliaSetPtᶜ ∧ Dense juliaSetPtᶜ) ∧
    ¬ (dimH repellingPeriodicPts = 1 ∧ IsOpen repellingPeriodicPtsᶜ ∧
        Dense repellingPeriodicPtsᶜ) ∧
    ¬ (dimH juliaRep = 1 ∧ IsOpen juliaRepᶜ ∧ Dense juliaRepᶜ) := by
  simp only [juliaSet_eq_empty, juliaSetPt_eq_empty, repellingPeriodicPts_eq_empty,
    juliaRep_eq_empty, dimH_empty, zero_ne_one, false_and, not_false_eq_true, and_self]

end C745
