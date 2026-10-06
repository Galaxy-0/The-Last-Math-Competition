import Mathlib

/-!
# Conjecture 00000004116 is false

The conjecture: the asymptotic dimension of the configuration space `Conf_n(ℝ^d)` is exactly
`d n - 1` (coinciding with the coarse dimension, with zero "fractal correction").

We formalize:
* `Conf n d`: ordered configurations of `n` distinct points of `ℝ^d`, i.e. injective
  `x : Fin n → ℝ^d`, as a subspace of `(ℝ^d)^n = ℝ^{dn}` with the Euclidean (`L²`) metric.
* `AsdimLE X n` (Gromov; the definition quoted from Wikipedia "Asymptotic dimension"):
  for every `R ≥ 1` there is a uniformly bounded cover `𝒰` of `X` such that every closed `R`-ball
  meets at most `n + 1` members of `𝒰`.  `asdim X ∈ ℕ∞` is the least such `n` (`⊤` if none).

Results.
* `not_asdimLE_zero_conf`: for all `n, d ≥ 1`, `asdim (Conf n d) ≥ 1` (a chain argument).
* `asdim_conf_one_one`: `asdim (Conf 1 1) = 1` (`Conf_1(ℝ) ≅ ℝ`), whereas `d n - 1 = 0`.
* `conjecture_4116_false`: the formula `asdim (Conf n d) = d n - 1` fails at `n = d = 1`.
-/

open Metric

namespace C4116

section Asdim

variable (X : Type*) [PseudoMetricSpace X]

/-- A family of subsets is uniformly bounded: `sup_{U ∈ 𝒰} diam U < ∞`. -/
def UniformlyBounded (𝒰 : Set (Set X)) : Prop :=
  ∃ D : ℝ, ∀ U ∈ 𝒰, ∀ x ∈ U, ∀ y ∈ U, dist x y ≤ D

/-- `asdim X ≤ n`: for every `R ≥ 1` there is a uniformly bounded cover `𝒰` of `X` such that
every closed `R`-ball meets at most `n + 1` members of `𝒰`. -/
def AsdimLE (n : ℕ) : Prop :=
  ∀ R : ℝ, 1 ≤ R → ∃ 𝒰 : Set (Set X), ⋃₀ 𝒰 = Set.univ ∧ UniformlyBounded X 𝒰 ∧
    ∀ x : X, {U ∈ 𝒰 | (U ∩ closedBall x R).Nonempty}.encard ≤ n + 1

/-- The asymptotic dimension: the least `n` with `asdim X ≤ n`, and `∞` if there is none. -/
noncomputable def asdim : ℕ∞ := ⨅ (n : ℕ) (_ : AsdimLE X n), (n : ℕ∞)

variable {X}

theorem asdim_le_of (n : ℕ) (h : AsdimLE X n) : asdim X ≤ n :=
  iInf₂_le n h

theorem le_asdim_of (n : ℕ) (h : ∀ m : ℕ, AsdimLE X m → n ≤ m) : (n : ℕ∞) ≤ asdim X :=
  le_iInf₂ fun m hm => by exact_mod_cast h m hm

/-- Chain argument: if there are points `f 0, f 1, …` with consecutive distances `≤ 1` and
`dist (f 0) (f k)` unbounded, then `asdim X ≤ 0` fails. -/
theorem not_asdimLE_zero_of_chain (f : ℕ → X) (hstep : ∀ k, dist (f k) (f (k + 1)) ≤ 1)
    (hunb : ∀ D : ℝ, ∃ k, D < dist (f 0) (f k)) : ¬ AsdimLE X 0 := by
  intro h
  obtain ⟨𝒰, hcov, ⟨D, hD⟩, hmult⟩ := h 1 le_rfl
  have mem : ∀ x : X, ∃ U ∈ 𝒰, x ∈ U := fun x => by
    have : x ∈ ⋃₀ 𝒰 := hcov ▸ Set.mem_univ x
    simpa using this
  obtain ⟨U, hU, h0⟩ := mem (f 0)
  -- every `f k` lies in the same member `U`
  have hall : ∀ k, f k ∈ U := by
    intro k
    induction k with
    | zero => exact h0
    | succ k ih =>
      obtain ⟨V, hV, hk⟩ := mem (f (k + 1))
      have hsub : {W ∈ 𝒰 | (W ∩ closedBall (f k) 1).Nonempty}.Subsingleton := by
        have := hmult (f k)
        rw [Nat.cast_zero, zero_add] at this
        exact Set.encard_le_one_iff_subsingleton.mp this
      have hUm : U ∈ {W ∈ 𝒰 | (W ∩ closedBall (f k) 1).Nonempty} :=
        ⟨hU, f k, ih, mem_closedBall_self zero_le_one⟩
      have hVm : V ∈ {W ∈ 𝒰 | (W ∩ closedBall (f k) 1).Nonempty} :=
        ⟨hV, f (k + 1), hk, by rw [mem_closedBall, dist_comm]; exact hstep k⟩
      rw [hsub hUm hVm]
      exact hk
  obtain ⟨k, hk⟩ := hunb D
  exact absurd (hD U hU _ (hall 0) _ (hall k)) (not_le.mpr hk)

/-- If `X` embeds isometrically in `ℝ` via `φ`, then `asdim X ≤ 1` (cover by half-open intervals
of length `3R`). -/
theorem asdimLE_one_of_isometry_real (φ : X → ℝ) (hφ : ∀ x y, dist x y = |φ x - φ y|) :
    AsdimLE X 1 := by
  intro R hR
  set L := 3 * R with hL
  have hLpos : 0 < L := by positivity
  let U : ℤ → Set X := fun j => {x | (j : ℝ) * L ≤ φ x ∧ φ x < (j + 1) * L}
  refine ⟨Set.range U, ?_, ⟨L, ?_⟩, ?_⟩
  · refine Set.eq_univ_of_forall fun x => Set.mem_sUnion.mpr ⟨U ⌊φ x / L⌋, ⟨_, rfl⟩, ?_, ?_⟩
    · have := Int.floor_le (φ x / L)
      rwa [le_div_iff₀ hLpos] at this
    · have := Int.lt_floor_add_one (φ x / L)
      rwa [div_lt_iff₀ hLpos] at this
  · rintro _ ⟨j, rfl⟩ x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩
    rw [hφ, abs_le]
    constructor <;> nlinarith
  · intro x
    set m := ⌊(φ x - R) / L⌋ with hm
    have hm1 : (m : ℝ) * L ≤ φ x - R := by
      have := Int.floor_le ((φ x - R) / L)
      rwa [le_div_iff₀ hLpos] at this
    have hm2 : φ x - R < (m + 1) * L := by
      have := Int.lt_floor_add_one ((φ x - R) / L)
      rwa [div_lt_iff₀ hLpos] at this
    have hsub : {V ∈ Set.range U | (V ∩ closedBall x R).Nonempty} ⊆ {U m, U (m + 1)} := by
      rintro _ ⟨⟨j, rfl⟩, y, ⟨hy1, hy2⟩, hyb⟩
      rw [mem_closedBall, hφ, abs_le] at hyb
      have hj1 : m < j + 1 := by
        have : (m : ℝ) * L < (j + 1) * L := by linarith
        exact_mod_cast lt_of_mul_lt_mul_right this hLpos.le
      have hj2 : j < m + 2 := by
        have : (j : ℝ) * L < (m + 2) * L := by linarith
        exact_mod_cast lt_of_mul_lt_mul_right this hLpos.le
      have : j = m ∨ j = m + 1 := by omega
      rcases this with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    calc _ ≤ ({U m, U (m + 1)} : Set (Set X)).encard := Set.encard_le_encard hsub
      _ ≤ 2 := by
        refine (Set.encard_insert_le _ _).trans ?_
        rw [Set.encard_singleton]; norm_num
      _ = 1 + 1 := by norm_num

end Asdim

section Conf

/-- The ordered configuration space `Conf_n(ℝ^d)`: `n`-tuples of pairwise distinct points of
`ℝ^d`, with the metric of `(ℝ^d)^n = ℝ^{dn}` (Euclidean `L²` product). -/
def Conf (n d : ℕ) : Type :=
  {x : PiLp 2 (fun _ : Fin n => EuclideanSpace ℝ (Fin d)) // Function.Injective x}

noncomputable instance (n d : ℕ) : MetricSpace (Conf n d) := by
  unfold Conf; infer_instance

theorem Conf.dist_eq {n d : ℕ} (x y : Conf n d) : dist x y = dist x.1 y.1 := rfl

/-- For `n, d ≥ 1`, `asdim Conf_n(ℝ^d) ≥ 1`: translating a configuration along a fixed direction
gives a chain with unit steps and unbounded total distance. -/
theorem not_asdimLE_zero_conf (n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d) : ¬ AsdimLE (Conf n d) 0 := by
  set e : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single ⟨0, hd⟩ 1 with he
  have he0 : e ≠ 0 := by
    intro h
    have := congrArg (fun v : EuclideanSpace ℝ (Fin d) => v ⟨0, hd⟩) h
    simp [he] at this
  let c : PiLp 2 (fun _ : Fin n => EuclideanSpace ℝ (Fin d)) :=
    WithLp.toLp 2 (fun i => ((i : ℕ) : ℝ) • e)
  let w : PiLp 2 (fun _ : Fin n => EuclideanSpace ℝ (Fin d)) := WithLp.toLp 2 (fun _ => e)
  have hw0 : w ≠ 0 := by
    intro h
    have := congrArg (fun v : PiLp 2 (fun _ : Fin n => EuclideanSpace ℝ (Fin d)) => v ⟨0, hn⟩) h
    exact he0 (by simpa [w] using this)
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hinj : ∀ t : ℝ, Function.Injective (c + t • w) := by
    intro t i j hij
    simp only [PiLp.add_apply, PiLp.smul_apply, c, w] at hij
    have h1 : ((i : ℕ) : ℝ) • e = ((j : ℕ) : ℝ) • e := add_right_cancel hij
    have h2 : ((i : ℕ) : ℝ) = ((j : ℕ) : ℝ) := smul_left_injective ℝ he0 h1
    exact Fin.ext (by exact_mod_cast h2)
  let f : ℕ → Conf n d := fun k => ⟨c + ((k : ℝ) / ‖w‖) • w, hinj _⟩
  have hdist : ∀ a b : ℕ, dist (f a) (f b) = |(a : ℝ) - b| := by
    intro a b
    rw [Conf.dist_eq, dist_eq_norm]
    simp only [f]
    rw [add_sub_add_left_eq_sub, ← sub_smul, norm_smul, Real.norm_eq_abs, ← sub_div,
      abs_div, abs_of_pos hwpos, div_mul_cancel₀ _ hwpos.ne']
  refine not_asdimLE_zero_of_chain f (fun k => ?_) (fun D => ?_)
  · rw [hdist]; push_cast; simp
  · obtain ⟨k, hk⟩ := exists_nat_gt D
    refine ⟨k, ?_⟩
    rw [hdist]; simpa using hk

/-- `Conf_1(ℝ)` is isometric to `ℝ` via the unique coordinate. -/
theorem conf_one_one_dist (x y : Conf 1 1) :
    dist x y = |x.1 0 0 - y.1 0 0| := by
  rw [Conf.dist_eq, PiLp.dist_eq_of_L2, Fin.sum_univ_one, Real.sqrt_sq dist_nonneg,
    EuclideanSpace.dist_eq, Fin.sum_univ_one, Real.dist_eq, Real.sqrt_sq_eq_abs, abs_abs]

/-- `asdim Conf_1(ℝ) = 1`. -/
theorem asdim_conf_one_one : asdim (Conf 1 1) = 1 := by
  apply le_antisymm
  · exact_mod_cast asdim_le_of 1
      (asdimLE_one_of_isometry_real (fun x : Conf 1 1 => x.1 0 0) conf_one_one_dist)
  · refine le_asdim_of 1 fun m hm => ?_
    by_contra h
    have hm0 : m = 0 := by omega
    exact not_asdimLE_zero_conf 1 1 le_rfl le_rfl (hm0 ▸ hm)

/-- For every `n, d ≥ 1`, `asdim Conf_n(ℝ^d) ≥ 1`. -/
theorem one_le_asdim_conf (n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d) : 1 ≤ asdim (Conf n d) := by
  refine le_asdim_of 1 fun m hm => ?_
  by_contra h
  have hm0 : m = 0 := by omega
  exact not_asdimLE_zero_conf n d hn hd (hm0 ▸ hm)

end Conf

/-- **Main theorem.** The formula `asdim Conf_n(ℝ^d) = d n - 1` is false: for `n = d = 1` the
asymptotic dimension is `1 = d n`, not `d n - 1 = 0`. -/
theorem conjecture_4116_false :
    ¬ ∀ n d : ℕ, 1 ≤ n → 1 ≤ d → asdim (Conf n d) = ((d * n - 1 : ℕ) : ℕ∞) := by
  intro h
  have := h 1 1 le_rfl le_rfl
  rw [asdim_conf_one_one] at this
  norm_num at this

end C4116
