import Mathlib

/-!
# Conjecture 00000007758 is false

The conjecture: for `f ∈ ℤ[x]` of degree at least 2, if `f` has no real fixed point with an
attracting interval ("the real Julia set is totally disconnected"), then the integer orbit
`a₀, a₁ = f(a₀), a₂ = f(a₁), …` is finite (plus counting clauses that we do not need).

Witness: `f = X ^ 2 + 1`, the polynomial named in the conjecture itself.
* `f` has degree 2 and no real fixed point at all, so it has no attracting real fixed point
  under any definition of "attracting";
* its real Julia set is empty (hence totally disconnected), where the Julia set of a polynomial
  is the boundary of its filled Julia set `{z ∈ ℂ | the orbit of z is bounded}`; the
  one-dimensional variant (frontier in `ℝ` of the real filled Julia set) is empty too;
* every integer orbit is strictly increasing, hence infinite and unbounded.
-/

open Polynomial

namespace C7758

/-- Forward orbit `{a, f a, f (f a), …}` of `a` under a self-map. -/
def orbit {α : Type*} (g : α → α) (a : α) : Set α := Set.range fun n : ℕ => g^[n] a

/-- The integer orbit of `a₀ ∈ ℤ` under `f ∈ ℤ[x]`. -/
def intOrbit (f : ℤ[X]) (a : ℤ) : Set ℤ := orbit (fun x => f.eval x) a

/-- `f` acting on `ℝ`. -/
noncomputable def evalR (f : ℤ[X]) : ℝ → ℝ := fun x => (f.map (Int.castRingHom ℝ)).eval x

/-- `f` acting on `ℂ`. -/
noncomputable def evalC (f : ℤ[X]) : ℂ → ℂ := fun z => (f.map (Int.castRingHom ℂ)).eval z

/-- Filled Julia set: complex points with bounded forward orbit. -/
def filledJulia (f : ℤ[X]) : Set ℂ := {z | Bornology.IsBounded (orbit (evalC f) z)}

/-- Julia set of a polynomial: the boundary of the filled Julia set. -/
def juliaSet (f : ℤ[X]) : Set ℂ := frontier (filledJulia f)

/-- Real Julia set: the real points of the Julia set. -/
def realJulia (f : ℤ[X]) : Set ℝ := {x | (x : ℂ) ∈ juliaSet f}

/-- Real filled Julia set (the dynamics of `f` on `ℝ` only). -/
def realFilledJulia (f : ℤ[X]) : Set ℝ := {x | Bornology.IsBounded (orbit (evalR f) x)}

/-- The witness `x ^ 2 + 1`. -/
noncomputable def f0 : ℤ[X] := X ^ 2 + C 1

lemma natDegree_f0 : f0.natDegree = 2 := by
  unfold f0; exact natDegree_X_pow_add_C

lemma eval_f0 (a : ℤ) : f0.eval a = a ^ 2 + 1 := by simp [f0]
lemma evalR_f0 (x : ℝ) : evalR f0 x = x ^ 2 + 1 := by simp [evalR, f0]
lemma evalC_f0 (z : ℂ) : evalC f0 z = z ^ 2 + 1 := by simp [evalC, f0]

/-- `x ^ 2 + 1` has no real fixed point. -/
lemma no_real_fixed (x : ℝ) : evalR f0 x ≠ x := by
  rw [evalR_f0]; nlinarith [sq_nonneg (x - 1 / 2)]

/-- Every integer orbit grows at least linearly: `aₙ ≥ a₀ + n`. -/
lemma int_iter_ge (a : ℤ) (n : ℕ) : a + n ≤ (fun x => f0.eval x)^[n] a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', eval_f0]
    push_cast
    nlinarith [sq_nonneg ((fun x => f0.eval x)^[n] a - 1)]

lemma int_strictMono (a : ℤ) : StrictMono fun n : ℕ => (fun x => f0.eval x)^[n] a := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  simp only [Function.iterate_succ_apply', eval_f0]
  nlinarith [sq_nonneg ((fun x => f0.eval x)^[n] a - 1)]

/-- Every integer orbit of `x ^ 2 + 1` is infinite. -/
lemma intOrbit_infinite (a : ℤ) : (intOrbit f0 a).Infinite :=
  Set.infinite_range_of_injective (int_strictMono a).injective

/-- Every integer orbit of `x ^ 2 + 1` is unbounded. -/
lemma intOrbit_not_bddAbove (a : ℤ) : ¬ BddAbove (intOrbit f0 a) := by
  rintro ⟨B, hB⟩
  have h := hB ⟨(B - a).toNat + 1, rfl⟩
  have h2 := int_iter_ge a ((B - a).toNat + 1)
  push_cast at h2
  have := Int.self_le_toNat (B - a)
  linarith

/-- Escape estimate: `‖z‖ ≥ 2 → ‖z ^ 2 + 1‖ ≥ ‖z‖ + 1`. -/
lemma escape_step (z : ℂ) (hz : 2 ≤ ‖z‖) : ‖z‖ + 1 ≤ ‖evalC f0 z‖ := by
  rw [evalC_f0]
  have h1 : ‖z ^ 2‖ - ‖(1 : ℂ)‖ ≤ ‖z ^ 2 + 1‖ := by
    have h := norm_sub_le (z ^ 2 + 1) 1
    have : z ^ 2 = (z ^ 2 + 1) - 1 := by ring
    calc ‖z ^ 2‖ - ‖(1 : ℂ)‖ = ‖(z ^ 2 + 1) - 1‖ - ‖(1 : ℂ)‖ := by rw [← this]
      _ ≤ ‖z ^ 2 + 1‖ := by linarith
  rw [norm_pow, norm_one] at h1
  nlinarith

lemma escape_iter (z : ℂ) (hz : 2 ≤ ‖z‖) (n : ℕ) : ‖z‖ + n ≤ ‖(evalC f0)^[n] z‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have := escape_step _ (by linarith)
    push_cast; linarith

/-- A point whose third iterate has norm `> 2` is not in the filled Julia set. -/
lemma not_mem_filled (z : ℂ) (hz : 2 < ‖(evalC f0)^[3] z‖) : z ∉ filledJulia f0 := by
  intro hb
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 (show Bornology.IsBounded (orbit (evalC f0) z) from hb)
  have h := hC ((evalC f0)^[(⌈C⌉₊ + 1) + 3] z) ⟨_, rfl⟩
  rw [Function.iterate_add_apply] at h
  have h2 := escape_iter _ hz.le (⌈C⌉₊ + 1)
  have := Nat.le_ceil C
  push_cast at h2
  linarith

lemma continuous_evalC : Continuous (evalC f0) := by
  have : evalC f0 = fun z => z ^ 2 + 1 := funext evalC_f0
  rw [this]; fun_prop

/-- For real `x`, the third iterate is real and at least `5`. -/
lemma iter3_real (x : ℝ) : (evalC f0)^[3] (x : ℂ) = (((x ^ 2 + 1) ^ 2 + 1) ^ 2 + 1 : ℝ) := by
  simp [Function.iterate_succ_apply', evalC_f0]

/-- No real number lies in the closure of the filled Julia set of `x ^ 2 + 1`. -/
lemma real_not_mem_closure (x : ℝ) : (x : ℂ) ∉ closure (filledJulia f0) := by
  set U : Set ℂ := (evalC f0)^[3] ⁻¹' {w | 2 < ‖w‖}
  have hU : IsOpen U :=
    (isOpen_lt continuous_const continuous_norm).preimage (continuous_evalC.iterate 3)
  have hxU : (x : ℂ) ∈ U := by
    show 2 < ‖(evalC f0)^[3] (x : ℂ)‖
    rw [iter3_real, Complex.norm_real, Real.norm_eq_abs]
    have h1 : 1 ≤ x ^ 2 + 1 := by nlinarith [sq_nonneg x]
    have h2 : 2 ≤ (x ^ 2 + 1) ^ 2 + 1 := by nlinarith
    rw [abs_of_pos (by positivity)]
    nlinarith
  have hdisj : U ∩ filledJulia f0 = ∅ := by
    ext z; simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    exact fun hz => not_mem_filled z hz
  intro hcl
  have := mem_closure_iff.1 hcl U hU hxU
  rw [hdisj] at this
  exact Set.not_nonempty_empty this

/-- The real Julia set of `x ^ 2 + 1` is empty. -/
lemma realJulia_f0 : realJulia f0 = ∅ := by
  ext x
  simp only [realJulia, juliaSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  exact fun h => real_not_mem_closure x (frontier_subset_closure h)

/-- The real filled Julia set of `x ^ 2 + 1` is empty: real orbits grow by at least `3/4`. -/
lemma realFilledJulia_f0 : realFilledJulia f0 = ∅ := by
  ext x
  simp only [realFilledJulia, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  intro hb
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hb
  have hgrow : ∀ n : ℕ, x + 3 / 4 * n ≤ (evalR f0)^[n] x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', evalR_f0]
      push_cast
      nlinarith [sq_nonneg ((evalR f0)^[n] x - 1 / 2)]
  set n := ⌈(C - x) * 4 / 3⌉₊ + 1
  have h1 := hgrow n
  have h2 := hC _ ⟨n, rfl⟩
  have h3 := Nat.le_ceil ((C - x) * 4 / 3)
  have h4 : ((evalR f0)^[n] x) ≤ C := (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using h2)
  have : (n : ℝ) = ⌈(C - x) * 4 / 3⌉₊ + 1 := by simp [n]
  nlinarith

/-- **Conjecture 00000007758 is false.** For every notion `Attracting` of an attracting fixed
point (e.g. `|f'(p)| < 1`, or "has an attracting interval"), the clause "if `f` has degree `≥ 2`,
no attracting real fixed point, and a totally disconnected real Julia set, then every integer
orbit is finite" fails, witnessed by `f = x ^ 2 + 1`. The second conjunct records that the
witness has no real fixed point at all, an empty real Julia set and an empty real filled Julia
set (whose frontier in `ℝ` is therefore empty), and that every one of its integer orbits is
infinite and unbounded (so the existential and the bounded readings fail as well). -/
theorem conjecture_7758_false (Attracting : (ℝ → ℝ) → ℝ → Prop) :
    ¬ (∀ f : ℤ[X], 2 ≤ f.natDegree →
        (¬ ∃ x : ℝ, Function.IsFixedPt (evalR f) x ∧ Attracting (evalR f) x) →
        IsTotallyDisconnected (realJulia f) →
        ∀ a : ℤ, (intOrbit f a).Finite) ∧
    (f0.natDegree = 2 ∧ (∀ x : ℝ, ¬ Function.IsFixedPt (evalR f0) x) ∧
      realJulia f0 = ∅ ∧ realFilledJulia f0 = ∅ ∧ frontier (realFilledJulia f0) = ∅ ∧
      ∀ a : ℤ, (intOrbit f0 a).Infinite ∧ ¬ BddAbove (intOrbit f0 a)) := by
  have hfix : ∀ x : ℝ, ¬ Function.IsFixedPt (evalR f0) x := fun x => no_real_fixed x
  refine ⟨fun H => ?_, natDegree_f0, hfix, realJulia_f0, realFilledJulia_f0, ?_,
    fun a => ⟨intOrbit_infinite a, intOrbit_not_bddAbove a⟩⟩
  · have := H f0 natDegree_f0.ge (fun ⟨x, hx, _⟩ => hfix x hx)
      (by rw [realJulia_f0]; exact isTotallyDisconnected_empty) 0
    exact intOrbit_infinite 0 this
  · rw [realFilledJulia_f0, frontier_empty]

end C7758
