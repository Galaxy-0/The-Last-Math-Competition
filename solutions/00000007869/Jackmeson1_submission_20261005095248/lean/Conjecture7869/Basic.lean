import Mathlib

/-!
# Conjecture 00000007869: the two random-order clauses contradict each other

Conjecture text: "Every deterministic online algorithm has `R_ro^n >= 3/2 + epsilon_0` for an
explicit positive `epsilon_0`, while Simple-Best-Fit achieves `R_ro^n <= 3/2 + O(n^{-1/2})`"
(Chinese: "ε₀ 为显式正常数", i.e. `ε₀` is an explicit positive constant).

Best Fit is itself a deterministic online algorithm, so the first clause applied to it gives
`R_ro^n(BF) >= 3/2 + ε₀`, while the second gives `R_ro^n(BF) <= 3/2 + C/√n`; these are
incompatible as soon as `C/√n < ε₀`.

Part 1 proves the clash for an arbitrary ratio function `R : Alg → ℕ → ℝ` and an arbitrary
algorithm `A₀`, so neither the precise definition of `R_ro^n` nor the precise meaning of the
nonstandard name "Simple-Best-Fit" matters, as long as both clauses use the same `R_ro^n` and
the named algorithm belongs to the class quantified over in the first clause.
Part 2 instantiates it with concrete definitions: deterministic online bin-packing algorithms,
Best Fit, the optimum `OPT`, and `R_ro^n(A) = sup over n-item instances I of
E_σ[A(I_σ)] / OPT(I)`, with `σ` a uniformly random arrival order.

Quantifier readings on `n` that are refuted (Part 1): clause 1 "for all `n >= 1`",
"for all sufficiently large `n`", "for infinitely many `n`", or as a limit / limit superior,
against clause 2 "for all sufficiently large `n`" (the standard meaning of `O(n^{-1/2})`, implied
by "for all `n >= 1`"); and clause 1 "for all `n >= 1`" / "for all sufficiently large `n`" / as a
limit, against clause 2 "for infinitely many `n`". Not refuted: clause 1 read as "for some `n`",
and clause 1 and clause 2 both read only "for infinitely many `n`". The constant `ε₀` may depend
on the algorithm (this only weakens clause 1), but not on `n`. Convention: `x / 0 = 0` in Lean.
The final clause (the "4/3 to 3/2 jump") is not formalized.
-/

open Filter Topology

namespace C7869

/-! ## Part 1: the clash for an arbitrary ratio function -/

/-- `C / √n → 0`, so it is eventually below any `ε > 0`. -/
theorem eventually_div_sqrt_lt (C : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, C / Real.sqrt n < ε := by
  have h : Tendsto (fun n : ℕ => C / Real.sqrt n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  exact h.eventually (gt_mem_nhds hε)

variable {Alg : Type*}

/-- Clause 1 for infinitely many `n` against clause 2 for all sufficiently large `n`. -/
theorem clash_frequently_eventually (R : Alg → ℕ → ℝ) (A₀ : Alg) {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (h₁ : ∃ᶠ n in atTop, 3 / 2 + ε₀ ≤ R A₀ n) (C : ℝ)
    (h₂ : ∀ᶠ n in atTop, R A₀ n ≤ 3 / 2 + C / Real.sqrt n) : False := by
  obtain ⟨n, h1, h2, h3⟩ := (h₁.and_eventually (h₂.and (eventually_div_sqrt_lt C hε₀))).exists
  linarith

/-- Clause 1 for all sufficiently large `n` against clause 2 for infinitely many `n`. -/
theorem clash_eventually_frequently (R : Alg → ℕ → ℝ) (A₀ : Alg) {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (h₁ : ∀ᶠ n in atTop, 3 / 2 + ε₀ ≤ R A₀ n) (C : ℝ)
    (h₂ : ∃ᶠ n in atTop, R A₀ n ≤ 3 / 2 + C / Real.sqrt n) : False := by
  obtain ⟨n, h2, h1, h3⟩ := (h₂.and_eventually (h₁.and (eventually_div_sqrt_lt C hε₀))).exists
  linarith

/-- Limit reading of clause 1 (`R_ro^n(A₀) → L >= 3/2 + ε₀`) against clause 2 for infinitely
many `n` (hence also for all sufficiently large `n`). -/
theorem clash_tendsto_frequently (R : Alg → ℕ → ℝ) (A₀ : Alg) {ε₀ L : ℝ} (hε₀ : 0 < ε₀)
    (hL : 3 / 2 + ε₀ ≤ L) (h₁ : Tendsto (R A₀) atTop (𝓝 L)) (C : ℝ)
    (h₂ : ∃ᶠ n in atTop, R A₀ n ≤ 3 / 2 + C / Real.sqrt n) : False := by
  have hev : ∀ᶠ n in atTop, 3 / 2 + ε₀ / 2 ≤ R A₀ n :=
    (h₁.eventually (lt_mem_nhds (by linarith : 3 / 2 + ε₀ / 2 < L))).mono fun _ h => h.le
  exact clash_eventually_frequently R A₀ (half_pos hε₀) hev C h₂

/-- Limit-superior reading of clause 1 (`limsup_n R_ro^n(A₀) >= 3/2 + ε₀`) against clause 2 for
all sufficiently large `n`, for a ratio that is bounded below (true for every ratio of
nonnegative quantities). -/
theorem clash_limsup_eventually (R : Alg → ℕ → ℝ) (A₀ : Alg) {ε₀ b : ℝ} (hε₀ : 0 < ε₀)
    (hb : ∀ n, b ≤ R A₀ n) (h₁ : 3 / 2 + ε₀ ≤ limsup (R A₀) atTop) (C : ℝ)
    (h₂ : ∀ᶠ n in atTop, R A₀ n ≤ 3 / 2 + C / Real.sqrt n) : False := by
  have hev : ∀ᶠ n in atTop, R A₀ n ≤ 3 / 2 + ε₀ / 2 :=
    (h₂.and (eventually_div_sqrt_lt C (half_pos hε₀))).mono fun _ h => by linarith [h.1, h.2]
  have := limsup_le_of_le (isCoboundedUnder_le_of_le atTop hb) hev
  linarith

/-- The two clauses, with clause 1 in its weakest form "for infinitely many `n`" (and `ε₀`
allowed to depend on the algorithm) and clause 2 in its standard `O(n^{-1/2})` form, cannot
both hold for any ratio `R` and any algorithm `A₀` in the class `IsDetOnline`. -/
theorem clauses_inconsistent (R : Alg → ℕ → ℝ) (IsDetOnline : Alg → Prop) (A₀ : Alg)
    (hA₀ : IsDetOnline A₀) :
    ¬ ((∀ A, IsDetOnline A → ∃ ε₀ > 0, ∃ᶠ n in atTop, 3 / 2 + ε₀ ≤ R A n) ∧
       (∃ C : ℝ, ∀ᶠ n in atTop, R A₀ n ≤ 3 / 2 + C / Real.sqrt n)) := by
  rintro ⟨h₁, C, h₂⟩
  obtain ⟨ε₀, hε₀, h⟩ := h₁ A₀ hA₀
  exact clash_frequently_eventually R A₀ hε₀ h C h₂

/-! ## Part 2: concrete online bin packing -/

/-- An instance with `n` items: sizes in `(0, 1]`, bins have capacity `1`. -/
structure Instance (n : ℕ) where
  size : Fin n → ℝ
  pos : ∀ i, 0 < size i
  le_one : ∀ i, size i ≤ 1

/-- A deterministic online bin-packing algorithm. When an item of size `s` arrives it sees the
sizes `hist` of the earlier items (in arrival order), the current bin loads `loads`, and `s`,
and returns the index of the bin to use. An index that is out of range, or a bin in which the
item does not fit, means "open a new bin". The decision never depends on future items. -/
def OnlineAlg : Type := List ℝ → List ℝ → ℝ → ℕ

/-- Put an item of size `s` into bin `j` if it fits there, otherwise into a new bin. -/
noncomputable def place (loads : List ℝ) (j : ℕ) (s : ℝ) : List ℝ :=
  if j < loads.length ∧ loads.getD j 0 + s ≤ 1 then loads.set j (loads.getD j 0 + s)
  else loads ++ [s]

/-- Run an online algorithm on the remaining items; returns the final list of bin loads. -/
noncomputable def runAux (A : OnlineAlg) : List ℝ → List ℝ → List ℝ → List ℝ
  | _, loads, [] => loads
  | hist, loads, s :: rest => runAux A (hist ++ [s]) (place loads (A hist loads s) s) rest

/-- Number of bins the algorithm opens on an arrival sequence. -/
noncomputable def binsUsed (A : OnlineAlg) (items : List ℝ) : ℕ := (runAux A [] [] items).length

/-- Best Fit: the fullest bin in which the item fits (lowest index among ties); a new bin if
the item fits in no open bin. -/
noncomputable def bestFit : OnlineAlg := fun _ loads s =>
  (List.range loads.length).foldl
    (fun best j => if loads.getD j 0 + s ≤ 1 ∧
        (loads.length ≤ best ∨ loads.getD best 0 < loads.getD j 0) then j else best)
    loads.length

/-- `I` can be packed into `k` bins of capacity `1`. -/
def Packable {n : ℕ} (I : Instance n) (k : ℕ) : Prop :=
  ∃ f : Fin n → Fin k, ∀ b, ∑ i ∈ Finset.univ.filter (fun i => f i = b), I.size i ≤ 1

/-- The offline optimum `OPT(I)`: the least number of bins into which `I` can be packed. -/
noncomputable def opt {n : ℕ} (I : Instance n) : ℕ := sInf {k | Packable I k}

/-- The items of `I` in arrival order `σ`: the `t`-th arriving item is item `σ t`. -/
def arrival {n : ℕ} (I : Instance n) (σ : Equiv.Perm (Fin n)) : List ℝ :=
  List.ofFn fun t => I.size (σ t)

/-- `E_σ[A(I_σ)] / OPT(I)` for a uniformly random arrival order `σ`. -/
noncomputable def expRatio (A : OnlineAlg) {n : ℕ} (I : Instance n) : ℝ :=
  ((∑ σ : Equiv.Perm (Fin n), (binsUsed A (arrival I σ) : ℝ)) / (Nat.factorial n : ℝ)) /
    (opt I : ℝ)

/-- The random-order ratio `R_ro^n(A)`: the supremum of `expRatio A I` over `n`-item
instances. -/
noncomputable def Rro (A : OnlineAlg) (n : ℕ) : ℝ := ⨆ I : Instance n, expRatio A I

theorem Rro_nonneg (A : OnlineAlg) (n : ℕ) : 0 ≤ Rro A n :=
  Real.iSup_nonneg fun I => by unfold expRatio; positivity

/-- Clause 1 (weakest form: for infinitely many `n`, `ε₀` may depend on the algorithm). -/
def Clause1 : Prop := ∀ A : OnlineAlg, ∃ ε₀ > 0, ∃ᶠ n in atTop, 3 / 2 + ε₀ ≤ Rro A n

/-- Clause 2: `R_ro^n(BF) <= 3/2 + C n^{-1/2}` for all sufficiently large `n`. -/
def Clause2 : Prop := ∃ C : ℝ, ∀ᶠ n in atTop, Rro bestFit n ≤ 3 / 2 + C / Real.sqrt n

/-- Main theorem: the two clauses of the conjecture cannot both hold. -/
theorem conjecture_7869_false : ¬ (Clause1 ∧ Clause2) := fun ⟨h₁, h₂⟩ =>
  clauses_inconsistent Rro (fun _ => True) bestFit trivial ⟨fun A _ => h₁ A, h₂⟩

/-- The literal reading: one constant `ε₀ > 0` for all algorithms and all `n >= 1`, and one
constant `C` for all `n >= 1`. -/
theorem conjecture_7869_false_forall :
    ¬ ((∃ ε₀ > 0, ∀ A : OnlineAlg, ∀ n ≥ 1, 3 / 2 + ε₀ ≤ Rro A n) ∧
       (∃ C : ℝ, ∀ n ≥ 1, Rro bestFit n ≤ 3 / 2 + C / Real.sqrt n)) := by
  rintro ⟨⟨ε₀, hε₀, h₁⟩, C, h₂⟩
  exact clash_frequently_eventually Rro bestFit hε₀
    (eventually_atTop.mpr ⟨1, h₁ bestFit⟩).frequently C (eventually_atTop.mpr ⟨1, h₂⟩)

/-- Clause 1 for all sufficiently large `n` against clause 2 for infinitely many `n`. -/
theorem conjecture_7869_false_eventually_frequently :
    ¬ ((∀ A : OnlineAlg, ∃ ε₀ > 0, ∀ᶠ n in atTop, 3 / 2 + ε₀ ≤ Rro A n) ∧
       (∃ C : ℝ, ∃ᶠ n in atTop, Rro bestFit n ≤ 3 / 2 + C / Real.sqrt n)) := by
  rintro ⟨h₁, C, h₂⟩
  obtain ⟨ε₀, hε₀, h⟩ := h₁ bestFit
  exact clash_eventually_frequently Rro bestFit hε₀ h C h₂

/-- Limit-superior reading of clause 1 against clause 2. -/
theorem conjecture_7869_false_limsup :
    ¬ ((∀ A : OnlineAlg, ∃ ε₀ > 0, 3 / 2 + ε₀ ≤ limsup (Rro A) atTop) ∧ Clause2) := by
  rintro ⟨h₁, C, h₂⟩
  obtain ⟨ε₀, hε₀, h⟩ := h₁ bestFit
  exact clash_limsup_eventually Rro bestFit hε₀ (Rro_nonneg bestFit) h C h₂

/-- Limit reading of clause 1 against clause 2 for infinitely many `n`. -/
theorem conjecture_7869_false_tendsto :
    ¬ ((∀ A : OnlineAlg, ∃ ε₀ > 0, ∃ L, 3 / 2 + ε₀ ≤ L ∧ Tendsto (Rro A) atTop (𝓝 L)) ∧
       (∃ C : ℝ, ∃ᶠ n in atTop, Rro bestFit n ≤ 3 / 2 + C / Real.sqrt n)) := by
  rintro ⟨h₁, C, h₂⟩
  obtain ⟨ε₀, hε₀, L, hL, h⟩ := h₁ bestFit
  exact clash_tendsto_frequently Rro bestFit hε₀ hL h C h₂

end C7869
