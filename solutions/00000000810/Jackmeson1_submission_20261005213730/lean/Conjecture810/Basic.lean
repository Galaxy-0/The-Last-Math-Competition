import Mathlib

/-!
# Conjecture 00000000810: the metric star does not minimise the first Kirchhoff eigenvalue

A metric graph is a finite (multi)graph whose edges are intervals `[0, len e]`.  The Kirchhoff
(standard) eigenvalue problem asks for `f_e'' = -lam f_e` on every edge, continuity at every vertex
and, at every vertex, vanishing of the sum of the outgoing derivatives.

We show, for every `k ≥ 3` (so `n = k + 1 ≥ 4` vertices) and every total length `L > 0`:
* no star `K_{1,k}` (any edge lengths summing to `L`) has a Kirchhoff eigenvalue in `(0, π²/L²]`;
* the path with `k + 1` vertices and total length `L` has the eigenvalue `π²/L²`;
* for every star and every positive eigenvalue `μ` of it, another star with the same number of
  vertices and the same total length has a positive eigenvalue `< μ`.
Hence no star attains the minimum of the first positive Kirchhoff eigenvalue, neither among all
metric graphs with `k + 1` vertices and length `L`, nor among stars alone.
-/

open Real Set Finset

namespace C810

/-- A finite metric graph on the vertex set `Fin n`: edges `Fin m`; edge `e` is the interval
`[0, len e]`, whose endpoint `0` is glued to `tail e` and whose endpoint `len e` is glued to
`head e`.  Loops and multiple edges are allowed. -/
structure MetricGraph (n : ℕ) where
  m : ℕ
  tail : Fin m → Fin n
  head : Fin m → Fin n
  len : Fin m → ℝ
  len_pos : ∀ e, 0 < len e

namespace MetricGraph

variable {n : ℕ} (G : MetricGraph n)

/-- Total length of a metric graph. -/
def totalLength : ℝ := ∑ e, G.len e

/-- `f` (with derivative `f'`) solves the Kirchhoff eigenvalue problem with eigenvalue `lam`:
`f_e'' = -lam f_e` on each closed edge (one-sided derivatives at the endpoints), continuity at the
vertices (a common vertex value `F v`), and the Kirchhoff condition: at every vertex the sum of the
derivatives in the outgoing direction, `f_e'(0)` at a tail and `-f_e'(len e)` at a head, is zero. -/
def IsEigenfunction (lam : ℝ) (f f' : Fin G.m → ℝ → ℝ) : Prop :=
  (∀ e, ∀ x ∈ Icc 0 (G.len e), HasDerivWithinAt (f e) (f' e x) (Icc 0 (G.len e)) x) ∧
  (∀ e, ∀ x ∈ Icc 0 (G.len e), HasDerivWithinAt (f' e) (-lam * f e x) (Icc 0 (G.len e)) x) ∧
  (∃ F : Fin n → ℝ, ∀ e, f e 0 = F (G.tail e) ∧ f e (G.len e) = F (G.head e)) ∧
  (∀ v, (∑ e with G.tail e = v, f' e 0) - (∑ e with G.head e = v, f' e (G.len e)) = 0)

/-- `lam` is a Kirchhoff eigenvalue: it has an eigenfunction that is not identically zero. -/
def IsEigenvalue (lam : ℝ) : Prop :=
  ∃ f f' : Fin G.m → ℝ → ℝ, G.IsEigenfunction lam f f' ∧ ∃ e, ∃ x ∈ Icc 0 (G.len e), f e x ≠ 0

end MetricGraph

open MetricGraph

/-- The metric star `K_{1,k}`: centre `0`, leaves `1, ..., k`; edge `e` joins the centre to the
leaf `e.succ` and has length `ℓ e`. -/
abbrev star (k : ℕ) (ℓ : Fin k → ℝ) (hℓ : ∀ e, 0 < ℓ e) : MetricGraph (k + 1) where
  m := k
  tail := fun _ => 0
  head := Fin.succ
  len := ℓ
  len_pos := hℓ

/-- The metric path with vertices `0, ..., k`: edge `e` joins `e` to `e + 1`, length `L / k`. -/
noncomputable abbrev path (k : ℕ) (L : ℝ) (hk : 0 < k) (hL : 0 < L) : MetricGraph (k + 1) where
  m := k
  tail := Fin.castSucc
  head := Fin.succ
  len := fun _ => L / k
  len_pos := fun _ => div_pos hL (Nat.cast_pos.2 hk)

/-! ### An ODE uniqueness lemma -/

/-- If `f'' = -s² f` on `[0, l]` and `f'(l) = 0`, then `f x = f l * cos (s (l - x))`. -/
lemma ode_cos {f f' : ℝ → ℝ} {s l : ℝ} (hs : 0 < s) (hl : 0 < l)
    (h1 : ∀ x ∈ Icc 0 l, HasDerivWithinAt f (f' x) (Icc 0 l) x)
    (h2 : ∀ x ∈ Icc 0 l, HasDerivWithinAt f' (-s ^ 2 * f x) (Icc 0 l) x) (hN : f' l = 0) :
    ∀ x ∈ Icc 0 l, f x = f l * cos (s * (l - x)) ∧ f' x = f l * s * sin (s * (l - x)) := by
  set a := f l
  have hc : ∀ x, HasDerivAt (fun x => a * cos (s * (l - x))) (a * s * sin (s * (l - x))) x :=
    fun x => ((((hasDerivAt_id' (x := x)).const_sub l).const_mul s).cos.const_mul a).congr_deriv
      (by ring)
  have hsn : ∀ x, HasDerivAt (fun x => a * s * sin (s * (l - x)))
      (-s ^ 2 * (a * cos (s * (l - x)))) x :=
    fun x => ((((hasDerivAt_id' (x := x)).const_sub l).const_mul s).sin.const_mul (a * s)).congr_deriv
      (by ring)
  -- `g = f - a cos (s (l - x))` solves the same equation with `g l = g' l = 0`
  have hg : ∀ x ∈ Icc 0 l, HasDerivWithinAt (fun y => f y - a * cos (s * (l - y)))
      (f' x - a * s * sin (s * (l - x))) (Icc 0 l) x := fun x hx =>
    (h1 x hx).sub (hc x).hasDerivWithinAt
  have hg' : ∀ x ∈ Icc 0 l, HasDerivWithinAt (fun y => f' y - a * s * sin (s * (l - y)))
      (-s ^ 2 * (f x - a * cos (s * (l - x)))) (Icc 0 l) x := fun x hx =>
    ((h2 x hx).sub (hsn x).hasDerivWithinAt).congr_deriv (by ring)
  -- the energy `g'² + s² g²` is constant
  have hE : ∀ x ∈ Icc 0 l, HasDerivWithinAt (fun y => (f' y - a * s * sin (s * (l - y))) *
      (f' y - a * s * sin (s * (l - y))) + s ^ 2 * ((f y - a * cos (s * (l - y))) *
      (f y - a * cos (s * (l - y))))) 0 (Icc 0 l) x := fun x hx =>
    (((hg' x hx).mul (hg' x hx)).add (((hg x hx).mul (hg x hx)).const_mul (s ^ 2))).congr_deriv
      (by ring)
  have hconst := constant_of_has_deriv_right_zero (fun x hx => (hE x hx).continuousWithinAt)
    (fun x hx => (hE x (Ico_subset_Icc_self hx)).mono_of_mem_nhdsWithin
      (Filter.mem_of_superset (Icc_mem_nhdsGE hx.2) (Icc_subset_Icc_left hx.1)))
  intro x hx
  have hEx := (hconst x hx).trans (hconst l ⟨hl.le, le_rfl⟩).symm
  simp only [sub_self, mul_zero, cos_zero, sin_zero, hN, a, mul_one] at hEx
  have hs2 := pow_pos hs 2
  constructor
  · nlinarith [mul_self_nonneg (f' x - f l * s * sin (s * (l - x))),
      mul_self_nonneg (f x - f l * cos (s * (l - x))),
      mul_self_eq_zero.1 (show (f x - f l * cos (s * (l - x))) * (f x - f l * cos (s * (l - x))) = 0
        by nlinarith [mul_self_nonneg (f' x - f l * s * sin (s * (l - x))),
          mul_self_nonneg (f x - f l * cos (s * (l - x)))])]
  · nlinarith [mul_self_eq_zero.1 (show (f' x - f l * s * sin (s * (l - x))) *
        (f' x - f l * s * sin (s * (l - x))) = 0 by
        nlinarith [mul_self_nonneg (f' x - f l * s * sin (s * (l - x))),
          mul_self_nonneg (f x - f l * cos (s * (l - x)))])]

/-! ### Superadditivity of `tan` on `[0, π/2)` -/

lemma tan_add_identity {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x + y < π / 2) :
    tan x + tan y + tan x * tan y * tan (x + y) = tan (x + y) := by
  have cx : cos x ≠ 0 := (cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith⟩).ne'
  have cy : cos y ≠ 0 := (cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith⟩).ne'
  have cxy : cos (x + y) ≠ 0 := (cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hxy⟩).ne'
  rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos, tan_eq_sin_div_cos]
  field_simp
  rw [sin_add, cos_add]
  ring

lemma tan_sum_le {ι : Type*} (s : Finset ι) (θ : ι → ℝ) (h0 : ∀ i ∈ s, 0 ≤ θ i)
    (h : ∑ i ∈ s, θ i < π / 2) : ∑ i ∈ s, tan (θ i) ≤ tan (∑ i ∈ s, θ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha] at h ⊢
    rw [sum_insert ha]
    have hs0 : 0 ≤ ∑ i ∈ s, θ i := sum_nonneg (fun i hi => h0 i (mem_insert_of_mem hi))
    have ha0 := h0 a (mem_insert_self a s)
    have ih' := ih (fun i hi => h0 i (mem_insert_of_mem hi)) (by linarith)
    have hid := tan_add_identity ha0 hs0 h
    have t1 := tan_nonneg_of_nonneg_of_le_pi_div_two ha0 (by linarith)
    have t2 := tan_nonneg_of_nonneg_of_le_pi_div_two hs0 (by linarith)
    have t3 := tan_nonneg_of_nonneg_of_le_pi_div_two (add_nonneg ha0 hs0) h.le
    nlinarith [mul_nonneg (mul_nonneg t1 t2) t3]

lemma tan_sum_lt {ι : Type*} (s : Finset ι) (θ : ι → ℝ) (h0 : ∀ i ∈ s, 0 < θ i)
    (h2 : 1 < s.card) (h : ∑ i ∈ s, θ i < π / 2) : ∑ i ∈ s, tan (θ i) < tan (∑ i ∈ s, θ i) := by
  classical
  obtain ⟨a, ha⟩ : s.Nonempty := card_pos.1 (by omega)
  rw [← add_sum_erase s _ ha] at h ⊢
  rw [← add_sum_erase s _ ha]
  have hne : (s.erase a).Nonempty := by
    rw [← card_pos, card_erase_of_mem ha]; omega
  have hR : 0 < ∑ i ∈ s.erase a, θ i := sum_pos (fun i hi => h0 i (mem_of_mem_erase hi)) hne
  have ha0 := h0 a ha
  have hle := tan_sum_le (s.erase a) θ (fun i hi => (h0 i (mem_of_mem_erase hi)).le)
    (by linarith)
  have hid := tan_add_identity ha0.le hR.le h
  have t1 := tan_pos_of_pos_of_lt_pi_div_two ha0 (by linarith)
  have t2 := tan_pos_of_pos_of_lt_pi_div_two hR (by linarith)
  have t3 := tan_pos_of_pos_of_lt_pi_div_two (add_pos ha0 hR) h
  nlinarith [mul_pos (mul_pos t1 t2) t3]

/-! ### The secular equation of a star has no root in `(0, π/L]` -/

/-- Continuity `a_e cos θ_e = c` and Kirchhoff `∑ a_e sin θ_e = 0`, with at least three positive
angles of total at most `π`, force all `a_e = 0`. -/
lemma star_trig {k : ℕ} (hk : 3 ≤ k) (θ a : Fin k → ℝ) (c : ℝ) (hθ : ∀ e, 0 < θ e)
    (hsum : ∑ e, θ e ≤ π) (hc : ∀ e, a e * cos (θ e) = c) (hK : ∑ e, a e * sin (θ e) = 0) :
    ∀ e, a e = 0 := by
  obtain ⟨e₀, -, hmax⟩ := exists_max_image univ θ ⟨⟨0, by omega⟩, mem_univ _⟩
  set S := univ.erase e₀ with hS
  set R := ∑ e ∈ S, θ e with hR_def
  have hsplit : θ e₀ + R = ∑ e, θ e := add_sum_erase _ _ (mem_univ _)
  have hcard : 1 < S.card := by
    rw [hS, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]; omega
  have hSne : S.Nonempty := card_pos.1 (by omega)
  have hR : 0 < R := sum_pos (fun e _ => hθ e) hSne
  have hlt : ∀ e ∈ S, θ e < R := by
    intro e he
    obtain ⟨j, hj, hje⟩ := exists_mem_ne hcard e
    exact single_lt_sum hje he hj (hθ j) (fun i _ _ => (hθ i).le)
  have hhalf : ∀ e ∈ S, θ e < π / 2 := by
    intro e he; have := hlt e he; have := hmax e (mem_univ _); linarith
  have hθ0 : θ e₀ < π := by linarith
  have hsin0 : 0 < sin (θ e₀) := sin_pos_of_pos_of_lt_pi (hθ e₀) hθ0
  have hcosS : ∀ e ∈ S, 0 < cos (θ e) := fun e he =>
    cos_pos_of_mem_Ioo ⟨by linarith [hθ e, pi_pos], hhalf e he⟩
  set T := ∑ e ∈ S, tan (θ e) with hT_def
  have hT : 0 < T := sum_pos (fun e he => tan_pos_of_pos_of_lt_pi_div_two (hθ e) (hhalf e he)) hSne
  have hKs : a e₀ * sin (θ e₀) + c * T = 0 := by
    rw [← hK, ← add_sum_erase _ _ (mem_univ e₀), mul_sum]
    congr 1
    apply sum_congr rfl
    intro e he
    rw [tan_eq_sin_div_cos, ← hc e]
    field_simp [(hcosS e he).ne']
  have hP : 0 < sin (θ e₀) + cos (θ e₀) * T := by
    rcases le_or_gt 0 (cos (θ e₀)) with h | h
    · nlinarith
    · have hgt : π / 2 < θ e₀ := by
        by_contra hh
        have := cos_nonneg_of_mem_Icc ⟨by linarith [hθ e₀, pi_pos], not_lt.1 hh⟩
        linarith
      have h1 : T < tan R := tan_sum_lt S θ (fun e _ => hθ e) hcard (by linarith)
      have h2 : tan R ≤ tan (π - θ e₀) :=
        strictMonoOn_tan.monotoneOn ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
          (by linarith)
      rw [tan_pi_sub, tan_eq_sin_div_cos (θ e₀)] at h2
      have h3 : cos (θ e₀) * (-(sin (θ e₀) / cos (θ e₀))) < cos (θ e₀) * T :=
        mul_lt_mul_of_neg_left (by linarith) h
      rw [mul_neg, mul_div_cancel₀ _ h.ne] at h3
      linarith
  have ha0 : a e₀ = 0 := by
    have : a e₀ * (sin (θ e₀) + cos (θ e₀) * T) = 0 := by
      linear_combination hKs + T * hc e₀
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · linarith
  have hc0 : c = 0 := by rw [← hc e₀, ha0, zero_mul]
  intro e
  by_cases he : e = e₀
  · rw [he]; exact ha0
  · have hcos := hcosS e (mem_erase.2 ⟨he, mem_univ _⟩)
    have := hc e
    rw [hc0] at this
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · linarith

/-- **No star has a Kirchhoff eigenvalue in `(0, π²/L²]`** when it has at least three edges. -/
theorem star_no_eigenvalue_le (k : ℕ) (hk : 3 ≤ k) (ℓ : Fin k → ℝ) (hℓ : ∀ e, 0 < ℓ e)
    (lam : ℝ) (hlam : 0 < lam) (hle : lam ≤ π ^ 2 / (∑ e, ℓ e) ^ 2) :
    ¬ (star k ℓ hℓ).IsEigenvalue lam := by
  rintro ⟨f, f', ⟨h1, h2, ⟨F, hF⟩, hK⟩, e₁, x₁, hx₁, hne⟩
  set s := √lam with hs_def
  have hs : 0 < s := Real.sqrt_pos.2 hlam
  have hs2 : s ^ 2 = lam := Real.sq_sqrt hlam.le
  have hL : 0 < ∑ e, ℓ e := sum_pos (fun e _ => hℓ e) ⟨⟨0, by omega⟩, mem_univ _⟩
  have hsL : s * ∑ e, ℓ e ≤ π := by
    have h0 : lam * (∑ e, ℓ e) ^ 2 ≤ π ^ 2 := by
      rwa [le_div_iff₀ (by positivity)] at hle
    by_contra hh
    nlinarith [pi_pos, not_le.1 hh]
  have hleaf : ∀ e, f' e (ℓ e) = 0 := by
    intro e
    have := hK e.succ
    have hz : ∀ e' : Fin k, ((0 : Fin (k + 1)) = e'.succ) ↔ False :=
      fun e' => ⟨fun h => Fin.succ_ne_zero e' h.symm, False.elim⟩
    simpa [hz, Finset.filter_eq'] using this
  have hsol := fun e => ode_cos hs (hℓ e) (h1 e) (by rw [hs2]; exact h2 e) (hleaf e)
  have hc : ∀ e, f e (ℓ e) * cos (s * ℓ e) = F 0 := by
    intro e
    have := (hsol e 0 ⟨le_rfl, (hℓ e).le⟩).1
    rw [sub_zero, (hF e).1] at this
    exact this.symm
  have hkir : ∑ e, f e (ℓ e) * sin (s * ℓ e) = 0 := by
    have := hK 0
    simp at this
    rw [← mul_eq_zero_iff_left hs.ne', mul_sum, ← this]
    apply sum_congr rfl
    intro e _
    rw [(hsol e 0 ⟨le_rfl, (hℓ e).le⟩).2, sub_zero]
    ring
  have ha := star_trig hk (fun e => s * ℓ e) (fun e => f e (ℓ e)) (F 0)
    (fun e => mul_pos hs (hℓ e)) (by rw [← mul_sum]; exact hsL) hc hkir
  apply hne
  rw [(hsol e₁ x₁ hx₁).1, ha e₁, zero_mul]

/-! ### The path has the eigenvalue `π²/L²` -/

/-- The path with `k + 1` vertices and total length `L` has the Kirchhoff eigenvalue `π²/L²`, with
eigenfunction `cos (π t / L)` in the arclength `t` (Neumann at both ends, smooth at the interior
vertices). -/
theorem path_eigenvalue (k : ℕ) (hk : 0 < k) (L : ℝ) (hL : 0 < L) :
    (path k L hk hL).totalLength = L ∧ (path k L hk hL).IsEigenvalue (π ^ 2 / L ^ 2) := by
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  refine ⟨by simp [totalLength]; field_simp, ?_⟩
  let f : Fin k → ℝ → ℝ := fun e x => cos (π / L * ((e : ℝ) * (L / k) + x))
  let f' : Fin k → ℝ → ℝ := fun e x => -(π / L * sin (π / L * ((e : ℝ) * (L / k) + x)))
  have hd1 : ∀ e x, HasDerivAt (f e) (f' e x) x := fun e x =>
    ((((hasDerivAt_id' (x := x)).const_add ((e : ℝ) * (L / k))).const_mul (π / L)).cos).congr_deriv
      (by simp only [f']; ring)
  have hd2 : ∀ e x, HasDerivAt (f' e) (-(π ^ 2 / L ^ 2) * f e x) x := fun e x =>
    ((((hasDerivAt_id' (x := x)).const_add ((e : ℝ) * (L / k))).const_mul (π / L)).sin.const_mul
      (π / L)).neg.congr_deriv (by simp only [f]; ring)
  -- vertex values of the derivative in the direction of increasing arclength
  set G : Fin (k + 1) → ℝ := fun v => -(π / L * sin (π * (v : ℕ) / k)) with hG
  have hG0 : ∀ e : Fin k, f' e 0 = G e.castSucc := fun e => by
    simp only [f', G, Fin.val_castSucc, add_zero]; congr 3; field_simp
  have hG1 : ∀ e : Fin k, f' e (L / k) = G e.succ := fun e => by
    simp only [f', G, Fin.val_succ]; push_cast; congr 3; field_simp
  refine ⟨f, f', ⟨fun e x _ => (hd1 e x).hasDerivWithinAt, fun e x _ => (hd2 e x).hasDerivWithinAt,
    ⟨fun v => cos (π * (v : ℕ) / k), fun e => ⟨?_, ?_⟩⟩, fun v => ?_⟩, ⟨0, hk⟩, 0, ?_, ?_⟩
  · simp only [f, Fin.val_castSucc, add_zero]; congr 1; field_simp
  · simp only [f, Fin.val_succ]; push_cast; congr 1; field_simp
  · have htail : ∑ e with (path k L hk hL).tail e = v, f' e 0 = G v := by
      simp only [hG0]
      induction v using Fin.lastCases with
      | last => simp [Fin.castSucc_ne_last, G, hk']
      | cast j => simp [Fin.castSucc_inj, Finset.filter_eq']
    have hhead : ∑ e with (path k L hk hL).head e = v, f' e ((path k L hk hL).len e) = G v := by
      simp only [hG1]
      induction v using Fin.cases with
      | zero => simp [Fin.succ_ne_zero, G]
      | succ j => simp [Fin.succ_inj, Finset.filter_eq']
    rw [htail, hhead, sub_self]
  · exact ⟨le_rfl, (div_pos hL (Nat.cast_pos.2 hk)).le⟩
  · simp [f]

/-! ### Every star is beaten by another star -/

/-- Two edges of length `a` followed by `j` edges of length `ε`. -/
def twoLong (j : ℕ) (a ε : ℝ) : Fin (j + 2) → ℝ := Fin.cons a (Fin.cons a fun _ => ε)

/-- On the star with edge lengths `a, a, ε, ..., ε`, the function equal to `± cos (s (a - x))`
on the two long edges (`s = π / (2a)`) and to `0` elsewhere is an eigenfunction. -/
theorem twoLong_eigenvalue (j : ℕ) (a ε : ℝ) (ha : 0 < a) (hpos : ∀ e, 0 < twoLong j a ε e) :
    (star (j + 2) (twoLong j a ε) hpos).IsEigenvalue ((π / (2 * a)) ^ 2) := by
  set s := π / (2 * a) with hs
  let σ : Fin (j + 2) → ℝ := Fin.cons 1 (Fin.cons (-1) fun _ => 0)
  have hsa : s * a = π / 2 := by rw [hs]; field_simp
  have hcen : ∀ e, σ e * cos (s * twoLong j a ε e) = 0 := by
    intro e
    induction e using Fin.cases with
    | zero => simp [σ, twoLong, hsa]
    | succ e =>
      induction e using Fin.cases with
      | zero => simp [σ, twoLong, hsa]
      | succ e => simp [σ]
  refine ⟨fun e x => σ e * cos (s * (twoLong j a ε e - x)), fun e x => σ e * s * sin (s * (twoLong j a ε e - x)),
    ⟨fun e x _ => ?_, fun e x _ => ?_, ⟨Fin.cons 0 σ, fun e => ⟨?_, ?_⟩⟩, fun v => ?_⟩,
    0, twoLong j a ε 0, ⟨(hpos 0).le, le_rfl⟩, ?_⟩
  · exact ((((hasDerivAt_id' (x := x)).const_sub (twoLong j a ε e)).const_mul s).cos.const_mul
      (σ e)).hasDerivWithinAt.congr_deriv (by ring)
  · exact ((((hasDerivAt_id' (x := x)).const_sub (twoLong j a ε e)).const_mul s).sin.const_mul
      (σ e * s)).hasDerivWithinAt.congr_deriv (by ring)
  · simpa using hcen e
  · simp
  · have hhead : ∀ e, σ e * s * sin (s * (twoLong j a ε e - twoLong j a ε e)) = 0 := by simp
    simp only [star, hhead, Finset.sum_const_zero, sub_zero]
    by_cases hv : v = 0
    · subst hv
      simp [Fin.sum_univ_succ, σ, twoLong, hsa]
    · simp [Ne.symm hv]
  · simp [σ, twoLong]

/-- For every `μ > π²/L²` some star with `j + 2 ≥ 3` edges and total length `L` has a positive
eigenvalue `< μ`. -/
theorem star_beaten (j : ℕ) (hj : 1 ≤ j) (L μ : ℝ) (hL : 0 < L) (hμ : π ^ 2 / L ^ 2 < μ) :
    ∃ ℓ : Fin (j + 2) → ℝ, ∃ hℓ : ∀ e, 0 < ℓ e, ∑ e, ℓ e = L ∧
      ∃ ν, 0 < ν ∧ ν < μ ∧ (star (j + 2) ℓ hℓ).IsEigenvalue ν := by
  have hμ0 : 0 < μ := lt_trans (by positivity) hμ
  set r := π / √μ with hr
  have hsq : 0 < √μ := Real.sqrt_pos.2 hμ0
  have hr0 : 0 < r := div_pos pi_pos hsq
  have hr2 : r ^ 2 = π ^ 2 / μ := by rw [hr, div_pow, Real.sq_sqrt hμ0.le]
  have hrL : r < L := by
    have : π ^ 2 < μ * L ^ 2 := by rwa [div_lt_iff₀ (by positivity)] at hμ
    have : r ^ 2 < L ^ 2 := by rw [hr2, div_lt_iff₀ hμ0]; linarith
    nlinarith
  obtain ⟨t, ht⟩ : ∃ t, t = (L + r) / 2 := ⟨_, rfl⟩
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  have hpos : ∀ e, 0 < twoLong j (t / 2) ((L - t) / j) e := by
    intro e
    induction e using Fin.cases with
    | zero => simp [twoLong]; linarith
    | succ e =>
      induction e using Fin.cases with
      | zero => simp [twoLong]; linarith
      | succ e => simp only [twoLong, Fin.cons_succ]; exact div_pos (by linarith) hj'
  refine ⟨_, hpos, ?_, (π / (2 * (t / 2))) ^ 2,
    pow_pos (div_pos pi_pos (by linarith)) 2, ?_, twoLong_eigenvalue j _ _
    (by linarith) hpos⟩
  · simp [twoLong, Fin.sum_univ_succ]; field_simp; ring
  · have h1 : π / t < π / r := div_lt_div_of_pos_left pi_pos hr0 (by linarith)
    have h2 : (π / r) ^ 2 = μ := by rw [div_pow, hr2]; field_simp
    rw [show 2 * (t / 2) = t by ring, ← h2]
    exact pow_lt_pow_left₀ h1 (div_pos pi_pos (by linarith)).le two_ne_zero

/-! ### Main results -/

/-- The set of positive Kirchhoff eigenvalues of `G`. -/
def posEig {n : ℕ} (G : MetricGraph n) : Set ℝ := {lam | 0 < lam ∧ G.IsEigenvalue lam}

/-- For `k ≥ 3` edges and length `L`: every positive eigenvalue `μ` of every star exceeds `π²/L²`,
which is an eigenvalue of the path with the same vertex count and length; and some other star with
the same vertex count and length has a positive eigenvalue `< μ`. -/
theorem star_not_minimal (k : ℕ) (hk : 3 ≤ k) (L : ℝ) (hL : 0 < L) (ℓ : Fin k → ℝ)
    (hℓ : ∀ e, 0 < ℓ e) (hsum : ∑ e, ℓ e = L) (μ : ℝ) (hμ : μ ∈ posEig (star k ℓ hℓ)) :
    π ^ 2 / L ^ 2 < μ ∧ (path k L (by omega) hL).totalLength = L ∧
      π ^ 2 / L ^ 2 ∈ posEig (path k L (by omega) hL) ∧
      ∃ ℓ' : Fin k → ℝ, ∃ hℓ' : ∀ e, 0 < ℓ' e, ∑ e, ℓ' e = L ∧
        ∃ ν ∈ posEig (star k ℓ' hℓ'), ν < μ := by
  have hlt : π ^ 2 / L ^ 2 < μ := by
    by_contra h
    exact star_no_eigenvalue_le k hk ℓ hℓ μ hμ.1 (by rw [hsum]; exact not_lt.1 h) hμ.2
  obtain ⟨hP1, hP2⟩ := path_eigenvalue k (by omega) L hL
  refine ⟨hlt, hP1, ⟨by positivity, hP2⟩, ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  obtain ⟨ℓ', hℓ', hs', ν, hν, hνμ, hνe⟩ := star_beaten j (by omega) L μ hL hlt
  exact ⟨ℓ', hℓ', hs', ν, ⟨hν, hνe⟩, hνμ⟩

/-- **Disproof (all metric graphs).** For `n = k + 1 ≥ 4` vertices and total length `L > 0`, no
star `K_{1,k}` (with any edge lengths summing to `L`) has a first positive eigenvalue that is at
most every positive Kirchhoff eigenvalue of every metric graph with `n` vertices and length `L`. -/
theorem not_star_minimizer (k : ℕ) (hk : 3 ≤ k) (L : ℝ) (hL : 0 < L) :
    ¬ ∃ (ℓ : Fin k → ℝ) (hℓ : ∀ e, 0 < ℓ e), ∑ e, ℓ e = L ∧
      ∃ μ, IsLeast (posEig (star k ℓ hℓ)) μ ∧
        ∀ G : MetricGraph (k + 1), G.totalLength = L → ∀ lam ∈ posEig G, μ ≤ lam := by
  rintro ⟨ℓ, hℓ, hsum, μ, hμ, hmin⟩
  obtain ⟨hlt, hP1, hP2, -⟩ := star_not_minimal k hk L hL ℓ hℓ hsum μ hμ.1
  exact absurd (hmin _ hP1 _ hP2) (not_le.2 hlt)

/-- **Disproof (stars only).** The same holds when the competitors are only the stars `K_{1,k}`
with total length `L` (so no vertex of degree two is used). -/
theorem not_star_minimizer_among_stars (k : ℕ) (hk : 3 ≤ k) (L : ℝ) (hL : 0 < L) :
    ¬ ∃ (ℓ : Fin k → ℝ) (hℓ : ∀ e, 0 < ℓ e), ∑ e, ℓ e = L ∧
      ∃ μ, IsLeast (posEig (star k ℓ hℓ)) μ ∧
        ∀ (ℓ' : Fin k → ℝ) (hℓ' : ∀ e, 0 < ℓ' e), ∑ e, ℓ' e = L →
          ∀ ν ∈ posEig (star k ℓ' hℓ'), μ ≤ ν := by
  rintro ⟨ℓ, hℓ, hsum, μ, hμ, hmin⟩
  obtain ⟨-, -, -, ℓ', hℓ', hs', ν, hν, hνμ⟩ := star_not_minimal k hk L hL ℓ hℓ hsum μ hμ.1
  exact absurd (hmin ℓ' hℓ' hs' ν hν) (not_le.2 hνμ)

end C810
