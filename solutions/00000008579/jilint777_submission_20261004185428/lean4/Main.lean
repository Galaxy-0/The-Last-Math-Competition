/-!
# Conjecture 00000008579: the partition multiplicity law for the Ornstein–Uhlenbeck operator

The conjecture (paraphrased): for the Ornstein–Uhlenbeck operator on Wiener space,
(1) the spectrum of `N = -L` is `{0, 1, 2, …}` ("Hermite spectrum law");
(2) **the multiplicity of the eigenvalue `n` is the partition number `p(n)`** ("partition
    multiplicity law");
(3) the spectral counting function has Hardy–Ramanujan asymptotics;
(4) the second-order correction is the Rademacher series.

We refute clause (2), hence the conjunction.  Everything is defined from scratch in core Lean 4:

* A polynomial in the Gaussian coordinates `x_0, x_1, …` is its integer coefficient map
  `f : (ℕ → ℕ) → ℤ` (`f β` is the coefficient of `x^β = ∏ x_i^{β_i}`).  `IsPoly d f` says that
  `f` has finite support and only involves `x_0, …, x_{d-1}`.
* `deriv i` is `∂/∂x_i` and `mulX i` is multiplication by `x_i`, both defined on coefficients;
  `L d f = Σ_{i<d} (∂_i ∂_i f - x_i ∂_i f)` is the Ornstein–Uhlenbeck generator on polynomials of
  the standard Gaussian measure on `ℝ^d`.  Polynomials are the core of the generator, and the
  eigenvectors exhibited below are polynomials, so lower bounds on multiplicities are exact.
* `Eig d n f` : `f` is a polynomial in `d` variables with `N f = n f`, i.e. `L d f = -n f`.
  `MultGE d n m` : there are `m` linearly independent such `f` (over `ℤ`, equivalently over `ℚ`).
  `Mult d n m` : the multiplicity is exactly `m` (`≥ m` and not `≥ m + 1`).
* The Wiener space (infinitely many coordinates) is the union over `d` of the cylinder
  polynomials; `L` is consistent across `d` (`L_eq_of_isPoly`), and `MultCyl` is the multiplicity
  there.
* `p n` is the number of partitions of `n`, by an enumeration proved to list exactly the
  partitions.

Results:
* `partitionLaw_false d : ¬ PartitionLaw d` for EVERY dimension `d` (`d = 0`: fails at `n = 1`;
  `d = 1`: fails at `n = 2`, and at every `n ≥ 2`; `d ≥ 2`: fails at `n = 1`).
* `partitionLawCyl_false : ¬ PartitionLawCyl`: on Wiener space every `n ≥ 1` has infinite
  multiplicity (`multCyl_infinite`).
* `conjecture_00000008579_false`, `conjecture_00000008579_false_wiener`: the conjunction is false
  whatever clauses (1), (3), (4) mean.
-/

namespace OU

/-! ## 1. Polynomials and the operators `∂_i`, `x_i`, `L` -/

/-- A multi-index: `β i` is the exponent of the variable `x_i`. -/
abbrev MIdx := Nat → Nat

/-- A polynomial with integer coefficients in `x_0, x_1, …`, given by its coefficient map:
`f β` is the coefficient of the monomial `x^β = ∏ x_i ^ (β i)`. -/
abbrev Poly := MIdx → Int

/-- `upd β i v` is the multi-index `β` with the `i`-th exponent replaced by `v`. -/
def upd (β : MIdx) (i v : Nat) : MIdx := fun j => if j = i then v else β j

@[simp] theorem upd_self (β : MIdx) (i v : Nat) : upd β i v i = v := by simp [upd]

theorem upd_upd (β : MIdx) (i a b : Nat) : upd (upd β i a) i b = upd β i b := by
  funext j; by_cases h : j = i <;> simp [upd, h]

theorem upd_eq_self (β : MIdx) (i : Nat) : upd β i (β i) = β := by
  funext j; by_cases h : j = i <;> simp [upd, h]

/-- Partial derivative `∂/∂x_i`: the coefficient of `x^β` in `∂_i f` is `(β_i + 1) · f_{β+e_i}`. -/
def deriv (i : Nat) (f : Poly) : Poly := fun β => ((β i : Int) + 1) * f (upd β i (β i + 1))

/-- Multiplication by `x_i`: the coefficient of `x^β` in `x_i f` is `f_{β-e_i}` (and `0` if
`β_i = 0`). -/
def mulX (i : Nat) (f : Poly) : Poly := fun β => if β i = 0 then 0 else f (upd β i (β i - 1))

/-- `isum d F = F 0 + ⋯ + F (d-1)`. -/
def isum : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | d + 1, F => isum d F + F d

/-- **The Ornstein–Uhlenbeck generator** in `d` Gaussian coordinates:
`L f = Σ_{i<d} (∂_i ∂_i f - x_i ∂_i f)` (`= Δf - x·∇f`).  The number operator is `N = -L`. -/
def L (d : Nat) (f : Poly) : Poly := fun β =>
  isum d fun i => deriv i (deriv i f) β - mulX i (deriv i f) β

/-- Sanity check: `∂_i` and `x_i` satisfy the canonical commutation relation `[∂_i, x_i] = 1`. -/
theorem deriv_mulX_comm (i : Nat) (f : Poly) (β : MIdx) :
    deriv i (mulX i f) β - mulX i (deriv i f) β = f β := by
  simp only [deriv, mulX, upd_self, upd_upd, Nat.add_sub_cancel, upd_eq_self,
    if_neg (Nat.succ_ne_zero _)]
  by_cases h : β i = 0
  · rw [if_pos h, h]; simp
  · rw [if_neg h]
    have e : β i - 1 + 1 = β i := by omega
    have e2 : ((β i - 1 : Nat) : Int) + 1 = (β i : Int) := by omega
    rw [e, e2, upd_eq_self, Int.add_mul, Int.one_mul]
    omega

theorem dd_apply (i : Nat) (f : Poly) (β : MIdx) :
    deriv i (deriv i f) β = ((β i : Int) + 1) * ((β i : Int) + 2) * f (upd β i (β i + 2)) := by
  simp only [deriv, upd_self, upd_upd]
  have e : ((β i + 1 : Nat) : Int) + 1 = (β i : Int) + 2 := by omega
  rw [e, Int.mul_assoc]

theorem xd_apply (i : Nat) (f : Poly) (β : MIdx) :
    mulX i (deriv i f) β = (β i : Int) * f β := by
  simp only [mulX, deriv, upd_self, upd_upd]
  by_cases h : β i = 0
  · rw [if_pos h, h]; simp
  · rw [if_neg h]
    have e : β i - 1 + 1 = β i := by omega
    have e2 : ((β i - 1 : Nat) : Int) + 1 = (β i : Int) := by omega
    rw [e, e2, upd_eq_self]

/-- Coefficient formula: `(L f)_β = Σ_{i<d} ((β_i+1)(β_i+2) f_{β+2e_i} - β_i f_β)`. -/
theorem L_apply (d : Nat) (f : Poly) (β : MIdx) :
    L d f β = isum d fun i =>
      ((β i : Int) + 1) * ((β i : Int) + 2) * f (upd β i (β i + 2)) - (β i : Int) * f β := by
  simp only [L, dd_apply, xd_apply]

/-! ## 2. Finite sums -/

theorem isum_congr {d : Nat} {F G : Nat → Int} (h : ∀ i, i < d → F i = G i) :
    isum d F = isum d G := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [isum]; rw [ih (fun i hi => h i (by omega)), h d (by omega)]

theorem isum_zero {d : Nat} {F : Nat → Int} (h : ∀ i, i < d → F i = 0) : isum d F = 0 := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [isum]; rw [ih (fun i hi => h i (by omega)), h d (by omega)]; rfl

theorem isum_neg (d : Nat) (F : Nat → Int) : isum d (fun i => -F i) = -isum d F := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [isum]; rw [ih]; omega

theorem isum_single {d i : Nat} {F : Nat → Int} (hi : i < d)
    (h : ∀ j, j < d → j ≠ i → F j = 0) : isum d F = F i := by
  induction d with
  | zero => omega
  | succ d ih =>
    simp only [isum]
    by_cases hid : i = d
    · subst hid
      rw [isum_zero (fun j hj => h j (by omega) (by omega))]; omega
    · rw [ih (by omega) (fun j hj hji => h j (by omega) hji), h d (by omega) (fun e => hid e.symm)]
      omega

theorem isum_trunc {m' : Nat} {F : Nat → Int} :
    ∀ k, (∀ i, m' ≤ i → i < m' + k → F i = 0) → isum (m' + k) F = isum m' F
  | 0, _ => rfl
  | k + 1, h => by
    show isum (m' + k) F + F (m' + k) = isum m' F
    rw [isum_trunc k (fun i h1 h2 => h i h1 (by omega)), h (m' + k) (by omega) (by omega)]
    omega

theorem isum_interval (a k D : Nat) :
    isum D (fun j => ((if a ≤ j ∧ j < a + k then 1 else 0 : Nat) : Int)) =
      ((min D (a + k) - min D a : Nat) : Int) := by
  induction D with
  | zero => simp [isum]
  | succ D ih =>
    simp only [isum]; rw [ih]
    split <;> omega

/-! ## 3. Polynomials in `d` variables, eigenvectors, multiplicities -/

/-- `f` only involves the variables `x_0, …, x_{d-1}`. -/
def InVars (d : Nat) (f : Poly) : Prop := ∀ β, f β ≠ 0 → ∀ j, d ≤ j → β j = 0

/-- All exponents occurring in `f` are bounded (with `InVars` this is finite support). -/
def Bounded (f : Poly) : Prop := ∃ K, ∀ β, f β ≠ 0 → ∀ j, β j < K

/-- `f` is a polynomial in `x_0, …, x_{d-1}`. -/
def IsPoly (d : Nat) (f : Poly) : Prop := InVars d f ∧ Bounded f

/-- `f` is a polynomial in `d` Gaussian coordinates with `N f = n f`, i.e. `L f = -n f`. -/
def Eig (d n : Nat) (f : Poly) : Prop := IsPoly d f ∧ ∀ β, L d f β = -(n : Int) * f β

/-- The linear combination `Σ_{i<m} c_i v_i`. -/
def combo (m : Nat) (c : Nat → Int) (v : Nat → Poly) : Poly := fun β => isum m fun i => c i * v i β

/-- `v_0, …, v_{m-1}` are linearly independent (over `ℤ`; clearing denominators, the same as
over `ℚ`). -/
def LinIndep (m : Nat) (v : Nat → Poly) : Prop :=
  ∀ c : Nat → Int, (∀ β, combo m c v β = 0) → ∀ i, i < m → c i = 0

/-- The eigenvalue `n` of `N` on polynomials in `d` variables has multiplicity `≥ m`. -/
def MultGE (d n m : Nat) : Prop :=
  ∃ v : Nat → Poly, (∀ i, i < m → Eig d n (v i)) ∧ LinIndep m v

/-- The eigenvalue `n` has multiplicity exactly `m` (the rank of the eigenspace). -/
def Mult (d n m : Nat) : Prop := MultGE d n m ∧ ¬ MultGE d n (m + 1)

theorem linIndep_mono {m m' : Nat} {v : Nat → Poly} (h : LinIndep m v) (hm : m' ≤ m) :
    LinIndep m' v := by
  intro c hc i hi
  have key := h (fun j => if j < m' then c j else 0) (fun β => by
    have e : m = m' + (m - m') := by omega
    simp only [combo]
    rw [e, isum_trunc (m - m') (fun j h1 _ => by simp [Nat.not_lt.mpr h1])]
    have := hc β
    simp only [combo] at this
    rw [← this]
    exact isum_congr (fun j hj => by simp [hj])) i (by omega)
  simpa [hi] using key

theorem multGE_mono {d n m m' : Nat} (h : MultGE d n m) (hm : m' ≤ m) : MultGE d n m' := by
  obtain ⟨v, hv, hi⟩ := h
  exact ⟨v, fun i hi' => hv i (by omega), linIndep_mono hi hm⟩

/-! ## 4. Monomials and squarefree eigenvectors -/

open Classical in
/-- The monomial `x^α`. -/
noncomputable def mono (α : MIdx) : Poly := fun β => if β = α then 1 else 0

theorem mono_self (α : MIdx) : mono α α = 1 := by simp [mono]

theorem mono_ne {α β : MIdx} (h : β ≠ α) : mono α β = 0 := by simp [mono, h]

theorem isPoly_mono {d : Nat} {α : MIdx} (hsq : ∀ j, α j ≤ 1) (hv : ∀ j, d ≤ j → α j = 0) :
    IsPoly d (mono α) := by
  refine ⟨fun β hβ j hj => ?_, ⟨2, fun β hβ j => ?_⟩⟩
  · by_cases h : β = α
    · rw [h]; exact hv j hj
    · exact absurd (mono_ne h) hβ
  · by_cases h : β = α
    · rw [h]; have := hsq j; omega
    · exact absurd (mono_ne h) hβ

/-- On a squarefree monomial, `∂_i²` vanishes, so `L x^α = -(Σ_{j<d} α_j) x^α`. -/
theorem L_mono {d : Nat} {α : MIdx} (hsq : ∀ j, α j ≤ 1) (β : MIdx) :
    L d (mono α) β = -(isum d fun j => (α j : Int)) * mono α β := by
  rw [L_apply]
  have h1 : ∀ i, mono α (upd β i (β i + 2)) = 0 := fun i => mono_ne (fun h => by
    have := congrFun h i; rw [upd_self] at this; have := hsq i; omega)
  simp only [h1, Int.mul_zero, Int.zero_sub]
  by_cases h : β = α
  · rw [h, mono_self, Int.mul_one, isum_neg]
    exact congrArg _ (isum_congr (fun i _ => Int.mul_one _))
  · rw [mono_ne h, Int.mul_zero]
    exact isum_zero (fun i _ => by rw [Int.mul_zero]; rfl)

theorem eig_mono {d n : Nat} {α : MIdx} (hsq : ∀ j, α j ≤ 1) (hv : ∀ j, d ≤ j → α j = 0)
    (hdeg : isum d (fun j => (α j : Int)) = n) : Eig d n (mono α) :=
  ⟨isPoly_mono hsq hv, fun β => by rw [L_mono hsq β, hdeg]⟩

/-- Monomials with distinct exponents are linearly independent. -/
theorem linIndep_monos (m : Nat) (α : Nat → MIdx)
    (hinj : ∀ i j, i < m → j < m → α i = α j → i = j) :
    LinIndep m (fun i => mono (α i)) := by
  intro c hc i hi
  have := hc (α i)
  simp only [combo] at this
  rw [isum_single hi (fun j hj hji => by
    rw [mono_ne (fun h => hji (hinj i j hi hj h).symm), Int.mul_zero]), mono_self,
    Int.mul_one] at this
  exact this

/-- The block multi-index `x_a x_{a+1} ⋯ x_{a+k-1}` (squarefree, degree `k`). -/
def blk (a k : Nat) : MIdx := fun j => if a ≤ j ∧ j < a + k then 1 else 0

theorem blk_le_one (a k j : Nat) : blk a k j ≤ 1 := by unfold blk; split <;> omega

theorem isum_blk (a k D : Nat) (h : a + k ≤ D) : isum D (fun j => (blk a k j : Int)) = k := by
  unfold blk; rw [isum_interval]; omega

/-- The coordinate function `x_i = W(e_i)`. -/
noncomputable def x (i : Nat) : Poly := mono (blk i 1)

theorem blk_one (i j : Nat) : blk i 1 j = if j = i then 1 else 0 := by
  unfold blk
  by_cases h : j = i
  · rw [if_pos (by omega), if_pos h]
  · rw [if_neg (by omega), if_neg h]

/-- `x_i` is an eigenvector of `N` with eigenvalue `1` in any dimension `d > i`. -/
theorem eig_x {d i : Nat} (hi : i < d) : Eig d 1 (x i) :=
  eig_mono (blk_le_one i 1) (fun j hj => by unfold blk; split <;> omega)
    (isum_blk i 1 d (by omega))

/-- `L x_0 = -x_0` and `L x_1 = -x_1` (in `d ≥ 2` variables), as polynomials. -/
theorem L_x0_x1 (d : Nat) (hd : 2 ≤ d) :
    L d (x 0) = (fun β => -(x 0 β)) ∧ L d (x 1) = (fun β => -(x 1 β)) := by
  constructor <;> funext β
  · rw [(eig_x (d := d) (i := 0) (by omega)).2 β]; simp
  · rw [(eig_x (d := d) (i := 1) (by omega)).2 β]; simp

/-- `x_0, …, x_{m-1}` are linearly independent. -/
theorem linIndep_x (m : Nat) : LinIndep m x :=
  linIndep_monos m (fun i => blk i 1) (fun i j _ _ h => by
    have := congrFun h i; simp only [blk_one, if_pos rfl] at this
    by_cases hij : i = j
    · exact hij
    · rw [if_neg hij] at this; exact absurd this (by decide))

/-- `MultGE d n m` whenever `n ≥ 1` and `n m ≤ d`: the products `x_{ni} ⋯ x_{ni+n-1}`, `i < m`,
are independent eigenvectors with eigenvalue `n`.  (So `mult_d(1) ≥ d`, `mult_d(n) ≥ ⌊d/n⌋`.) -/
theorem multGE_blocks (d n m : Nat) (hn : 1 ≤ n) (h : n * m ≤ d) : MultGE d n m := by
  refine ⟨fun i => mono (blk (n * i) n), fun i hi => ?_, linIndep_monos m _ ?_⟩
  · have hb : n * i + n ≤ d := by
      have : n * (i + 1) ≤ n * m := Nat.mul_le_mul_left n hi
      rw [Nat.mul_succ] at this; omega
    exact eig_mono (blk_le_one _ _) (fun j hj => by unfold blk; split <;> omega)
      (isum_blk _ _ _ hb)
  · intro i j _ _ hij
    have e1 : blk (n * j) n (n * i) = 1 := by
      rw [← hij]; unfold blk; rw [if_pos]; omega
    have e2 : blk (n * i) n (n * j) = 1 := by
      rw [hij]; unfold blk; rw [if_pos]; omega
    unfold blk at e1 e2
    by_cases c1 : n * j ≤ n * i ∧ n * i < n * j + n
    · by_cases c2 : n * i ≤ n * j ∧ n * j < n * i + n
      · have hne : n * i = n * j := by omega
        exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < n) hne
      · rw [if_neg c2] at e2; exact absurd e2 (by decide)
    · rw [if_neg c1] at e1; exact absurd e1 (by decide)

/-! ## 5. One variable: every eigenspace has dimension at most one -/

/-- The one-variable multi-index `x_0^k`. -/
def s (k : Nat) : MIdx := fun j => if j = 0 then k else 0

@[simp] theorem s_zero (k : Nat) : s k 0 = k := rfl

theorem upd_s (k v : Nat) : upd (s k) 0 v = s v := by
  funext j; by_cases h : j = 0 <;> simp [upd, s, h]

theorem eq_s (β : MIdx) (h : ∀ j, 1 ≤ j → β j = 0) : β = s (β 0) := by
  funext j
  by_cases hj : j = 0
  · subst hj; rfl
  · simp only [s, if_neg hj]; exact h j (by omega)

theorem s_inj {a b : Nat} (h : s a = s b) : a = b := by
  have := congrFun h 0; simpa using this

/-- The eigen-equation `L f = -n f` in one variable, read on coefficients `g k = f(x^k)`. -/
def Rec (n : Nat) (g : Nat → Int) : Prop :=
  ∀ k : Nat, ((k : Int) + 1) * ((k : Int) + 2) * g (k + 2) - (k : Int) * g k = -(n : Int) * g k

theorem eig1_rec {n : Nat} {f : Poly} (hf : Eig 1 n f) : Rec n (fun k => f (s k)) := by
  intro k
  show ((k : Int) + 1) * ((k : Int) + 2) * f (s (k + 2)) - (k : Int) * f (s k) = -(n : Int) * f (s k)
  have := hf.2 (s k)
  rw [L_apply] at this
  simp only [isum, s_zero, upd_s] at this
  omega

theorem rec_step {n : Nat} {g : Nat → Int} (hrec : Rec n g) (k : Nat) (hk : k ≠ n)
    (h2 : g (k + 2) = 0) : g k = 0 := by
  have e := hrec k
  rw [h2, Int.mul_zero, Int.zero_sub, Int.neg_mul] at e
  have e2 : ((k : Int) - n) * g k = 0 := by rw [Int.sub_mul]; omega
  rcases Int.mul_eq_zero.mp e2 with h | h
  · omega
  · exact h

/-- A finitely supported solution of the recursion with `g n = 0` vanishes identically. -/
theorem rec_zero {n K : Nat} {g : Nat → Int} (hK : ∀ k, K ≤ k → g k = 0) (hrec : Rec n g)
    (hn : g n = 0) : ∀ k, g k = 0 := by
  have above : ∀ t k, n < k → K ≤ k + 2 * t → g k = 0 := by
    intro t
    induction t with
    | zero => intro k _ hk; exact hK k (by omega)
    | succ t ih =>
      intro k hk hK'
      exact rec_step hrec k (by omega) (ih (k + 2) (by omega) (by omega))
  have below : ∀ t k, k ≤ n + 1 → n + 1 ≤ k + t → g k = 0 := by
    intro t
    induction t with
    | zero => intro k h1 h2; exact above K k (by omega) (by omega)
    | succ t ih =>
      intro k h1 h2
      by_cases h3 : n + 1 ≤ k + t
      · exact ih k h1 h3
      · by_cases h4 : k = n
        · rw [h4]; exact hn
        · exact rec_step hrec k h4 (ih (k + 2) (by omega) (by omega))
  intro k
  by_cases hk : n < k
  · exact above K k hk (by omega)
  · exact below (n + 1) k (by omega) (by omega)

theorem rec_lin {n : Nat} {g0 g1 : Nat → Int} (a b : Int) (h0 : Rec n g0) (h1 : Rec n g1) :
    Rec n (fun k => a * g0 k + b * g1 k) := by
  intro k
  have e0 := congrArg (a * ·) (h0 k)
  have e1 := congrArg (b * ·) (h1 k)
  simp only [Int.mul_add, Int.mul_sub, Int.neg_mul, Int.mul_neg] at e0 e1 ⊢
  simp only [Int.mul_left_comm a, Int.mul_left_comm b] at e0 e1 ⊢
  omega

theorem bounded_s {f : Poly} (hf : Bounded f) : ∃ K, ∀ k, K ≤ k → f (s k) = 0 := by
  obtain ⟨K, hK⟩ := hf
  exact ⟨K, fun k hk => Classical.byContradiction fun h => by
    have := hK _ h 0; rw [s_zero] at this; omega⟩

/-- A one-variable eigenvector with eigenvalue `n` whose `x^n`-coefficient vanishes is zero. -/
theorem eig1_zero {n : Nat} {f : Poly} (hf : Eig 1 n f) (hn : f (s n) = 0) : ∀ β, f β = 0 := by
  obtain ⟨K, hK⟩ := bounded_s hf.1.2
  have hz := rec_zero hK (eig1_rec hf) hn
  intro β
  apply Classical.byContradiction
  intro h
  rw [eq_s β (hf.1.1 β h)] at h
  exact h (hz _)

/-- **Any two one-variable eigenvectors for the same eigenvalue are proportional**:
`g_n · f = f_n · g`, where `f_n` is the coefficient of `x^n`.  (No degree bound is assumed.) -/
theorem eig1_prop {n : Nat} {f g : Poly} (hf : Eig 1 n f) (hg : Eig 1 n g) :
    ∀ β, g (s n) * f β = f (s n) * g β := by
  have hk : ∀ k, g (s n) * f (s k) + -f (s n) * g (s k) = 0 := by
    obtain ⟨K0, hK0⟩ := bounded_s hf.1.2
    obtain ⟨K1, hK1⟩ := bounded_s hg.1.2
    refine rec_zero (g := fun k => g (s n) * f (s k) + -f (s n) * g (s k)) (K := K0 + K1)
      (fun k hk => ?_) (rec_lin _ _ (eig1_rec hf) (eig1_rec hg)) ?_
    · simp only; rw [hK0 k (by omega), hK1 k (by omega)]; simp
    · simp only; rw [Int.mul_comm (g (s n)), Int.neg_mul]; omega
  intro β
  have key : g (s n) * f β + -f (s n) * g β = 0 := by
    by_cases h0 : f β = 0
    · by_cases h1 : g β = 0
      · rw [h0, h1]; simp
      · rw [eq_s β (hg.1.1 β h1)]; exact hk _
    · rw [eq_s β (hf.1.1 β h0)]; exact hk _
  rw [Int.neg_mul] at key
  omega

/-- **In one variable, every eigenvalue of `N` has multiplicity at most `1`.** -/
theorem mult1_le (n : Nat) : ¬ MultGE 1 n 2 := by
  rintro ⟨v, hv, hind⟩
  have e0 := hv 0 (by decide)
  have e1 := hv 1 (by decide)
  have hrel : ∀ β, v 1 (s n) * v 0 β + -v 0 (s n) * v 1 β = 0 := by
    intro β; have := eig1_prop e0 e1 β; rw [Int.neg_mul]; omega
  have hc := hind (fun i => if i = 0 then v 1 (s n) else -v 0 (s n)) (fun β => by
    simp only [combo, isum]; simpa using hrel β)
  have c1 := hc 1 (by decide)
  simp only [if_neg (by decide : (1 : Nat) ≠ 0)] at c1
  have z := eig1_zero e0 (by omega)
  have := hind (fun i => if i = 0 then 1 else 0) (fun β => by simp [combo, isum, z β]) 0
    (by decide)
  simp at this

/-- Dimension `0` (constants only): no eigenvector for `n ≥ 1`. -/
theorem mult0_le (n : Nat) (hn : 1 ≤ n) : ¬ MultGE 0 n 1 := by
  rintro ⟨v, hv, hind⟩
  have e := (hv 0 (by decide)).2
  have z : ∀ β, v 0 β = 0 := by
    intro β
    have := e β
    rw [L_apply] at this
    simp only [isum] at this
    rcases Int.mul_eq_zero.mp this.symm with h | h
    · omega
    · exact h
  have := hind (fun _ => 1) (fun β => by simp [combo, isum, z β]) 0 (by decide)
  simp at this

/-! ## 6. Non-vacuity: `x² - 1 = H_2`, and the exact one-variable multiplicities -/

/-- The Hermite polynomial `H_2(x_0) = x_0² - 1`. -/
noncomputable def H2 : Poly := fun β => mono (s 2) β - mono (s 0) β

theorem mono_s_s {a b : Nat} (h : a ≠ b) : mono (s a) (s b) = 0 :=
  mono_ne (fun e => h (s_inj e).symm)

/-- `H_2 = x² - 1` is an eigenvector: `L H_2 = -2 H_2`, i.e. `N H_2 = 2 H_2`. -/
theorem eig_H2 : Eig 1 2 H2 := by
  have hz : ∀ β, β ≠ s 2 → β ≠ s 0 → H2 β = 0 := fun β h2 h0 => by
    simp only [H2, mono_ne h2, mono_ne h0]; rfl
  refine ⟨⟨fun β hβ j hj => ?_, ⟨3, fun β hβ j => ?_⟩⟩, fun β => ?_⟩
  · by_cases h2 : β = s 2
    · rw [h2]; simp [s]; omega
    · by_cases h0 : β = s 0
      · rw [h0]; simp [s]
      · exact absurd (hz β h2 h0) hβ
  · by_cases h2 : β = s 2
    · rw [h2]; simp only [s]; split <;> omega
    · by_cases h0 : β = s 0
      · rw [h0]; simp only [s]; split <;> omega
      · exact absurd (hz β h2 h0) hβ
  · rw [L_apply]
    simp only [isum]
    by_cases h2 : β = s 2
    · rw [h2, s_zero, upd_s]
      simp only [H2, mono_self, mono_s_s (by decide : (0 : Nat) ≠ 2), mono_s_s (by decide : (2 : Nat) ≠ 0),
        mono_s_s (by decide : (0 : Nat) ≠ 4), mono_s_s (by decide : (2 : Nat) ≠ 4)]
      omega
    · by_cases h0 : β = s 0
      · rw [h0, s_zero, upd_s]
        simp only [H2, mono_self, mono_s_s (by decide : (0 : Nat) ≠ 2), mono_s_s (by decide : (2 : Nat) ≠ 0),
        mono_s_s (by decide : (0 : Nat) ≠ 4), mono_s_s (by decide : (2 : Nat) ≠ 4)]
        omega
      · have hu2 : upd β 0 (β 0 + 2) ≠ s 2 := fun e => by
          apply h0
          funext j
          have := congrFun e j
          by_cases hj : j = 0
          · subst hj; simp [upd, s] at this ⊢; omega
          · simpa [upd, s, hj] using this
        have hu0 : upd β 0 (β 0 + 2) ≠ s 0 := fun e => by
          have := congrFun e 0; simp [upd, s] at this
        rw [hz β h2 h0, hz _ hu2 hu0]; simp

theorem linIndep_one {f : Poly} {β : MIdx} (h : f β ≠ 0) : LinIndep 1 (fun _ => f) := by
  intro c hc i hi
  have := hc β
  simp only [combo, isum, Int.zero_add] at this
  have hi0 : i = 0 := by omega
  subst hi0
  rcases Int.mul_eq_zero.mp this with h' | h'
  · exact h'
  · exact absurd h' h

/-- Every one-variable polynomial `f` (of any degree) with `N f = 2 f` is `c · (x² - 1)`,
`c = f_2`: e.g. `a + b x + c x²` is an eigenvector iff `b = 0` and `a = -c`. -/
theorem eig2_eq_H2 {f : Poly} (hf : Eig 1 2 f) : ∀ β, f β = f (s 2) * H2 β := by
  intro β
  have := eig1_prop hf eig_H2 β
  have h1 : H2 (s 2) = 1 := by
    simp only [H2, mono_self, mono_s_s (by decide : (0 : Nat) ≠ 2)]; rfl
  rw [h1, Int.one_mul] at this
  exact this

/-- In one variable the multiplicities of `0, 1, 2` are exactly `1, 1, 1`, with eigenvectors
`1, x, x² - 1`; the partition law would require `p(2) = 2` at `n = 2`. -/
theorem mult1_exact : Mult 1 0 1 ∧ Mult 1 1 1 ∧ Mult 1 2 1 := by
  refine ⟨⟨⟨fun _ => mono (s 0), fun _ _ => ?_, linIndep_one (β := s 0) (by rw [mono_self]; decide)⟩,
      mult1_le 0⟩,
    ⟨⟨fun _ => x 0, fun _ _ => eig_x (by decide),
      linIndep_one (β := blk 0 1) (by simp only [x, mono_self]; decide)⟩, mult1_le 1⟩,
    ⟨⟨fun _ => H2, fun _ _ => eig_H2,
      linIndep_one (β := s 2) (by simp only [H2, mono_self, mono_s_s (by decide : (0:Nat) ≠ 2)]; decide)⟩,
      mult1_le 2⟩⟩
  exact eig_mono (fun j => by simp only [s]; split <;> omega)
    (fun j hj => by simp only [s]; split <;> omega) (by simp [isum, s])

/-! ## 7. Partition numbers -/

/-- All lists of length `n` with entries `< k`. -/
def allLists : Nat → Nat → List (List Nat)
  | 0, _ => [[]]
  | n + 1, k => (List.range k).flatMap fun a => (allLists n k).map (a :: ·)

theorem mem_allLists (k : Nat) : ∀ (n : Nat) (l : List Nat),
    l.length = n → (∀ y ∈ l, y < k) → l ∈ allLists n k
  | 0, [], _, _ => List.Mem.head _
  | 0, _ :: _, h, _ => absurd h (Nat.succ_ne_zero _)
  | _ + 1, [], h, _ => absurd h.symm (Nat.succ_ne_zero _)
  | n + 1, a :: l, h, hb => by
    rw [allLists, List.mem_flatMap]
    refine ⟨a, List.mem_range.mpr (hb a (List.Mem.head _)), ?_⟩
    rw [List.mem_map]
    exact ⟨l, mem_allLists k n l (Nat.succ.inj h) (fun y hy => hb y (List.mem_cons_of_mem a hy)),
      rfl⟩

/-- `l` is a partition of `n`: positive parts, nonincreasing, summing to `n`. -/
def IsPartition (n : Nat) (l : List Nat) : Prop :=
  l.sum = n ∧ (∀ y ∈ l, 0 < y) ∧ l.Pairwise (fun a b => b ≤ a)

instance (n : Nat) (l : List Nat) : Decidable (IsPartition n l) := by
  unfold IsPartition; infer_instance

/-- All partitions of `n` (a partition has at most `n` parts, each `≤ n`). -/
def partitionsL (n : Nat) : List (List Nat) :=
  ((List.range (n + 1)).flatMap fun len => allLists len (n + 1)).filter
    fun l => decide (IsPartition n l)

/-- The partition number `p(n)`. -/
def p (n : Nat) : Nat := (partitionsL n).length

theorem le_sum_of_mem : ∀ (l : List Nat) (y : Nat), y ∈ l → y ≤ l.sum
  | [], _, h => by simp at h
  | a :: l, y, h => by
    simp only [List.mem_cons] at h
    simp only [List.sum_cons]
    rcases h with rfl | h
    · omega
    · have := le_sum_of_mem l y h; omega

theorem length_le_sum : ∀ (l : List Nat), (∀ y ∈ l, 0 < y) → l.length ≤ l.sum
  | [], _ => by simp
  | a :: l, h => by
    have ha := h a (by simp)
    have := length_le_sum l (fun y hy => h y (by simp [hy]))
    simp only [List.length_cons, List.sum_cons]
    omega

/-- `partitionsL n` lists exactly the partitions of `n` (for every `n`). -/
theorem mem_partitionsL (n : Nat) (l : List Nat) : l ∈ partitionsL n ↔ IsPartition n l := by
  unfold partitionsL
  rw [List.mem_filter]
  constructor
  · intro h; exact of_decide_eq_true h.2
  · intro h
    refine ⟨?_, decide_eq_true h⟩
    rw [List.mem_flatMap]
    have hlen := length_le_sum l h.2.1
    have hs : l.sum = n := h.1
    refine ⟨l.length, List.mem_range.mpr (by omega), mem_allLists (n + 1) _ l rfl ?_⟩
    intro y hy
    have := le_sum_of_mem l y hy
    omega

/-- `p(0..5) = 1, 1, 2, 3, 5, 7`, and the enumerations are duplicate-free (so `p` counts). -/
theorem p_values : p 0 = 1 ∧ p 1 = 1 ∧ p 2 = 2 ∧ p 3 = 3 ∧ p 4 = 5 ∧ p 5 = 7 ∧
    (partitionsL 1).Nodup ∧ (partitionsL 2).Nodup ∧ (partitionsL 3).Nodup := by
  decide +kernel

theorem two_le_length {l : List (List Nat)} {a b : List Nat} (ha : a ∈ l) (hb : b ∈ l)
    (hab : a ≠ b) : 2 ≤ l.length := by
  match l, ha, hb with
  | [], ha, _ => simp at ha
  | [_], ha, hb =>
    simp only [List.mem_singleton] at ha hb
    exact absurd (ha.trans hb.symm) hab
  | _ :: _ :: _, _, _ => simp

/-- `p(n) ≥ 2` for `n ≥ 2`: `(n)` and `(1, …, 1)` are distinct partitions of `n`. -/
theorem p_ge_two (n : Nat) (hn : 2 ≤ n) : 2 ≤ p n := by
  unfold p
  refine two_le_length ((mem_partitionsL n [n]).2 ⟨by simp, by simp; omega, by simp⟩)
    ((mem_partitionsL n (List.replicate n 1)).2
      ⟨by simp, by simp [List.mem_replicate], by simp [List.pairwise_replicate]⟩) ?_
  intro h
  have := congrArg List.length h
  simp at this
  omega

/-! ## 8. The partition multiplicity law is false in every dimension -/

/-- **Clause (2)** for the Gaussian space `ℝ^d`, *polynomial-core version*: for every `n`, the
eigenvalue `n` of `N` restricted to polynomials has multiplicity exactly `p(n)`.  `Mult d n (p n)`
has two halves: a lower bound (`MultGE d n (p n)`) and an upper bound (`¬ MultGE d n (p n + 1)`).
The `L²` law implies the upper-bound half directly, because polynomial eigenvectors are `L²`
eigenvectors.  It implies the lower-bound half only via Hermite completeness (proved in the report),
because then all `L²` eigenvectors are polynomials. -/
def PartitionLaw (d : Nat) : Prop := ∀ n, Mult d n (p n)

/-- The polynomial-core partition law fails in every dimension.
* `d ≥ 2`: the **upper-bound half** fails at `n = 1`, because `x_0, x_1` are two independent
  eigenvectors although `p(1) = 1`.  This transfers to the `L²` law with no extra input, since
  polynomial eigenvectors are `L²` eigenvectors.  The same holds on Wiener space
  (`partitionLawCyl_false`).
* `d = 1`: the **lower-bound half** fails at `n = 2`, because no two independent polynomial
  eigenvectors exist although `p(2) = 2`.  Transferring this to `L²(γ₁)` needs Hermite
  completeness (every `L²` eigenvector is a polynomial), which is proved in the report.
* `d = 0`: the lower-bound half fails at `n = 1` (on `ℝ⁰` every function is a constant
  polynomial). -/
theorem partitionLaw_false (d : Nat) : ¬ PartitionLaw d := by
  intro h
  obtain ⟨_, p1, p2, -⟩ := p_values
  match d, h with
  | 0, h =>
    have := (h 1).1; rw [p1] at this; exact mult0_le 1 (Nat.le_refl 1) this
  | 1, h =>
    have := (h 2).1; rw [p2] at this; exact mult1_le 2 this
  | d + 2, h =>
    have := (h 1).2; rw [p1] at this
    exact this (multGE_blocks (d + 2) 1 2 (Nat.le_refl 1) (by omega))

/-- `d ≥ 2`: two independent eigenvectors `x_0, x_1` for the eigenvalue `1`, while `p(1) = 1`. -/
theorem mult_one_ge_two (d : Nat) (hd : 2 ≤ d) : MultGE d 1 2 ∧ p 1 = 1 :=
  ⟨⟨x, fun i hi => eig_x (by omega), linIndep_x 2⟩, p_values.2.1⟩

/-- `d = 1`: the law fails at EVERY `n ≥ 2` (so also "for all large `n`" and shifted readings). -/
theorem d1_fails_all (n : Nat) (hn : 2 ≤ n) : ¬ Mult 1 n (p n) :=
  fun h => mult1_le n (multGE_mono h.1 (p_ge_two n hn))

/-! ## 9. Wiener space: cylinder polynomials in infinitely many coordinates -/

theorem inVars_mono {d d' : Nat} {f : Poly} (h : InVars d f) (hd : d ≤ d') : InVars d' f :=
  fun β hβ j hj => h β hβ j (by omega)

theorem L_succ {d : Nat} {f : Poly} (hf : InVars d f) (β : MIdx) : L (d + 1) f β = L d f β := by
  rw [L_apply, L_apply]
  simp only [isum]
  have h1 : f (upd β d (β d + 2)) = 0 := Classical.byContradiction fun h => by
    have := hf _ h d (Nat.le_refl d); rw [upd_self] at this; omega
  have h2 : (β d : Int) * f β = 0 := by
    by_cases hb : f β = 0
    · rw [hb, Int.mul_zero]
    · rw [hf β hb d (Nat.le_refl d)]; simp
  rw [h1, h2]; simp

theorem L_add {d : Nat} {f : Poly} (hf : InVars d f) : ∀ k β, L (d + k) f β = L d f β
  | 0, _ => rfl
  | k + 1, β => by
    rw [← Nat.add_assoc, L_succ (inVars_mono hf (Nat.le_add_right d k)), L_add hf k β]

/-- `L` is consistent across dimensions: on a polynomial in `d` and in `d'` variables,
`L_d f = L_{d'} f`.  So `L` is well defined on cylinder polynomials. -/
theorem L_eq_of_isPoly {d d' : Nat} {f : Poly} (h : InVars d f) (h' : InVars d' f) :
    L d f = L d' f := by
  funext β
  rw [← L_add h d' β, ← L_add h' d β, Nat.add_comm]

/-- `f` is a cylinder polynomial with `N f = n f`. -/
def EigCyl (n : Nat) (f : Poly) : Prop := ∃ d, Eig d n f

def MultGECyl (n m : Nat) : Prop :=
  ∃ v : Nat → Poly, (∀ i, i < m → EigCyl n (v i)) ∧ LinIndep m v

def MultCyl (n m : Nat) : Prop := MultGECyl n m ∧ ¬ MultGECyl n (m + 1)

/-- Clause (2) on Wiener space (cylinder-polynomial core).  It is refuted through its upper-bound
half, which the `L²` law implies directly. -/
def PartitionLawCyl : Prop := ∀ n, MultCyl n (p n)

/-- On Wiener space every eigenvalue `n ≥ 1` has infinitely many independent eigenvectors. -/
theorem multGECyl_all (n m : Nat) (hn : 1 ≤ n) : MultGECyl n m := by
  obtain ⟨v, hv, hi⟩ := multGE_blocks (n * m) n m hn (Nat.le_refl _)
  exact ⟨v, fun i h => ⟨n * m, hv i h⟩, hi⟩

/-- No finite multiplicity: `mult(n) = ∞` for every `n ≥ 1`. -/
theorem multCyl_infinite (n : Nat) (hn : 1 ≤ n) (m : Nat) : ¬ MultCyl n m :=
  fun h => h.2 (multGECyl_all n (m + 1) hn)

theorem partitionLawCyl_false : ¬ PartitionLawCyl :=
  fun h => multCyl_infinite 1 (Nat.le_refl 1) (p 1) (h 1)

/-! ## 10. The conjecture -/

/-- The conjecture for `ℝ^d`: clause (1) ∧ clause (2) ∧ clause (3) ∧ clause (4); clauses (1),
(3), (4) are arbitrary propositions. -/
def Conjecture (d : Nat) (SpectrumLaw HRLaw RLaw : Prop) : Prop :=
  SpectrumLaw ∧ PartitionLaw d ∧ HRLaw ∧ RLaw

def ConjectureWiener (SpectrumLaw HRLaw RLaw : Prop) : Prop :=
  SpectrumLaw ∧ PartitionLawCyl ∧ HRLaw ∧ RLaw

theorem conjecture_00000008579_false (d : Nat) (S H R : Prop) : ¬ Conjecture d S H R :=
  fun h => partitionLaw_false d h.2.1

theorem conjecture_00000008579_false_wiener (S H R : Prop) : ¬ ConjectureWiener S H R :=
  fun h => partitionLawCyl_false h.2.1

end OU

#print axioms OU.deriv_mulX_comm
#print axioms OU.L_x0_x1
#print axioms OU.linIndep_x
#print axioms OU.eig_H2
#print axioms OU.eig1_prop
#print axioms OU.mult1_le
#print axioms OU.eig2_eq_H2
#print axioms OU.mult1_exact
#print axioms OU.p_values
#print axioms OU.p_ge_two
#print axioms OU.partitionLaw_false
#print axioms OU.mult_one_ge_two
#print axioms OU.d1_fails_all
#print axioms OU.L_eq_of_isPoly
#print axioms OU.multCyl_infinite
#print axioms OU.partitionLawCyl_false
#print axioms OU.conjecture_00000008579_false
#print axioms OU.conjecture_00000008579_false_wiener
