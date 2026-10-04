/-!
# Conjecture 00000007130: the period of an Ehrhart quasi-polynomial

The conjecture says that the period of the Ehrhart quasi-polynomial of a rational polytope
equals the least common multiple of its denominators.  We refute this clause.

* **Vertex reading** (the standard "denominator" of a rational polytope: the lcm of the
  denominators of the vertex coordinates).  The triangle
  `T = conv{(0,0), (1,1/2), (2,0)}` has vertex-denominator lcm `2`, but
  `L_T(t) = #(tT ∩ ℤ²) = (t+1)(t+2)/2` for every `t ≥ 0`.  So `L_T` is a polynomial and its
  minimal period is `1 ≠ 2` (period collapse, McAllister–Woods 2005).
* **Facet reading** (lcm of the denominators of the right-hand sides of the facet
  inequalities, normals primitive).  The triangle `T₂ = conv{(0,0), (1,0), (0,1/2)}` has facets
  `x ≥ 0, y ≥ 0, x + 2y ≤ 1`, so this lcm is `1`, but its minimal period is `2`.

Everything is defined from scratch:
* rational triangles by their vertices, and membership of a lattice point in the dilate `tP`
  via rational convex-combination weights (denominators cleared);
* the lattice-point count `hcount`, which counts the integer points of a finite box that
  satisfy a list of facet inequalities;
* `Describes P fs W H`: the facet list `fs` and the box `[0, W t] × [0, H t]` capture
  exactly the lattice points of `tP`, for every `t`;
* quasi-polynomials with period `p` (`HasPeriod`) and minimal periods (`IsMinPeriod`).
-/

namespace Ehrhart

/-! ## Finite counting -/

/-- `countUpTo p n = #{x < n : p x}`. -/
def countUpTo (p : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => countUpTo p n + (if p n then 1 else 0)

/-- `sumUpTo f n = f 0 + ⋯ + f (n-1)`. -/
def sumUpTo (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumUpTo f n + f n

/-- The number of `x < n` with `a ≤ x` and `x + c ≤ e`. -/
theorem countUpTo_interval (p : Nat → Bool) (a c e : Nat)
    (hp : ∀ x, p x = true ↔ (a ≤ x ∧ x + c ≤ e)) :
    ∀ n, countUpTo p n = min n (e + 1 - c) - min n a := by
  intro n
  induction n with
  | zero => simp [countUpTo]
  | succ n ih =>
    simp only [countUpTo, ih]
    cases h : p n with
    | true =>
      have := (hp n).1 h
      simp only [if_true]
      omega
    | false =>
      have : ¬ (a ≤ n ∧ n + c ≤ e) := fun hh => by
        have := (hp n).2 hh
        rw [h] at this
        exact Bool.false_ne_true this
      simp only [Bool.false_eq_true, if_false]
      omega

theorem sumUpTo_congr (f g : Nat → Nat) :
    ∀ n, (∀ y, y < n → f y = g y) → sumUpTo f n = sumUpTo g n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro h
    simp only [sumUpTo]
    rw [ih (fun y hy => h y (by omega)), h n (by omega)]

theorem sumUpTo_shift (f : Nat → Nat) :
    ∀ n, sumUpTo f (n + 1) = f 0 + sumUpTo (fun y => f (y + 1)) n := by
  intro n
  induction n with
  | zero => simp [sumUpTo]
  | succ n ih =>
    rw [sumUpTo, ih, sumUpTo]
    omega

/-! ## Rational triangles and their dilates -/

/-- A rational number `num / den`. -/
structure RQ where
  num : Int
  den : Nat

/-- `den > 0` and the fraction is in lowest terms. -/
def RQ.Reduced (q : RQ) : Prop := 0 < q.den ∧ Nat.gcd q.num.natAbs q.den = 1

instance (q : RQ) : Decidable q.Reduced := by unfold RQ.Reduced; infer_instance

/-- `q · N` as an integer, when `q.den ∣ N`. -/
def RQ.scaleTo (q : RQ) (N : Nat) : Int := q.num * ((N / q.den : Nat) : Int)

/-- A point of `ℚ²`. -/
structure RPt where
  x : RQ
  y : RQ

/-- A triangle, given by its three vertices. -/
structure Tri where
  v0 : RPt
  v1 : RPt
  v2 : RPt

/-- The six vertex coordinates. -/
def Tri.coords (P : Tri) : List RQ := [P.v0.x, P.v0.y, P.v1.x, P.v1.y, P.v2.x, P.v2.y]

/-- All vertex coordinates are written in lowest terms. -/
def Tri.Reduced (P : Tri) : Prop := ∀ q ∈ P.coords, q.Reduced

instance (P : Tri) : Decidable P.Reduced := by unfold Tri.Reduced; infer_instance

/-- The least common multiple of the denominators of the vertex coordinates. -/
def Tri.denLcm (P : Tri) : Nat := P.coords.foldl (fun l q => Nat.lcm l q.den) 1

/-- A common denominator used only to clear fractions (the product of all denominators). -/
def Tri.denProd (P : Tri) : Nat := P.coords.foldl (fun l q => l * q.den) 1

/-- The lattice point `(x, y)` lies in the dilate `t · P`: there are rational weights
`ν_i = μ_i / M ≥ 0` (`M > 0`) with `ν_0 + ν_1 + ν_2 = t` and `(x, y) = Σ ν_i v_i`.
Fractions are cleared by multiplying by `M` and by the common denominator `N = denProd`. -/
def Tri.MemScaled (P : Tri) (t : Nat) (x y : Int) : Prop :=
  ∃ M a b c : Int, 0 < M ∧ 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = M * t ∧
    M * P.denProd * x = a * P.v0.x.scaleTo P.denProd + b * P.v1.x.scaleTo P.denProd
      + c * P.v2.x.scaleTo P.denProd ∧
    M * P.denProd * y = a * P.v0.y.scaleTo P.denProd + b * P.v1.y.scaleTo P.denProd
      + c * P.v2.y.scaleTo P.denProd

/-! ## Facet inequalities and the lattice-point count -/

/-- The closed half-plane `a1 x + a2 y ≤ b` with `b ∈ ℚ`. -/
structure Facet where
  a1 : Int
  a2 : Int
  b : RQ

/-- `(x, y)` satisfies the facet inequality of the dilate: `a1 x + a2 y ≤ t b`. -/
def Facet.holds (f : Facet) (t : Nat) (x y : Int) : Bool :=
  decide ((f.b.den : Int) * (f.a1 * x + f.a2 * y) ≤ f.b.num * (t : Int))

/-- The normal `(a1, a2)` is primitive and `b` is in lowest terms. -/
def Facet.Primitive (f : Facet) : Prop := Nat.gcd f.a1.natAbs f.a2.natAbs = 1 ∧ f.b.Reduced

instance (f : Facet) : Decidable f.Primitive := by unfold Facet.Primitive; infer_instance

/-- The boundary line `a1 x + a2 y = b` passes through the rational point `v`. -/
def Facet.Through (f : Facet) (v : RPt) : Prop :=
  (f.b.den : Int) * (f.a1 * v.x.num * v.y.den + f.a2 * v.y.num * v.x.den)
    = f.b.num * v.x.den * v.y.den

instance (f : Facet) (v : RPt) : Decidable (f.Through v) := by
  unfold Facet.Through; infer_instance

/-- Every listed facet is primitive and its line passes through two vertices of `P`. -/
def FacetsOf (P : Tri) (fs : List Facet) : Prop :=
  ∀ f ∈ fs, f.Primitive ∧ ((f.Through P.v0 ∧ f.Through P.v1) ∨ (f.Through P.v0 ∧ f.Through P.v2)
    ∨ (f.Through P.v1 ∧ f.Through P.v2))

instance (P : Tri) (fs : List Facet) : Decidable (FacetsOf P fs) := by
  unfold FacetsOf; infer_instance

/-- The least common multiple of the denominators of the right-hand sides. -/
def facetDenLcm (fs : List Facet) : Nat := fs.foldl (fun l f => Nat.lcm l f.b.den) 1

/-- The number of lattice points `(x, y)` with `0 ≤ x ≤ W t`, `0 ≤ y ≤ H t` that satisfy every
facet inequality of the dilate by `t`. -/
def hcount (fs : List Facet) (W H : Nat) (t : Nat) : Nat :=
  sumUpTo (fun y => countUpTo (fun x => fs.all (fun f => f.holds t x y)) (W * t + 1)) (H * t + 1)

/-- The facet list `fs` and the box `[0, W t] × [0, H t]` describe exactly the lattice points of
every dilate `t P`.  Then `hcount fs W H t = #(tP ∩ ℤ²)`, the Ehrhart function of `P`. -/
def Describes (P : Tri) (fs : List Facet) (W H : Nat) : Prop :=
  ∀ (t : Nat) (x y : Int), P.MemScaled t x y ↔
    (0 ≤ x ∧ x ≤ ((W * t : Nat) : Int) ∧ 0 ≤ y ∧ y ≤ ((H * t : Nat) : Int) ∧
      (fs.all fun f => f.holds t x y) = true)

/-! ## Quasi-polynomials and periods -/

/-- Evaluation of an integer polynomial given by its coefficient list (constant term first). -/
def peval : List Int → Int → Int
  | [], _ => 0
  | c :: cs, x => c + x * peval cs x

/-- `L` is a quasi-polynomial with period `p`: there are polynomials `c_0, …, c_{p-1}` with
rational coefficients (written as integer polynomials over a common denominator `D > 0`)
such that `L t = c_{t mod p}(t)` for all `t ≥ 0`. -/
def HasPeriod (L : Nat → Nat) (p : Nat) : Prop :=
  0 < p ∧ ∃ D : Int, 0 < D ∧ ∃ c : Nat → List Int,
    ∀ t : Nat, D * (L t : Int) = peval (c (t % p)) (t : Int)

/-- `p` is the (minimal) period of `L`. -/
def IsMinPeriod (L : Nat → Nat) (p : Nat) : Prop :=
  HasPeriod L p ∧ ∀ q, 0 < q → q < p → ¬ HasPeriod L q

/-- The minimal period is unique, so "the period" is well defined. -/
theorem isMinPeriod_unique (L : Nat → Nat) (p q : Nat)
    (hp : IsMinPeriod L p) (hq : IsMinPeriod L q) : p = q := by
  have h1 : ¬ p < q := fun h => hq.2 p hp.1.1 h hp.1
  have h2 : ¬ q < p := fun h => hp.2 q hq.1.1 h hq.1
  omega

/-- A period-`1` quasi-polynomial has every positive period. -/
theorem hasPeriod_of_one (L : Nat → Nat) (p : Nat) (hp : 0 < p) (h : HasPeriod L 1) :
    HasPeriod L p := by
  obtain ⟨_, D, hD, c, hc⟩ := h
  exact ⟨hp, D, hD, fun _ => c 0, fun t => by rw [hc t, Nat.mod_one]⟩

/-- `a - b` divides `P(a) - P(b)` for an integer polynomial `P`. -/
theorem peval_sub_dvd (P : List Int) (a b : Int) : (a - b) ∣ peval P a - peval P b := by
  induction P with
  | nil => simp [peval]
  | cons c cs ih =>
    have e : peval (c :: cs) a - peval (c :: cs) b
        = a * (peval cs a - peval cs b) + (a - b) * peval cs b := by
      simp only [peval]
      rw [Int.mul_sub, Int.sub_mul]
      omega
    rw [e]
    exact Int.dvd_add (Int.dvd_trans ih (Int.dvd_mul_left a _)) (Int.dvd_mul_right _ _)

/-! ## The triangle `T = conv{(0,0), (1,1/2), (2,0)}` -/

def T : Tri := ⟨⟨⟨0, 1⟩, ⟨0, 1⟩⟩, ⟨⟨1, 1⟩, ⟨1, 2⟩⟩, ⟨⟨2, 1⟩, ⟨0, 1⟩⟩⟩

/-- Facets of `T`: `-y ≤ 0`, `-x + 2y ≤ 0`, `x + 2y ≤ 2`. -/
def Tfacets : List Facet := [⟨0, -1, ⟨0, 1⟩⟩, ⟨-1, 2, ⟨0, 1⟩⟩, ⟨1, 2, ⟨2, 1⟩⟩]

theorem T_reduced : T.Reduced := by decide

theorem T_denLcm : T.denLcm = 2 := by decide

theorem Tfacets_facetsOf : FacetsOf T Tfacets := by decide

theorem Tfacets_denLcm : facetDenLcm Tfacets = 1 := by decide

theorem Tfacets_holds (t : Nat) (x y : Int) :
    (Tfacets.all fun f => f.holds t x y) = true ↔ (0 ≤ y ∧ 2 * y ≤ x ∧ x + 2 * y ≤ 2 * t) := by
  simp [Tfacets, Facet.holds] <;> omega

theorem pos_mul_nonneg {M z : Int} (hM : 0 < M) (h : 0 ≤ M * z) : 0 ≤ z := by
  apply Classical.byContradiction
  intro hz
  have : M * z < 0 := Int.mul_neg_of_pos_of_neg hM (by omega)
  omega

/-- The facet list and the box `[0, 2t] × [0, t]` capture exactly the lattice points of `tT`. -/
theorem describes_T : Describes T Tfacets 2 1 := by
  intro t x y
  rw [Tfacets_holds]
  simp only [Tri.MemScaled, T, Tri.denProd, Tri.coords, RQ.scaleTo, List.foldl]
  simp only [Nat.reduceMul, Nat.reduceDiv, show ((2 : Nat) : Int) = 2 from rfl,
    show ((1 : Nat) : Int) = 1 from rfl, Int.reduceMul, Int.mul_zero, Int.zero_mul,
    Int.add_zero, Int.zero_add, Int.mul_one, Int.one_mul]
  constructor
  · rintro ⟨M, a, b, c, hM, ha, hb, hc, hs, hx, hy⟩
    -- `2 M x = 2 b + 4 c`, `2 M y = b`, `a + b + c = M t`
    have e1 : M * 2 * x = 2 * (M * x) := by rw [Int.mul_comm M 2, Int.mul_assoc]
    have e2 : M * 2 * y = 2 * (M * y) := by rw [Int.mul_comm M 2, Int.mul_assoc]
    rw [e1] at hx
    rw [e2] at hy
    have hy0 : 0 ≤ y := pos_mul_nonneg hM (by omega)
    have h1 : 0 ≤ x - 2 * y := pos_mul_nonneg hM (by rw [Int.mul_sub, Int.mul_left_comm]; omega)
    have h2 : 0 ≤ 2 * t - x - 2 * y := pos_mul_nonneg hM (by
      rw [Int.mul_sub, Int.mul_sub, Int.mul_left_comm, Int.mul_left_comm M 2 y]; omega)
    omega
  · intro h
    refine ⟨2, 2 * t - x - 2 * y, 4 * y, x - 2 * y, by omega, by omega, by omega, by omega,
      by omega, by omega, by omega⟩

/-- The Ehrhart function of `T`. -/
def LT (t : Nat) : Nat := hcount Tfacets 2 1 t

/-- Row `y` of `tT` contains `2t + 1 - 4y` lattice points (truncated at `0`). -/
theorem LT_row (t y : Nat) :
    countUpTo (fun x => Tfacets.all (fun f => f.holds t x y)) (2 * t + 1) = 2 * t + 1 - 4 * y := by
  rw [countUpTo_interval _ (2 * y) (2 * y) (2 * t) (fun x => by rw [Tfacets_holds]; omega)]
  omega

def ST (t : Nat) : Nat := sumUpTo (fun y => 2 * t + 1 - 4 * y) (t + 1)

theorem LT_eq_ST (t : Nat) : LT t = ST t := by
  unfold LT hcount ST
  rw [Nat.one_mul]
  exact sumUpTo_congr _ _ _ (fun y _ => LT_row t y)

theorem ST_rec (t : Nat) : ST (t + 2) = ST t + (2 * t + 5) := by
  unfold ST
  rw [sumUpTo_shift]
  rw [sumUpTo_congr (fun y => 2 * (t + 2) + 1 - 4 * (y + 1)) (fun y => 2 * t + 1 - 4 * y) (t + 2)
    (fun y _ => by show 2 * (t + 2) + 1 - 4 * (y + 1) = 2 * t + 1 - 4 * y; omega)]
  rw [sumUpTo]
  omega

theorem sq_step (t : Nat) : (t + 2) * (t + 2) = t * t + 4 * t + 4 := by
  simp only [Nat.add_mul, Nat.mul_add]
  omega

theorem ST_formula : ∀ t, 2 * ST t = t * t + 3 * t + 2
  | 0 => by decide
  | 1 => by decide
  | t + 2 => by
    rw [ST_rec, Nat.mul_add, ST_formula t, sq_step]
    omega

/-- **Period collapse.**  `#(tT ∩ ℤ²) = (t+1)(t+2)/2` for every `t ≥ 0`. -/
theorem LT_formula (t : Nat) : 2 * LT t = (t + 1) * (t + 2) := by
  rw [LT_eq_ST, ST_formula]
  simp only [Nat.add_mul, Nat.mul_add]
  omega

theorem LT_formula' (t : Nat) : LT t = (t + 1) * (t + 2) / 2 := by
  rw [← LT_formula]; omega

theorem LT_small : [LT 0, LT 1, LT 2, LT 3, LT 4, LT 5] = [1, 3, 6, 10, 15, 21] := by decide

/-- `L_T` is a polynomial: `2 L_T(t) = 2 + 3t + t²`. -/
theorem LT_period_one : HasPeriod LT 1 := by
  refine ⟨by decide, 2, by decide, fun _ => [2, 3, 1], fun t => ?_⟩
  have h' : ((2 * ST t : Nat) : Int) = ((t * t + 3 * t + 2 : Nat) : Int) := by rw [ST_formula t]
  simp only [Int.natCast_mul, Int.natCast_add] at h'
  rw [LT_eq_ST]
  simp only [peval, Int.mul_zero, Int.add_zero, Int.mul_one]
  rw [Int.mul_add]
  omega

theorem LT_minPeriod : IsMinPeriod LT 1 :=
  ⟨LT_period_one, fun q hq hq1 => absurd hq1 (by omega)⟩

/-- The lcm `2` is *a* period of `L_T` (as Ehrhart's theorem guarantees), but not the minimal one. -/
theorem LT_period_denLcm : HasPeriod LT T.denLcm := by
  rw [T_denLcm]; exact hasPeriod_of_one LT 2 (by decide) LT_period_one

theorem LT_not_minPeriod_two : ¬ IsMinPeriod LT 2 :=
  fun h => h.2 1 (by decide) (by decide) LT_period_one

/-! ## The control triangle `T₂ = conv{(0,0), (1,0), (0,1/2)}` -/

def T2 : Tri := ⟨⟨⟨0, 1⟩, ⟨0, 1⟩⟩, ⟨⟨1, 1⟩, ⟨0, 1⟩⟩, ⟨⟨0, 1⟩, ⟨1, 2⟩⟩⟩

/-- Facets of `T₂`: `-x ≤ 0`, `-y ≤ 0`, `x + 2y ≤ 1`. -/
def T2facets : List Facet := [⟨-1, 0, ⟨0, 1⟩⟩, ⟨0, -1, ⟨0, 1⟩⟩, ⟨1, 2, ⟨1, 1⟩⟩]

theorem T2_reduced : T2.Reduced := by decide

theorem T2_denLcm : T2.denLcm = 2 := by decide

theorem T2facets_facetsOf : FacetsOf T2 T2facets := by decide

theorem T2facets_denLcm : facetDenLcm T2facets = 1 := by decide

theorem T2facets_holds (t : Nat) (x y : Int) :
    (T2facets.all fun f => f.holds t x y) = true ↔ (0 ≤ x ∧ 0 ≤ y ∧ x + 2 * y ≤ t) := by
  simp [T2facets, Facet.holds] <;> omega

theorem describes_T2 : Describes T2 T2facets 1 1 := by
  intro t x y
  rw [T2facets_holds]
  simp only [Tri.MemScaled, T2, Tri.denProd, Tri.coords, RQ.scaleTo, List.foldl]
  simp only [Nat.reduceMul, Nat.reduceDiv, show ((2 : Nat) : Int) = 2 from rfl,
    show ((1 : Nat) : Int) = 1 from rfl, Int.reduceMul, Int.mul_zero, Int.zero_mul,
    Int.add_zero, Int.zero_add, Int.mul_one, Int.one_mul]
  constructor
  · rintro ⟨M, a, b, c, hM, ha, hb, hc, hs, hx, hy⟩
    -- `2 M x = 2 b`, `2 M y = c`, `a + b + c = M t`
    have e1 : M * 2 * x = 2 * (M * x) := by rw [Int.mul_comm M 2, Int.mul_assoc]
    have e2 : M * 2 * y = 2 * (M * y) := by rw [Int.mul_comm M 2, Int.mul_assoc]
    rw [e1] at hx
    rw [e2] at hy
    have hx0 : 0 ≤ x := pos_mul_nonneg hM (by omega)
    have hy0 : 0 ≤ y := pos_mul_nonneg hM (by omega)
    have h2 : 0 ≤ t - x - 2 * y := pos_mul_nonneg hM (by
      rw [Int.mul_sub, Int.mul_sub, Int.mul_left_comm M 2 y]; omega)
    omega
  · intro h
    refine ⟨1, t - x - 2 * y, x, 2 * y, by omega, by omega, by omega, by omega,
      by omega, by omega, by omega⟩

/-- The Ehrhart function of `T₂`. -/
def L2 (t : Nat) : Nat := hcount T2facets 1 1 t

theorem L2_row (t y : Nat) :
    countUpTo (fun x => T2facets.all (fun f => f.holds t x y)) (t + 1) = t + 1 - 2 * y := by
  rw [countUpTo_interval _ 0 (2 * y) t (fun x => by rw [T2facets_holds]; omega)]
  omega

def S2 (t : Nat) : Nat := sumUpTo (fun y => t + 1 - 2 * y) (t + 1)

theorem L2_eq_S2 (t : Nat) : L2 t = S2 t := by
  unfold L2 hcount S2
  rw [Nat.one_mul]
  exact sumUpTo_congr _ _ _ (fun y _ => L2_row t y)

theorem S2_rec (t : Nat) : S2 (t + 2) = S2 t + (t + 3) := by
  unfold S2
  rw [sumUpTo_shift]
  rw [sumUpTo_congr (fun y => t + 2 + 1 - 2 * (y + 1)) (fun y => t + 1 - 2 * y) (t + 2)
    (fun y _ => by show t + 2 + 1 - 2 * (y + 1) = t + 1 - 2 * y; omega)]
  rw [sumUpTo]
  omega

theorem S2_formula : ∀ t, 4 * S2 t + t % 2 = t * t + 4 * t + 4
  | 0 => by decide
  | 1 => by decide
  | t + 2 => by
    have ih := S2_formula t
    rw [S2_rec, sq_step]
    omega

/-- `4 L_{T₂}(t) = (t+2)²` for even `t` and `(t+1)(t+3)` for odd `t`. -/
theorem L2_formula (t : Nat) : 4 * L2 t + t % 2 = (t + 2) * (t + 2) := by
  rw [L2_eq_S2, S2_formula, sq_step]

theorem L2_small : [L2 0, L2 1, L2 2, L2 3, L2 4, L2 5] = [1, 2, 4, 6, 9, 12] := by decide

theorem L2_period_two : HasPeriod L2 2 := by
  refine ⟨by decide, 4, by decide, fun r => if r = 0 then [4, 4, 1] else [3, 4, 1], fun t => ?_⟩
  have h := L2_formula t
  rw [sq_step] at h
  have h' : ((4 * L2 t + t % 2 : Nat) : Int) = ((t * t + 4 * t + 4 : Nat) : Int) := by rw [h]
  simp only [Int.natCast_mul, Int.natCast_add] at h'
  have hm : t % 2 = 0 ∨ t % 2 = 1 := by omega
  rcases hm with hm | hm
  · rw [hm] at h'
    simp only [hm, if_true, peval, Int.mul_zero, Int.add_zero, Int.mul_one]
    rw [Int.mul_add]
    omega
  · rw [hm] at h'
    simp only [hm, Nat.one_ne_zero, if_false, peval, Int.mul_zero, Int.add_zero, Int.mul_one]
    rw [Int.mul_add]
    omega

/-- `L_{T₂}` is not a polynomial.  If `D · L_{T₂} = P` on `ℕ` for an integer polynomial `P`,
then `a = 2D + 1` divides `P(a) - P(0) = D (L(a) - 1)`, which forces `a ∣ D`. -/
theorem L2_not_period_one : ¬ HasPeriod L2 1 := by
  rintro ⟨_, D, hD, c, hc⟩
  obtain ⟨n, rfl⟩ : ∃ n : Nat, D = (n : Int) := ⟨D.toNat, by omega⟩
  have hn : 0 < n := by omega
  have h1 := hc (2 * n + 1)
  have h0 := hc 0
  rw [Nat.mod_one] at h1 h0
  have hdiv := peval_sub_dvd (c 0) ((2 * n + 1 : Nat) : Int) ((0 : Nat) : Int)
  rw [← h1, ← h0] at hdiv
  have hL0 : L2 0 = 1 := by decide
  rw [hL0] at hdiv
  have hf := L2_formula (2 * n + 1)
  have hodd : (2 * n + 1) % 2 = 1 := by omega
  rw [hodd] at hf
  -- integer forms
  generalize hL : L2 (2 * n + 1) = L at hf hdiv
  have hf' : ((4 * L + 1 : Nat) : Int) = (((2 * n + 1 + 2) * (2 * n + 1 + 2) : Nat) : Int) := by
    rw [hf]
  simp only [Int.natCast_mul, Int.natCast_add] at hf' hdiv
  generalize ha : ((2 : Nat) : Int) * (n : Int) + ((1 : Nat) : Int) = a at hf' hdiv
  have ha' : a = 2 * (n : Int) + 1 := by rw [← ha]; rfl
  obtain ⟨k, hk⟩ := hdiv
  -- `hk : n * L - n * 1 = (a - 0) * k`,  `hf' : 4 L + 1 = (a + 2) (a + 2)`.
  have e0 : (a - ((0 : Nat) : Int)) = a := by simp
  rw [e0] at hk
  have e1 : (a + ((2 : Nat) : Int)) * (a + ((2 : Nat) : Int)) = a * a + 4 * a + 4 := by
    simp only [Int.add_mul, Int.mul_add]
    have : ((2 : Nat) : Int) = 2 := rfl
    rw [this]
    omega
  rw [e1] at hf'
  -- `4 n (L - 1) = n a (a + 4) - n`
  have e2 : (n : Int) * (4 * (L : Int)) = (n : Int) * (a * a + 4 * a + 3) := by
    rw [show 4 * (L : Int) = a * a + 4 * a + 3 by
      have : ((4 : Nat) : Int) = 4 := rfl
      have : ((1 : Nat) : Int) = 1 := rfl
      omega]
  rw [Int.mul_add, Int.mul_add, Int.mul_left_comm, Int.mul_left_comm (n : Int) 4 a] at e2
  have e3 : (n : Int) * (a * a) = a * ((n : Int) * a) := by rw [Int.mul_left_comm]
  have e4 : (n : Int) * a = a * (n : Int) := Int.mul_comm _ _
  have hk' : (n : Int) * (L : Int) - (n : Int) = a * k := by
    rw [← hk]; simp
  -- hence `n = a * (n * a + 4 n) - 4 (a k)`, so `a ∣ n`
  have key : (n : Int) = a * ((n : Int) * a + 4 * (n : Int)) - 4 * (a * k) := by
    rw [Int.mul_add, Int.mul_left_comm a 4 (n : Int), ← e3, ← e4]
    omega
  have hdvd : a ∣ (n : Int) := by
    rw [key]
    exact Int.dvd_sub (Int.dvd_mul_right _ _) (Int.dvd_trans (Int.dvd_mul_right a k)
      (Int.dvd_mul_left _ _))
  have := Int.le_of_dvd (by omega) hdvd
  omega

theorem L2_minPeriod : IsMinPeriod L2 2 :=
  ⟨L2_period_two, fun q hq hq2 => by
    have : q = 1 := by omega
    subst this; exact L2_not_period_one⟩

/-! ## The conjecture -/

/-- The clause, vertex reading: for every rational triangle `P` (coordinates in lowest terms) and
every facet list and box describing its dilates, the minimal period of the Ehrhart function
`t ↦ #(tP ∩ ℤ²)` equals the lcm of the denominators of the vertex coordinates. -/
def VertexClaim : Prop :=
  ∀ (P : Tri) (fs : List Facet) (W H : Nat), P.Reduced → Describes P fs W H →
    IsMinPeriod (hcount fs W H) P.denLcm

/-- The clause, facet reading: the minimal period equals the lcm of the denominators of the
right-hand sides `b` of the facet inequalities `a·x ≤ b` (with primitive integer normals). -/
def FacetClaim : Prop :=
  ∀ (P : Tri) (fs : List Facet) (W H : Nat), P.Reduced → Describes P fs W H → FacetsOf P fs →
    IsMinPeriod (hcount fs W H) (facetDenLcm fs)

/-- The facet reading with "a period" instead of "the period". -/
def FacetClaimWeak : Prop :=
  ∀ (P : Tri) (fs : List Facet) (W H : Nat), P.Reduced → Describes P fs W H → FacetsOf P fs →
    HasPeriod (hcount fs W H) (facetDenLcm fs)

/-- **Main theorem.**  The clause fails for `T = conv{(0,0), (1,1/2), (2,0)}`:
its vertex denominators have lcm `2`, but its Ehrhart quasi-polynomial has period `1`. -/
theorem conjecture_00000007130_false : ¬ VertexClaim := by
  intro h
  have := h T Tfacets 2 1 T_reduced describes_T
  rw [T_denLcm] at this
  exact LT_not_minPeriod_two this

/-- The facet reading fails for `T₂ = conv{(0,0), (1,0), (0,1/2)}`: facet lcm `1`, period `2`. -/
theorem conjecture_00000007130_false_facet : ¬ FacetClaim := by
  intro h
  have := h T2 T2facets 1 1 T2_reduced describes_T2 T2facets_facetsOf
  rw [T2facets_denLcm] at this
  exact L2_not_period_one this.1

theorem conjecture_00000007130_false_facet_weak : ¬ FacetClaimWeak := by
  intro h
  have := h T2 T2facets 1 1 T2_reduced describes_T2 T2facets_facetsOf
  rw [T2facets_denLcm] at this
  exact L2_not_period_one this

/-- Non-vacuity: the hypotheses are satisfied, and the claimed equality does hold in other
instances (`T₂` in the vertex reading, `T` in the facet reading). -/
theorem sanity_T2_vertex : IsMinPeriod L2 T2.denLcm := by rw [T2_denLcm]; exact L2_minPeriod

theorem sanity_T_facet : IsMinPeriod LT (facetDenLcm Tfacets) := by
  rw [Tfacets_denLcm]; exact LT_minPeriod

end Ehrhart

#print axioms Ehrhart.isMinPeriod_unique
#print axioms Ehrhart.describes_T
#print axioms Ehrhart.LT_formula
#print axioms Ehrhart.LT_minPeriod
#print axioms Ehrhart.LT_period_denLcm
#print axioms Ehrhart.describes_T2
#print axioms Ehrhart.L2_formula
#print axioms Ehrhart.L2_minPeriod
#print axioms Ehrhart.conjecture_00000007130_false
#print axioms Ehrhart.conjecture_00000007130_false_facet
#print axioms Ehrhart.conjecture_00000007130_false_facet_weak
#print axioms Ehrhart.sanity_T2_vertex
#print axioms Ehrhart.sanity_T_facet
