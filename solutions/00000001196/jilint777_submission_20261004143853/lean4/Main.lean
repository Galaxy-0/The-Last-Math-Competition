/-!
# Conjecture 00000001196: maximal shifted Littlewood–Richardson coefficients

The conjecture defines `M(λ,μ) = max_ν N^ν_{λμ}`, the largest structure constant of the
Schur `Q`-functions in the product of the functions indexed by `λ` and `μ`, and claims
`M(λ,μ) ≤ min(2^{ℓ(λ)}, 2^{ℓ(μ)}, f^ν)` and `M((k),(k)) = 2^{k-1}`.

At `k = 3` the claimed value is `4`, but
* `Q_3 Q_3 = 2 Q_6 + 2 Q_51 + 2 Q_42`      (`QQ_in_Q`)
* `P_3 P_3 = P_6 + 2 P_51 + 2 P_42`        (`PP_in_P`, Stembridge's coefficients `f^ν_{λμ}`)
so `M((3),(3)) = 2` in both standard normalisations (`value_clause_false_P/Q`).
All eight normalisation readings "`X_(k) Y_(k)` expanded in the `Z`-basis",
`X, Y, Z ∈ {P, Q}`, are treated: in each of them, at `λ = μ = (3)`, either the value
clause `M = 4` or the consequence `M ≤ 2^{ℓ((3))} = 2` of the bound clause fails
(`conjecture_00000001196_false`).

Everything is computed from scratch in `ℤ[x₁,x₂,x₃]`:
* `q r` is the coefficient of `t^r` in `∏_{i ≤ 3} (1 + x_i t)/(1 - x_i t)`;
* `Qfun ν` is Schur's Pfaffian `Q_ν = Pf(Q_(ν_i,ν_j))` with
  `Q_(r,s) = q_r q_s + 2 Σ_{i=1}^{s} (-1)^i q_{r+i} q_{s-i}` (Macdonald III.8);
* `Pfun ν = 2^{-ℓ(ν)} Q_ν` (the division is checked to be exact);
* the four `Q_ν`, `ν ∈ {6, 51, 42, 321}`, are shown to be linearly independent
  (triangular at four monomials), so expansion coefficients are unique.

Polynomials are lists of (exponent triple, coefficient) pairs; `coeff p m` is the total
coefficient of the monomial `m` (the sum over all entries with exponent `m`), so two lists
denote the same polynomial iff their `coeff` functions agree.  "`d · T = Σ c_ν B_ν`" is
`Expands d T c B`, stated coefficientwise for every monomial.
-/

namespace SchurQ

/-- Exponent vector `(a,b,c)` of the monomial `x₁^a x₂^b x₃^c`. -/
abbrev Mono := Nat × Nat × Nat
/-- A polynomial in `ℤ[x₁,x₂,x₃]`. -/
abbrev Poly := List (Mono × Int)

/-! ## Polynomial arithmetic -/

/-- Lexicographic order on exponent triples (only used to keep lists sorted). -/
def monoLt (m n : Mono) : Bool :=
  Nat.blt m.1 n.1 || (m.1 == n.1 && (Nat.blt m.2.1 n.2.1 || (m.2.1 == n.2.1 && Nat.blt m.2.2 n.2.2)))

/-- Equality test for exponent triples (a `Bool`, for fast kernel evaluation). -/
def monoEq (m n : Mono) : Bool := m.1 == n.1 && m.2.1 == n.2.1 && m.2.2 == n.2.2

theorem monoEq_iff (m n : Mono) : monoEq m n = true ↔ m = n := by
  obtain ⟨a, b, c⟩ := m
  obtain ⟨a', b', c'⟩ := n
  simp [monoEq, and_assoc]

def madd (m n : Mono) : Mono := (m.1 + n.1, m.2.1 + n.2.1, m.2.2 + n.2.2)

/-- Add the term `c·x^m` to a polynomial (merging with an equal monomial). -/
def insertTerm (m : Mono) (c : Int) : Poly → Poly
  | [] => if c = 0 then [] else [(m, c)]
  | (m', c') :: p =>
    if monoEq m m' then (if c + c' = 0 then p else (m', c + c') :: p)
    else if monoLt m m' then (if c = 0 then (m', c') :: p else (m, c) :: (m', c') :: p)
    else (m', c') :: insertTerm m c p

def add (p q : Poly) : Poly := p.foldr (fun t acc => insertTerm t.1 t.2 acc) q

def scaleAux (a : Int) (p : Poly) : Poly := p.foldr (fun t acc => insertTerm t.1 (a * t.2) acc) []

def scale (a : Int) (p : Poly) : Poly := if a = 0 then [] else scaleAux a p

def mul (p q : Poly) : Poly :=
  p.foldr (fun t acc => q.foldr (fun s acc' => insertTerm (madd t.1 s.1) (t.2 * s.2) acc') acc) []

/-- Exact division of all coefficients by `n` (used only where it is exact). -/
def divBy (n : Int) (p : Poly) : Poly := p.foldr (fun t acc => insertTerm t.1 (t.2 / n) acc) []

/-- Coefficient of `x^m` in `p`. -/
def coeff : Poly → Mono → Int
  | [], _ => 0
  | (m', c) :: p, m => (if m' = m then c else 0) + coeff p m

theorem coeff_insertTerm (m : Mono) (c : Int) (p : Poly) (x : Mono) :
    coeff (insertTerm m c p) x = (if m = x then c else 0) + coeff p x := by
  induction p with
  | nil =>
    by_cases hc : c = 0
    · subst hc; simp [insertTerm, coeff]
    · simp [insertTerm, coeff, hc]
  | cons t p ih =>
    obtain ⟨m', c'⟩ := t
    by_cases h1 : monoEq m m' = true
    · have h1' := (monoEq_iff m m').1 h1
      subst h1'
      simp only [insertTerm, h1, if_true]
      by_cases h2 : c + c' = 0
      · by_cases hx : m = x
        · simp [insertTerm, coeff, h2, hx]; omega
        · simp [insertTerm, coeff, h2, hx]
      · by_cases hx : m = x
        · simp [insertTerm, coeff, h2, hx]; omega
        · simp [insertTerm, coeff, h2, hx]
    · by_cases h3 : monoLt m m' = true
      · by_cases hc : c = 0
        · subst hc; simp [insertTerm, coeff, h1, h3]
        · simp only [insertTerm, h1, h3, hc, if_false, if_true, coeff, Bool.false_eq_true]
      · simp only [insertTerm, h1, h3, if_false, coeff, ih, Bool.false_eq_true]
        omega

theorem coeff_add (p q : Poly) (x : Mono) : coeff (add p q) x = coeff p x + coeff q x := by
  induction p with
  | nil => simp [add, coeff]
  | cons t p ih =>
    simp only [add, List.foldr] at ih ⊢
    rw [coeff_insertTerm, ih]
    simp only [coeff]
    omega

theorem coeff_scaleAux (a : Int) (p : Poly) (x : Mono) : coeff (scaleAux a p) x = a * coeff p x := by
  induction p with
  | nil => simp [scaleAux, coeff]
  | cons t p ih =>
    simp only [scaleAux, List.foldr] at ih ⊢
    rw [coeff_insertTerm, ih]
    simp only [coeff]
    by_cases h : t.1 = x <;> simp [h, Int.mul_add]

theorem coeff_scale (a : Int) (p : Poly) (x : Mono) : coeff (scale a p) x = a * coeff p x := by
  by_cases ha : a = 0
  · subst ha; simp [scale, coeff]
  · simp [scale, ha, coeff_scaleAux]

/-! ## The functions `q_r` and the Schur `Q`- and `P`-functions in three variables -/

/-- `(1 + x t)/(1 - x t) = 1 + Σ_{s ≥ 1} 2 x^s t^s`: the coefficient of `x^s t^s`. -/
def w (s : Nat) : Int := if s = 0 then 1 else 2

/-- `q_r(x₁,x₂,x₃)`: the coefficient of `t^r` in `∏_{i=1}^{3} (1 + x_i t)/(1 - x_i t)`,
i.e. the sum over `a + b + c = r` of `w a * w b * w c * x₁^a x₂^b x₃^c`. -/
def q (r : Nat) : Poly :=
  (List.range (r + 1)).foldr (fun a acc =>
    (List.range (r + 1 - a)).foldr (fun b acc' =>
      insertTerm (a, b, r - a - b) (w a * w b * w (r - a - b)) acc') acc) []

/-- `Q_(r,s) = q_r q_s + 2 Σ_{i=1}^{s} (-1)^i q_{r+i} q_{s-i}` (Macdonald III (8.2')). -/
def Q2 (r s : Nat) : Poly :=
  (List.range s).foldr (fun j acc =>
    add (scale (2 * (-1) ^ (j + 1)) (mul (q (r + j + 1)) (q (s - (j + 1))))) acc) (mul (q r) (q s))

/-- Schur `Q`-function `Q_ν(x₁,x₂,x₃)` for a strict partition `ν` (as a decreasing list),
via Schur's Pfaffian `Q_ν = Pf (Q_(ν_i,ν_j))` (Macdonald III (8.11)); for odd length a
part `0` is appended, and `Q_(r,0) = q_r`.  In three variables `Q_ν = 0` for `ℓ(ν) > 3`. -/
def Qfun : List Nat → Poly
  | [] => [((0, 0, 0), 1)]
  | [a] => q a
  | [a, b] => Q2 a b
  | [a, b, c] => add (add (mul (Q2 a b) (q c)) (scale (-1) (mul (Q2 a c) (q b)))) (mul (q a) (Q2 b c))
  | _ => []

/-- Schur `P`-function `P_ν = 2^{-ℓ(ν)} Q_ν`. -/
def Pfun (ν : List Nat) : Poly := divBy (2 ^ ν.length) (Qfun ν)

/-- The two standard normalisations. -/
inductive Norm | P | Q
  deriving DecidableEq, Repr

def fn : Norm → List Nat → Poly
  | .P, ν => Pfun ν
  | .Q, ν => Qfun ν

/-! ## Strict partitions -/

def spAux : Nat → Nat → Nat → List (List Nat)
  | 0, n, _ => if n = 0 then [[]] else []
  | fuel + 1, n, mx =>
    if n = 0 then [[]] else
      ((List.range (min n mx)).reverse.map (· + 1)).flatMap
        (fun a => (spAux fuel (n - a) (a - 1)).map (a :: ·))

/-- Strict partitions of `n`, as decreasing lists. -/
def strictParts (n : Nat) : List (List Nat) := spAux n n n

theorem strictParts_six : strictParts 6 = [[6], [5, 1], [4, 2], [3, 2, 1]] := by decide

/-- The basis `{Z_ν : ν strict, |ν| = n}` (in three variables). -/
def basis (Z : Norm) (n : Nat) : List Poly := (strictParts n).map (fn Z)

/-! ## Expansions and the conjecture -/

def dot : List Int → List Int → Int
  | a :: as, b :: bs => a * b + dot as bs
  | _, _ => 0

/-- `d · T = Σ_i cs_i · B_i` as polynomials (equality of all coefficients).  With `d > 0`
this says that `T` has the rational expansion coefficients `cs_i / d` in the family `B`. -/
def Expands (d : Int) (T : Poly) (cs : List Int) (B : List Poly) : Prop :=
  ∀ m : Mono, d * coeff T m = dot cs (B.map (fun p => coeff p m))

def maxList : List Int → Int
  | [] => 0
  | [a] => a
  | a :: l => max a (maxList l)

/-- The product `X_(k) · Y_(k)`. -/
def prodK (X Y : Norm) (k : Nat) : Poly := mul (fn X [k]) (fn Y [k])

/-- Value clause of the conjecture under the reading `(X,Y,Z)`: the expansion of
`X_(k) Y_(k)` in the basis `{Z_ν}` has largest coefficient `M((k),(k)) = 2^(k-1)`. -/
def ValueAt (k : Nat) (X Y Z : Norm) : Prop :=
  ∃ (d : Int) (cs : List Int), 0 < d ∧ cs.length = (basis Z (2 * k)).length ∧
    Expands d (prodK X Y k) cs (basis Z (2 * k)) ∧ maxList cs = 2 ^ (k - 1) * d

/-- Consequence of the bound clause `M(λ,μ) ≤ min(2^{ℓ(λ)}, 2^{ℓ(μ)}, f^ν)` at `λ = μ = (k)`:
`M((k),(k)) ≤ 2^{ℓ((k))} = 2`. -/
def BoundAt (k : Nat) (X Y Z : Norm) : Prop :=
  ∀ (d : Int) (cs : List Int), 0 < d → cs.length = (basis Z (2 * k)).length →
    Expands d (prodK X Y k) cs (basis Z (2 * k)) → maxList cs ≤ 2 ^ ([k].length) * d

/-- The conjecture (its value clause and the consequence `M ≤ 2^{ℓ(λ)}` of its bound),
for all `k ≥ 1`, under the normalisation reading `(X, Y, Z)`.  Only the instance `k = 3`
is used; there three variables suffice (all strict partitions of `6` have at most three
parts and the four basis functions are proved linearly independent), so `ValueAt 3` and
`BoundAt 3` are faithful to the statement in the ring `Γ` of all variables. -/
def Conjecture (X Y Z : Norm) : Prop := ∀ k, 1 ≤ k → ValueAt k X Y Z ∧ BoundAt k X Y Z

/-! ## Sanity checks on the definitions -/

/-- The defining relation `Σ_{i+j=r} (-1)^i q_i q_j = 0` (i.e. `Q(t) Q(-t) = 1`) of the
ring `Γ`, checked for `1 ≤ r ≤ 6`.  (`verify.py` also checks `q_r = Σ_{a+b=r} e_a h_b`.) -/
theorem q_relation : ∀ r ∈ [1, 2, 3, 4, 5, 6],
    (List.range (r + 1)).foldr (fun i acc => add (scale ((-1) ^ i) (mul (q i) (q (r - i)))) acc) [] = [] := by
  decide +kernel

theorem q_one : q 1 = [((0, 0, 1), 2), ((0, 1, 0), 2), ((1, 0, 0), 2)] := by decide

/-- `P_ν` really is `2^{-ℓ(ν)} Q_ν`: the division is exact for all `ν` used. -/
theorem P_exact : ∀ ν ∈ [[3], [6], [5, 1], [4, 2], [3, 2, 1]],
    scale (2 ^ ν.length) (Pfun ν) = Qfun ν := by
  decide +kernel

/-- The basis elements are nonzero (`Q_321(x₁,x₂,x₃) = 8 x₁x₂x₃ (x₁+x₂)(x₁+x₃)(x₂+x₃)`). -/
theorem Q321_eq : Qfun [3, 2, 1] =
    mul [((1, 1, 1), 8)] (mul [((1, 0, 0), 1), ((0, 1, 0), 1)]
      (mul [((1, 0, 0), 1), ((0, 0, 1), 1)] [((0, 1, 0), 1), ((0, 0, 1), 1)])) := by
  decide +kernel

/-! ## Coefficient tables at four monomials -/

def m1 : Mono := (6, 0, 0)
def m2 : Mono := (5, 1, 0)
def m3 : Mono := (4, 2, 0)
def m4 : Mono := (3, 2, 1)

theorem evQ1 : (basis .Q 6).map (fun p => coeff p m1) = [2, 0, 0, 0] := by decide +kernel
theorem evQ2 : (basis .Q 6).map (fun p => coeff p m2) = [4, 4, 0, 0] := by decide +kernel
theorem evQ3 : (basis .Q 6).map (fun p => coeff p m3) = [4, 8, 4, 0] := by decide +kernel
theorem evQ4 : (basis .Q 6).map (fun p => coeff p m4) = [8, 24, 24, 8] := by decide +kernel
theorem evP1 : (basis .P 6).map (fun p => coeff p m1) = [1, 0, 0, 0] := by decide +kernel
theorem evP2 : (basis .P 6).map (fun p => coeff p m2) = [2, 1, 0, 0] := by decide +kernel
theorem evP3 : (basis .P 6).map (fun p => coeff p m3) = [2, 2, 1, 0] := by decide +kernel
theorem evP4 : (basis .P 6).map (fun p => coeff p m4) = [4, 6, 6, 1] := by decide +kernel

theorem basis_length (Z : Norm) : (basis Z 6).length = 4 := by
  cases Z <;> simp [basis, strictParts_six]

/-- Linear independence (triangularity): any expansion in the `Q`-basis is determined by
the coefficients of `T` at the four monomials `m1..m4`. -/
theorem solveQ {T : Poly} {d : Int} {cs : List Int} (hl : cs.length = 4)
    (h : Expands d T cs (basis .Q 6)) : ∃ a b e f, cs = [a, b, e, f] ∧
    d * coeff T m1 = 2 * a ∧ d * coeff T m2 = 4 * a + 4 * b ∧
    d * coeff T m3 = 4 * a + 8 * b + 4 * e ∧ d * coeff T m4 = 8 * a + 24 * b + 24 * e + 8 * f := by
  match cs, hl with
  | [a, b, e, f], _ =>
    refine ⟨a, b, e, f, rfl, ?_, ?_, ?_, ?_⟩
    · have h1 := h m1; rw [evQ1] at h1; simp only [dot] at h1; omega
    · have h1 := h m2; rw [evQ2] at h1; simp only [dot] at h1; omega
    · have h1 := h m3; rw [evQ3] at h1; simp only [dot] at h1; omega
    · have h1 := h m4; rw [evQ4] at h1; simp only [dot] at h1; omega

theorem solveP {T : Poly} {d : Int} {cs : List Int} (hl : cs.length = 4)
    (h : Expands d T cs (basis .P 6)) : ∃ a b e f, cs = [a, b, e, f] ∧
    d * coeff T m1 = a ∧ d * coeff T m2 = 2 * a + b ∧
    d * coeff T m3 = 2 * a + 2 * b + e ∧ d * coeff T m4 = 4 * a + 6 * b + 6 * e + f := by
  match cs, hl with
  | [a, b, e, f], _ =>
    refine ⟨a, b, e, f, rfl, ?_, ?_, ?_, ?_⟩
    · have h1 := h m1; rw [evP1] at h1; simp only [dot] at h1; omega
    · have h1 := h m2; rw [evP2] at h1; simp only [dot] at h1; omega
    · have h1 := h m3; rw [evP3] at h1; simp only [dot] at h1; omega
    · have h1 := h m4; rw [evP4] at h1; simp only [dot] at h1; omega

/-! ## The products at `k = 3` -/

def tvec (T : Poly) : List Int := [coeff T m1, coeff T m2, coeff T m3, coeff T m4]

theorem tv_QQ : tvec (prodK .Q .Q 3) = [4, 16, 32, 112] := by decide +kernel
theorem tv_PP : tvec (prodK .P .P 3) = [1, 4, 8, 28] := by decide +kernel
theorem tv_PQ : tvec (prodK .P .Q 3) = [2, 8, 16, 56] := by decide +kernel
theorem tv_QP : tvec (prodK .Q .P 3) = [2, 8, 16, 56] := by decide +kernel

/-- The linear combination `Σ cs_i B_i` as a polynomial. -/
def linComb : List Int → List Poly → Poly
  | c :: cs, b :: bs => add (scale c b) (linComb cs bs)
  | _, _ => []

theorem coeff_linComb (cs : List Int) (B : List Poly) (m : Mono) :
    coeff (linComb cs B) m = dot cs (B.map (fun p => coeff p m)) := by
  induction cs generalizing B with
  | nil => cases B <;> simp [linComb, dot, coeff]
  | cons c cs ih =>
    cases B with
    | nil => simp [linComb, dot, coeff]
    | cons b B => simp [linComb, dot, coeff_add, coeff_scale, ih]

theorem expands_of_eq {d : Int} {T : Poly} {cs : List Int} {B : List Poly}
    (h : scale d T = linComb cs B) : Expands d T cs B := by
  intro m
  rw [← coeff_scale, h, coeff_linComb]

/-- `Q_3 Q_3 = 2 Q_6 + 2 Q_51 + 2 Q_42` (as polynomials). -/
theorem QQ_in_Q : scale 1 (prodK .Q .Q 3) = linComb [2, 2, 2, 0] (basis .Q 6) := by decide +kernel
/-- `P_3 P_3 = P_6 + 2 P_51 + 2 P_42` (Stembridge's shifted LR coefficients). -/
theorem PP_in_P : scale 1 (prodK .P .P 3) = linComb [1, 2, 2, 0] (basis .P 6) := by decide +kernel
/-- `P_3 Q_3 = 2 P_6 + 4 P_51 + 4 P_42`. -/
theorem PQ_in_P : scale 1 (prodK .P .Q 3) = linComb [2, 4, 4, 0] (basis .P 6) := by decide +kernel
theorem QP_in_P : scale 1 (prodK .Q .P 3) = linComb [2, 4, 4, 0] (basis .P 6) := by decide +kernel
/-- `P_3 Q_3 = Q_6 + Q_51 + Q_42`. -/
theorem PQ_in_Q : scale 1 (prodK .P .Q 3) = linComb [1, 1, 1, 0] (basis .Q 6) := by decide +kernel
theorem QP_in_Q : scale 1 (prodK .Q .P 3) = linComb [1, 1, 1, 0] (basis .Q 6) := by decide +kernel
/-- `Q_3 Q_3 = 4 P_6 + 8 P_51 + 8 P_42`. -/
theorem QQ_in_P : scale 1 (prodK .Q .Q 3) = linComb [4, 8, 8, 0] (basis .P 6) := by decide +kernel
/-- `2 P_3 P_3 = Q_6 + Q_51 + Q_42`, i.e. `P_3 P_3 = ½ (Q_6 + Q_51 + Q_42)`. -/
theorem PP_in_Q : scale 2 (prodK .P .P 3) = linComb [1, 1, 1, 0] (basis .Q 6) := by decide +kernel

/-- The expansion vector `w` (with common denominator `δ`) of `X_3 Y_3` in the `Z`-basis:
coefficient of `Z_ν` is `w_ν / δ`. -/
def expVec : Norm → Norm → Norm → List Int × Int
  | .P, .P, .P => ([1, 2, 2, 0], 1)
  | .Q, .Q, .Q => ([2, 2, 2, 0], 1)
  | .P, .Q, .P => ([2, 4, 4, 0], 1)
  | .Q, .P, .P => ([2, 4, 4, 0], 1)
  | .P, .Q, .Q => ([1, 1, 1, 0], 1)
  | .Q, .P, .Q => ([1, 1, 1, 0], 1)
  | .Q, .Q, .P => ([4, 8, 8, 0], 1)
  | .P, .P, .Q => ([1, 1, 1, 0], 2)

/-- Non-vacuity: every reading has an expansion at `k = 3`. -/
theorem expansion_exists (X Y Z : Norm) :
    Expands (expVec X Y Z).2 (prodK X Y 3) (expVec X Y Z).1 (basis Z 6) := by
  cases X <;> cases Y <;> cases Z <;> apply expands_of_eq
  · exact PP_in_P
  · exact PP_in_Q
  · exact PQ_in_P
  · exact PQ_in_Q
  · exact QP_in_P
  · exact QP_in_Q
  · exact QQ_in_P
  · exact QQ_in_Q

def tvecVal : Norm → Norm → List Int
  | .Q, .Q => [4, 16, 32, 112]
  | .P, .P => [1, 4, 8, 28]
  | .P, .Q => [2, 8, 16, 56]
  | .Q, .P => [2, 8, 16, 56]

theorem tv (X Y : Norm) : tvec (prodK X Y 3) = tvecVal X Y := by
  cases X <;> cases Y
  · exact tv_PP
  · exact tv_PQ
  · exact tv_QP
  · exact tv_QQ

/-- Uniqueness: every expansion `d · X_3 Y_3 = Σ c_ν Z_ν` has `δ · c = d · w`, i.e. the
coefficients `c_ν / d` are exactly `w_ν / δ`. -/
theorem expansion_unique (X Y Z : Norm) (d : Int) (cs : List Int) (hl : cs.length = 4)
    (h : Expands d (prodK X Y 3) cs (basis Z 6)) :
    cs.map (fun c => (expVec X Y Z).2 * c) = (expVec X Y Z).1.map (fun x => d * x) := by
  have hv := tv X Y
  simp only [tvec] at hv
  cases Z
  · obtain ⟨a, b, e, f, rfl, h1, h2, h3, h4⟩ := solveP hl h
    cases X <;> cases Y <;>
    · simp only [tvecVal, List.cons.injEq] at hv
      obtain ⟨v1, v2, v3, v4, -⟩ := hv
      rw [v1] at h1; rw [v2] at h2; rw [v3] at h3; rw [v4] at h4
      simp only [expVec, List.map, List.cons.injEq, and_true]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
  · obtain ⟨a, b, e, f, rfl, h1, h2, h3, h4⟩ := solveQ hl h
    cases X <;> cases Y <;>
    · simp only [tvecVal, List.cons.injEq] at hv
      obtain ⟨v1, v2, v3, v4, -⟩ := hv
      rw [v1] at h1; rw [v2] at h2; rw [v3] at h3; rw [v4] at h4
      simp only [expVec, List.map, List.cons.injEq, and_true]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- `max_ν w_ν / δ`, i.e. the value of `M((3),(3))` under each reading (times `δ`). -/
def expMax : Norm → Norm → Norm → Int
  | .P, .P, .P => 2
  | .Q, .Q, .Q => 2
  | .P, .Q, .P => 4
  | .Q, .P, .P => 4
  | .P, .Q, .Q => 1
  | .Q, .P, .Q => 1
  | .Q, .Q, .P => 8
  | .P, .P, .Q => 1

theorem expMax_eq (X Y Z : Norm) : maxList (expVec X Y Z).1 = expMax X Y Z := by
  cases X <;> cases Y <;> cases Z <;> decide

/-- The expansion coefficients at `k = 3` are forced: for `d > 0`, the rational coefficients
`cs/d` are the entries of `expVec`, hence `M((3),(3)) = max(w)/δ`. -/
theorem max_coeff (X Y Z : Norm) (d : Int) (cs : List Int) (hd : 0 < d) (hl : cs.length = 4)
    (h : Expands d (prodK X Y 3) cs (basis Z 6)) :
    (expVec X Y Z).2 * maxList cs = d * expMax X Y Z := by
  have hu := expansion_unique X Y Z d cs hl h
  match cs, hl with
  | [a, b, e, f], _ =>
    cases X <;> cases Y <;> cases Z <;>
    · simp only [expVec, List.map, List.cons.injEq, and_true] at hu
      simp only [expVec, expMax, maxList]
      omega

theorem two_mul_three : 2 * 3 = 6 := rfl

/-- **Value clause fails at `k = 3`** for every reading except `P_3·Q_3` (or `Q_3·P_3`)
expanded in the `P`-basis.  In particular it fails for the two standard readings
(Stembridge's `P_λ P_μ = Σ f^ν_{λμ} P_ν`, and `Q_λ Q_μ = Σ c Q_ν`): there `M((3),(3)) = 2 ≠ 4`. -/
theorem value_fails (X Y Z : Norm)
    (hr : ¬ ((X = .P ∧ Y = .Q ∧ Z = .P) ∨ (X = .Q ∧ Y = .P ∧ Z = .P))) :
    ¬ ValueAt 3 X Y Z := by
  rintro ⟨d, cs, hd, hl, h, hmax⟩
  rw [two_mul_three] at hl h
  rw [basis_length] at hl
  have hm := max_coeff X Y Z d cs hd hl h
  cases X <;> cases Y <;> cases Z <;> simp at hr <;>
  · simp only [expVec, expMax] at hm
    rw [hmax] at hm
    omega

/-- **Bound clause fails at `k = 3`** for the two readings not covered by `value_fails`
(and also for `Q_3·Q_3` in the `P`-basis): `M((3),(3)) > 2 = 2^{ℓ((3))}`. -/
theorem bound_fails (X Y Z : Norm)
    (hr : (X = .P ∧ Y = .Q ∧ Z = .P) ∨ (X = .Q ∧ Y = .P ∧ Z = .P) ∨ (X = .Q ∧ Y = .Q ∧ Z = .P)) :
    ¬ BoundAt 3 X Y Z := by
  intro hb
  have hb' := hb (expVec X Y Z).2 (expVec X Y Z).1
  rw [two_mul_three, basis_length] at hb'
  rcases hr with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
  · have := hb' (by decide) (by decide) (expansion_exists _ _ _)
    revert this; decide

/-- The standard readings: the value clause `M((k),(k)) = 2^(k-1)` is false. -/
theorem value_clause_false_P : ¬ ∀ k, 1 ≤ k → ValueAt k .P .P .P :=
  fun h => value_fails .P .P .P (by simp) (h 3 (by decide))

theorem value_clause_false_Q : ¬ ∀ k, 1 ≤ k → ValueAt k .Q .Q .Q :=
  fun h => value_fails .Q .Q .Q (by simp) (h 3 (by decide))

/-- **Main theorem.**  Under every normalisation reading `(X, Y, Z)` (product `X_(k) Y_(k)`
expanded in the basis `{Z_ν}`), the conjecture fails at `λ = μ = (3)`: either
`M((3),(3)) ≠ 2^{3-1} = 4` or `M((3),(3)) > 2^{ℓ((3))} = 2`. -/
theorem conjecture_00000001196_false (X Y Z : Norm) : ¬ Conjecture X Y Z := by
  intro h
  obtain ⟨hv, hb⟩ := h 3 (by decide)
  by_cases hr : (X = .P ∧ Y = .Q ∧ Z = .P) ∨ (X = .Q ∧ Y = .P ∧ Z = .P)
  · exact bound_fails X Y Z (by rcases hr with hr | hr <;> simp [hr]) hb
  · exact value_fails X Y Z hr hv

/-- Non-vacuity of `BoundAt`: in the standard readings the bound clause does hold at `k = 3`
(`M((3),(3)) = 2 ≤ 2`), so it is a genuine condition, and `ValueAt` is satisfiable
(it holds for `P_3·Q_3` in the `P`-basis, where `M((3),(3)) = 4`). -/
theorem bound_holds_P : BoundAt 3 .P .P .P := by
  intro d cs hd hl h
  rw [two_mul_three] at hl h
  rw [basis_length] at hl
  have hm := max_coeff .P .P .P d cs hd hl h
  simp only [expVec, expMax, List.length] at hm ⊢
  omega

theorem value_holds_PQP : ValueAt 3 .P .Q .P :=
  ⟨1, [2, 4, 4, 0], by decide, by rw [two_mul_three, basis_length]; rfl,
    by rw [two_mul_three]; exact expansion_exists .P .Q .P, by decide⟩

end SchurQ

#print axioms SchurQ.coeff_insertTerm
#print axioms SchurQ.q_relation
#print axioms SchurQ.P_exact
#print axioms SchurQ.Q321_eq
#print axioms SchurQ.solveQ
#print axioms SchurQ.solveP
#print axioms SchurQ.QQ_in_Q
#print axioms SchurQ.PP_in_P
#print axioms SchurQ.expansion_exists
#print axioms SchurQ.expansion_unique
#print axioms SchurQ.max_coeff
#print axioms SchurQ.value_fails
#print axioms SchurQ.bound_fails
#print axioms SchurQ.value_clause_false_P
#print axioms SchurQ.value_clause_false_Q
#print axioms SchurQ.conjecture_00000001196_false
#print axioms SchurQ.bound_holds_P
#print axioms SchurQ.value_holds_PQP
