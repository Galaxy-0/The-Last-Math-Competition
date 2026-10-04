/-!
# Conjecture 00000001007: ovoids of `Q(4,q)` in even characteristic

Conjecture (clause refuted here): *for `q` even, every ovoid of the parabolic
quadric `Q(4,q)` is an elliptic quadric*.

We refute it for `q = 8`.  Everything is built from scratch in core Lean:

* `F8` is the field `GF(8) = F₂[ω]/(ω³ + ω + 1)` (constructor `zi` is the
  element whose binary digits are the coordinates of `i` in the basis
  `1, ω, ω²`); the field axioms are checked by `decide`.
* `Q x = x₀x₃ + x₁x₂ + x₄²` is the standard parabolic quadric of `PG(4,8)`,
  `pol` its polar (bilinear) form.  `Q` is nondegenerate: the radical of
  `pol` is spanned by the nucleus `N = (0,0,0,0,1)` and `Q N = 1`.
* `IsOvoid O`: `O` is a list of `q² + 1 = 65` distinct points of `Q(4,8)`, no
  two of them collinear on the quadric (`pol p q ≠ 0`).  We also prove that
  such a set meets every totally singular line in at most one point.
* `tits` is the Suzuki–Tits ovoid (Tits 1962) for `q = 8`, `σ(x) = x⁴`
  (`σ² = ` Frobenius): the points
  `(1, x, y, xy + x^{σ+2} + y^σ, x³ + y²)` and `(0,0,0,1,0)`.
* An elliptic quadric of `Q(4,8)` is a hyperplane section `Q(4,8) ∩ H`; in the
  model obtained by projecting from the nucleus to `PG(3,8)` it is an elliptic
  quadric of `PG(3,8)`, i.e. lies on a quadric.  `tits` lies in no hyperplane
  of `PG(4,8)` and its projection lies on no quadric of `PG(3,8)`.

Main results: `conjecture_00000001007_false` and the reading-independent
`conjecture_00000001007_false_any_reading`.
-/

namespace Ovoid1007

/-! ## The field `GF(8)` -/

/-- Elements of `GF(8) = F₂[ω]/(ω³+ω+1)`; `zi` has binary digits = coordinates
of `i` in the basis `1, ω, ω²` (so `z2 = ω`, `z4 = ω²`, `z3 = ω + 1 = ω³`). -/
inductive F8
  | z0 | z1 | z2 | z3 | z4 | z5 | z6 | z7
deriving DecidableEq, Repr

open F8

/-- Addition (bitwise xor of coordinates). -/
def F8.add : F8 → F8 → F8
  | z0, z0 => z0
  | z0, z1 => z1
  | z0, z2 => z2
  | z0, z3 => z3
  | z0, z4 => z4
  | z0, z5 => z5
  | z0, z6 => z6
  | z0, z7 => z7
  | z1, z0 => z1
  | z1, z1 => z0
  | z1, z2 => z3
  | z1, z3 => z2
  | z1, z4 => z5
  | z1, z5 => z4
  | z1, z6 => z7
  | z1, z7 => z6
  | z2, z0 => z2
  | z2, z1 => z3
  | z2, z2 => z0
  | z2, z3 => z1
  | z2, z4 => z6
  | z2, z5 => z7
  | z2, z6 => z4
  | z2, z7 => z5
  | z3, z0 => z3
  | z3, z1 => z2
  | z3, z2 => z1
  | z3, z3 => z0
  | z3, z4 => z7
  | z3, z5 => z6
  | z3, z6 => z5
  | z3, z7 => z4
  | z4, z0 => z4
  | z4, z1 => z5
  | z4, z2 => z6
  | z4, z3 => z7
  | z4, z4 => z0
  | z4, z5 => z1
  | z4, z6 => z2
  | z4, z7 => z3
  | z5, z0 => z5
  | z5, z1 => z4
  | z5, z2 => z7
  | z5, z3 => z6
  | z5, z4 => z1
  | z5, z5 => z0
  | z5, z6 => z3
  | z5, z7 => z2
  | z6, z0 => z6
  | z6, z1 => z7
  | z6, z2 => z4
  | z6, z3 => z5
  | z6, z4 => z2
  | z6, z5 => z3
  | z6, z6 => z0
  | z6, z7 => z1
  | z7, z0 => z7
  | z7, z1 => z6
  | z7, z2 => z5
  | z7, z3 => z4
  | z7, z4 => z3
  | z7, z5 => z2
  | z7, z6 => z1
  | z7, z7 => z0

/-- Multiplication modulo `ω³ + ω + 1`. -/
def F8.mul : F8 → F8 → F8
  | z0, z0 => z0
  | z0, z1 => z0
  | z0, z2 => z0
  | z0, z3 => z0
  | z0, z4 => z0
  | z0, z5 => z0
  | z0, z6 => z0
  | z0, z7 => z0
  | z1, z0 => z0
  | z1, z1 => z1
  | z1, z2 => z2
  | z1, z3 => z3
  | z1, z4 => z4
  | z1, z5 => z5
  | z1, z6 => z6
  | z1, z7 => z7
  | z2, z0 => z0
  | z2, z1 => z2
  | z2, z2 => z4
  | z2, z3 => z6
  | z2, z4 => z3
  | z2, z5 => z1
  | z2, z6 => z7
  | z2, z7 => z5
  | z3, z0 => z0
  | z3, z1 => z3
  | z3, z2 => z6
  | z3, z3 => z5
  | z3, z4 => z7
  | z3, z5 => z4
  | z3, z6 => z1
  | z3, z7 => z2
  | z4, z0 => z0
  | z4, z1 => z4
  | z4, z2 => z3
  | z4, z3 => z7
  | z4, z4 => z6
  | z4, z5 => z2
  | z4, z6 => z5
  | z4, z7 => z1
  | z5, z0 => z0
  | z5, z1 => z5
  | z5, z2 => z1
  | z5, z3 => z4
  | z5, z4 => z2
  | z5, z5 => z7
  | z5, z6 => z3
  | z5, z7 => z6
  | z6, z0 => z0
  | z6, z1 => z6
  | z6, z2 => z7
  | z6, z3 => z1
  | z6, z4 => z5
  | z6, z5 => z3
  | z6, z6 => z2
  | z6, z7 => z4
  | z7, z0 => z0
  | z7, z1 => z7
  | z7, z2 => z5
  | z7, z3 => z2
  | z7, z4 => z1
  | z7, z5 => z6
  | z7, z6 => z4
  | z7, z7 => z3

instance : Add F8 := ⟨F8.add⟩
instance : Mul F8 := ⟨F8.mul⟩

/-- Numerals: `n` denotes `z(n mod 8)`. -/
def F8.lit (n : Nat) : F8 :=
  match n % 8 with
  | 0 => z0 | 1 => z1 | 2 => z2 | 3 => z3 | 4 => z4 | 5 => z5 | 6 => z6 | _ => z7

instance (n : Nat) : OfNat F8 n := ⟨F8.lit n⟩

instance (P : F8 → Prop) [DecidablePred P] : Decidable (∀ x, P x) :=
  decidable_of_iff (P z0 ∧ P z1 ∧ P z2 ∧ P z3 ∧ P z4 ∧ P z5 ∧ P z6 ∧ P z7)
    ⟨fun ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ x => by cases x <;> assumption,
     fun h => ⟨h _, h _, h _, h _, h _, h _, h _, h _⟩⟩

instance (P : F8 → Prop) [DecidablePred P] : Decidable (∃ x, P x) :=
  decidable_of_iff (P z0 ∨ P z1 ∨ P z2 ∨ P z3 ∨ P z4 ∨ P z5 ∨ P z6 ∨ P z7)
    ⟨fun h => by rcases h with h | h | h | h | h | h | h | h <;> exact ⟨_, h⟩,
     fun ⟨x, hx⟩ => by cases x <;> simp_all⟩

/-- The eight elements. -/
def elems : List F8 := [z0, z1, z2, z3, z4, z5, z6, z7]

theorem elems_complete : (∀ x : F8, x ∈ elems) ∧ elems.Nodup ∧ elems.length = 8 := by decide

/-! ### Field axioms (all checked exhaustively) -/

theorem add_comm : ∀ a b : F8, a + b = b + a := by decide
theorem add_assoc : ∀ a b c : F8, a + b + c = a + (b + c) := by decide
theorem add_left_comm : ∀ a b c : F8, a + (b + c) = b + (a + c) := by decide
theorem zero_add : ∀ a : F8, 0 + a = a := by decide
theorem add_zero : ∀ a : F8, a + 0 = a := by decide
theorem add_neg : ∀ a : F8, ∃ b : F8, a + b = 0 := by decide
theorem mul_comm : ∀ a b : F8, a * b = b * a := by decide
theorem mul_assoc : ∀ a b c : F8, a * b * c = a * (b * c) := by decide
theorem one_mul : ∀ a : F8, 1 * a = a := by decide
theorem mul_one : ∀ a : F8, a * 1 = a := by decide
theorem zero_mul : ∀ a : F8, 0 * a = 0 := by decide
theorem mul_zero : ∀ a : F8, a * 0 = 0 := by decide
theorem left_distrib : ∀ a b c : F8, a * (b + c) = a * b + a * c := by decide
theorem right_distrib : ∀ a b c : F8, (a + b) * c = a * c + b * c := by decide
theorem mul_inv : ∀ a : F8, a ≠ 0 → ∃ b : F8, a * b = 1 := by decide
theorem zero_ne_one : (0 : F8) ≠ 1 := by decide

/-- `GF(8)` has characteristic 2, so `q = 8` is even. -/
theorem char_two : ∀ a : F8, a + a = 0 := by decide

theorem add_cancel_left : ∀ a b : F8, a + (a + b) = b := by decide

/-- `ω = z2` generates the multiplicative group (order 7), so `F8` is `GF(8)`. -/
theorem omega_generates :
    [z2, z2*z2, z2*z2*z2, z2*z2*z2*z2, z2*z2*z2*z2*z2, z2*z2*z2*z2*z2*z2, z2*z2*z2*z2*z2*z2*z2]
      = [z2, z4, z3, z6, z7, z5, z1] := by decide

theorem sq_eq_zero : ∀ a : F8, a * a = 0 → a = 0 := by decide

/-- The automorphism `σ(x) = x⁴` of `GF(8)`. -/
def sigma (x : F8) : F8 := x * x * x * x

/-- `σ` is a field automorphism with `σ² = ` Frobenius (`x ↦ x²`), as required for
the Suzuki–Tits ovoid (`q = 2^{2e+1}`, `e = 1`, `σ = 2^{e+1}`). -/
theorem sigma_props :
    (∀ x y : F8, sigma (x + y) = sigma x + sigma y) ∧
    (∀ x y : F8, sigma (x * y) = sigma x * sigma y) ∧
    (∀ x : F8, sigma (sigma x) = x * x) ∧ sigma z2 ≠ z2 := by decide

/-! ## Vectors, the quadric `Q(4,8)` and its polar form -/

/-- Vectors of `GF(8)⁵`; a point of `PG(4,8)` is a nonzero vector up to scalars. -/
structure V5 where
  x0 : F8
  x1 : F8
  x2 : F8
  x3 : F8
  x4 : F8
deriving DecidableEq, Repr

def V5.zero : V5 := ⟨0, 0, 0, 0, 0⟩

def vadd (u v : V5) : V5 := ⟨u.x0 + v.x0, u.x1 + v.x1, u.x2 + v.x2, u.x3 + v.x3, u.x4 + v.x4⟩
def smul (t : F8) (v : V5) : V5 := ⟨t * v.x0, t * v.x1, t * v.x2, t * v.x3, t * v.x4⟩

/-- The parabolic quadratic form `Q(x) = x₀x₃ + x₁x₂ + x₄²` on `GF(8)⁵`. -/
def Q (v : V5) : F8 := v.x0 * v.x3 + v.x1 * v.x2 + v.x4 * v.x4

/-- Its polar form `pol(u,v) = Q(u+v) - Q(u) - Q(v)`. -/
def pol (u v : V5) : F8 := u.x0 * v.x3 + u.x3 * v.x0 + u.x1 * v.x2 + u.x2 * v.x1

/-- The nucleus of `Q(4,8)`. -/
def nucleus : V5 := ⟨0, 0, 0, 0, 1⟩

theorem mul_add_add (a b c d : F8) : (a + b) * (c + d) = a * c + b * d + (a * d + b * c) := by
  rw [right_distrib, left_distrib, left_distrib]
  simp only [add_assoc, add_comm, add_left_comm]

theorem sq_add (a b : F8) : (a + b) * (a + b) = a * a + b * b := by
  rw [mul_add_add, mul_comm b a, char_two, add_zero]

/-- Polarization identity: `pol` is the polar form of `Q`. -/
theorem Q_vadd (u v : V5) : Q (vadd u v) = Q u + Q v + pol u v := by
  cases u; cases v
  simp only [Q, pol, vadd, sq_add, mul_add_add]
  simp only [add_assoc, add_comm, add_left_comm, mul_comm, add_cancel_left]

theorem pol_comm (u v : V5) : pol u v = pol v u := by
  cases u; cases v
  simp only [pol]
  simp only [add_assoc, add_comm, add_left_comm, mul_comm]

/-- `pol` is alternating: `pol(v, t v) = 0`. -/
theorem pol_smul_self (t : F8) (v : V5) : pol v (smul t v) = 0 := by
  cases v with
  | mk a b c d e =>
    have h : ∀ x y : F8, x * (t * y) + y * (t * x) = 0 := by
      intro x y
      rw [mul_comm t y, ← mul_assoc, mul_comm t x, ← mul_assoc, mul_comm y x, char_two]
    simp only [pol, smul]
    rw [h a d, zero_add, h b c]

/-- `Q` is nondegenerate (parabolic): the radical of `pol` is spanned by the nucleus,
and `Q` does not vanish on the nucleus; hence no nonzero singular radical vector. -/
theorem Q_nondegenerate :
    (∀ v : V5, (∀ w : V5, pol v w = 0) → v.x0 = 0 ∧ v.x1 = 0 ∧ v.x2 = 0 ∧ v.x3 = 0) ∧
    (∀ w : V5, pol nucleus w = 0) ∧ Q nucleus = 1 ∧
    (∀ v : V5, (∀ w : V5, pol v w = 0) → Q v = 0 → v = V5.zero) := by
  have rad : ∀ v : V5, (∀ w : V5, pol v w = 0) → v.x0 = 0 ∧ v.x1 = 0 ∧ v.x2 = 0 ∧ v.x3 = 0 := by
    intro v h
    have h3 := h ⟨0, 0, 0, 1, 0⟩
    have h2 := h ⟨0, 0, 1, 0, 0⟩
    have h1 := h ⟨0, 1, 0, 0, 0⟩
    have h0 := h ⟨1, 0, 0, 0, 0⟩
    simp only [pol, mul_zero, mul_one, zero_add, add_zero] at h0 h1 h2 h3
    exact ⟨h3, h2, h1, h0⟩
  refine ⟨rad, ?_, by decide, ?_⟩
  · intro w; cases w; simp only [pol, nucleus, zero_mul, add_zero]
  · intro v h hq
    obtain ⟨e0, e1, e2, e3⟩ := rad v h
    cases v with
    | mk a b c d e =>
      simp only at e0 e1 e2 e3
      subst e0 e1 e2 e3
      simp only [Q, zero_mul, zero_add] at hq
      rw [sq_eq_zero e hq]; rfl

/-! ## Ovoids of `Q(4,8)` -/

/-- An ovoid of `Q(4,q)`, `q = 8`: `q² + 1 = 65` distinct points of the quadric
(nonzero representatives), no two of which are collinear on the quadric, i.e.
`pol p q ≠ 0` (two points of `Q` span a line of `Q` iff `pol` vanishes on them).
This is the standard finite characterization; see `IsOvoid.at_most_one` and the
report for the equivalence with "meets every line of `Q(4,8)` exactly once". -/
def IsOvoid (O : List V5) : Prop :=
  O.length = 65 ∧ O.Nodup ∧ (∀ p ∈ O, p ≠ V5.zero ∧ Q p = 0) ∧
    (∀ p ∈ O, ∀ q ∈ O, p ≠ q → pol p q ≠ 0)

instance (O : List V5) : Decidable (IsOvoid O) := by unfold IsOvoid; infer_instance

/-- Distinct members of an ovoid are distinct projective points. -/
theorem IsOvoid.proj_distinct {O : List V5} (hO : IsOvoid O) :
    ∀ p ∈ O, ∀ q ∈ O, p ≠ q → ∀ t : F8, q ≠ smul t p := by
  intro p hp q hq hne t heq
  apply hO.2.2.2 p hp q hq hne
  rw [heq, pol_smul_self]

/-- The points of the line spanned by `u, v`: `s u + t v`. -/
def lin (s t : F8) (u v : V5) : V5 := vadd (smul s u) (smul t v)

theorem lin_coord (s t s' t' a b : F8) :
    s * a + t * b + (s' * a + t' * b) = (s + s') * a + (t + t') * b := by
  rw [right_distrib, right_distrib]
  simp only [add_assoc, add_comm, add_left_comm]

theorem lin_add (s t s' t' : F8) (u v : V5) :
    vadd (lin s t u v) (lin s' t' u v) = lin (s + s') (t + t') u v := by
  cases u; cases v
  simp only [lin, vadd, smul, lin_coord]

/-- An ovoid meets every totally singular line of `Q(4,8)` in at most one point. -/
theorem IsOvoid.at_most_one {O : List V5} (hO : IsOvoid O) (u v : V5)
    (hline : ∀ s t : F8, Q (lin s t u v) = 0) (p q : V5) (hp : p ∈ O) (hq : q ∈ O)
    (hpl : ∃ s t : F8, p = lin s t u v) (hql : ∃ s t : F8, q = lin s t u v) : p = q := by
  apply Classical.byContradiction
  intro hne
  apply hO.2.2.2 p hp q hq hne
  obtain ⟨s, t, rfl⟩ := hpl
  obtain ⟨s', t', rfl⟩ := hql
  have h := hline (s + s') (t + t')
  rw [← lin_add, Q_vadd, hline s t, hline s' t', zero_add, zero_add] at h
  exact h

/-! ## Elliptic quadrics -/

/-- Linear functionals: `dot a p = Σ aᵢ pᵢ`. -/
def dotL : List F8 → List F8 → F8
  | a :: as, b :: bs => a * b + dotL as bs
  | _, _ => 0

def V5.toL (v : V5) : List F8 := [v.x0, v.x1, v.x2, v.x3, v.x4]

def dot (a p : V5) : F8 := dotL p.toL a.toL

/-- `O` lies in a hyperplane `{p : Σ aᵢ pᵢ = 0}` of `PG(4,8)`, `a ≠ 0`.
An elliptic quadric of `Q(4,8)` is a hyperplane section `Q(4,8) ∩ H`, so every
elliptic-quadric ovoid satisfies this (it is a necessary condition). -/
def InHyperplane (O : List V5) : Prop := ∃ a : V5, a ≠ V5.zero ∧ ∀ p ∈ O, dot a p = 0

/-- Quadratic forms on `GF(8)⁴` (coefficients of `xᵢxⱼ`, `i ≤ j`). -/
structure QForm where
  c00 : F8
  c01 : F8
  c02 : F8
  c03 : F8
  c11 : F8
  c12 : F8
  c13 : F8
  c22 : F8
  c23 : F8
  c33 : F8
deriving DecidableEq

def QForm.zero : QForm := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
def QForm.toL (c : QForm) : List F8 :=
  [c.c00, c.c01, c.c02, c.c03, c.c11, c.c12, c.c13, c.c22, c.c23, c.c33]

/-- Quadratic monomials of the projection `(p₀,p₁,p₂,p₃)` of `p` from the nucleus. -/
def mon (p : V5) : List F8 :=
  [p.x0 * p.x0, p.x0 * p.x1, p.x0 * p.x2, p.x0 * p.x3, p.x1 * p.x1, p.x1 * p.x2,
   p.x1 * p.x3, p.x2 * p.x2, p.x2 * p.x3, p.x3 * p.x3]

def QForm.eval (c : QForm) (p : V5) : F8 := dotL (mon p) c.toL

/-- The projection of `O` from the nucleus to `PG(3,8)` (`x₄ ↦` dropped) lies on a
quadric of `PG(3,8)`.  An elliptic quadric of `PG(3,8)` is the zero set of a
nonzero quadratic form, so every elliptic-quadric ovoid in this model satisfies this. -/
def OnQuadricPG3 (O : List V5) : Prop :=
  ∃ c : QForm, c ≠ QForm.zero ∧ ∀ p ∈ O, c.eval p = 0

/-! ## The Suzuki–Tits ovoid for `q = 8` -/

/-- `(1, x, y, xy + x^{σ+2} + y^σ, x³ + y²)`. -/
def titsPt (x y : F8) : V5 := ⟨1, x, y, x * y + sigma x * x * x + sigma y, x * x * x + y * y⟩

def tits : List V5 := (elems.flatMap fun x => elems.map fun y => titsPt x y) ++ [⟨0, 0, 0, 1, 0⟩]

/-- The last coordinate is the (unique) square root that puts the Tits point of
`PG(3,8)` on `Q(4,8)`: `(x³ + y²)² = x^{σ+2} + y^σ`. -/
theorem tits_lift : ∀ x y : F8, (x * x * x + y * y) * (x * x * x + y * y) = sigma x * x * x + sigma y := by
  decide

set_option maxRecDepth 100000 in
/-- The Suzuki–Tits set is an ovoid of `Q(4,8)`. -/
theorem tits_isOvoid : IsOvoid tits := by decide +kernel

/-! ### Linear-algebra certificate machinery -/

def addL : List F8 → List F8 → List F8
  | x :: xs, y :: ys => (x + y) :: addL xs ys
  | [], ys => ys
  | xs, [] => xs

def smulL (a : F8) (r : List F8) : List F8 := r.map (a * ·)

/-- `comb n E = Σⱼ nⱼ Eⱼ`. -/
def comb : List F8 → List (List F8) → List F8
  | a :: as, r :: rs => addL (smulL a r) (comb as rs)
  | _, _ => []

theorem dotL_nil (c : List F8) : dotL [] c = 0 := by cases c <;> rfl

theorem dotL_nil_right (c : List F8) : dotL c [] = 0 := by cases c <;> rfl

theorem dotL_addL : ∀ x y c : List F8, dotL (addL x y) c = dotL x c + dotL y c
  | [], ys, c => by cases ys <;> simp only [addL, dotL_nil, zero_add]
  | x :: xs, [], c => by simp only [addL, dotL_nil, add_zero]
  | x :: xs, y :: ys, [] => by simp only [addL, dotL_nil_right, add_zero]
  | x :: xs, y :: ys, d :: ds => by
    simp only [addL, dotL, dotL_addL xs ys ds, right_distrib]
    simp only [add_assoc, add_comm, add_left_comm]

theorem dotL_smulL (a : F8) : ∀ r c : List F8, dotL (smulL a r) c = a * dotL r c
  | [], c => by simp only [smulL, List.map, dotL_nil, mul_zero]
  | x :: xs, [] => by simp only [smulL, List.map, dotL_nil_right, mul_zero]
  | x :: xs, d :: ds => by
    have ih := dotL_smulL a xs ds
    simp only [smulL] at ih
    simp only [smulL, List.map, dotL, ih, left_distrib, mul_assoc]

/-- If `c` is orthogonal to every row of `E`, it is orthogonal to every combination. -/
theorem dotL_comb (c : List F8) :
    ∀ E : List (List F8), (∀ r ∈ E, dotL r c = 0) → ∀ n : List F8, dotL (comb n E) c = 0
  | [], _, n => by cases n <;> simp only [comb, dotL_nil]
  | r :: rs, h, [] => by simp only [comb, dotL_nil]
  | r :: rs, h, a :: as => by
    simp only [comb, dotL_addL, dotL_smulL]
    rw [h r (List.mem_cons_self), dotL_comb c rs (fun r' hr' => h r' (List.mem_cons_of_mem _ hr')) as,
      mul_zero, zero_add]

/-- If `N E = I` (`N` a list of rows) and `c ⊥` rows of `E`, then `c ⊥` rows of `I`. -/
theorem kill (c : List F8) (E : List (List F8)) (N I : List (List F8))
    (hE : ∀ r ∈ E, dotL r c = 0) (hNI : N.map (fun n => comb n E) = I) :
    ∀ u ∈ I, dotL u c = 0 := by
  intro u hu
  rw [← hNI] at hu
  obtain ⟨n, -, rfl⟩ := List.mem_map.1 hu
  exact dotL_comb c E hE n

/-! ### `tits` lies in no hyperplane -/

/-- Five points of `tits`. -/
def pts5 : List V5 := [titsPt 0 0, titsPt 0 1, titsPt 0 2, titsPt 0 4, titsPt 1 0]

/-- Rows of the inverse of the `5 × 5` matrix of `pts5`. -/
def N5 : List (List F8) :=
  [[1, 0, 0, 0, 0],
   [7, 0, 4, 2, 1],
   [7, 1, 4, 2, 0],
   [5, 1, 2, 6, 0],
   [3, 1, 6, 4, 0]]

def I5 : List (List F8) :=
  [[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]]

theorem pts5_sub : ∀ p ∈ pts5, p ∈ tits := by decide

theorem N5_cert : N5.map (fun n => comb n (pts5.map V5.toL)) = I5 := by decide

theorem tits_not_inHyperplane : ¬ InHyperplane tits := by
  rintro ⟨a, ha, h⟩
  have hE : ∀ r ∈ pts5.map V5.toL, dotL r a.toL = 0 := by
    intro r hr
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr
    exact h p (pts5_sub p hp)
  have k := kill a.toL _ N5 I5 hE N5_cert
  cases a with
  | mk a0 a1 a2 a3 a4 =>
    simp only [I5, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      dotL, V5.toL, one_mul, zero_mul, add_zero, zero_add] at k
    obtain ⟨k0, k1, k2, k3, k4⟩ := k
    subst k0 k1 k2 k3 k4
    exact ha rfl

/-! ### The projection of `tits` lies on no quadric of `PG(3,8)` -/

def pts10 : List V5 :=
  [titsPt 0 0, titsPt 0 1, titsPt 0 2, titsPt 0 3, titsPt 0 4,
   titsPt 1 0, titsPt 1 1, titsPt 1 2, titsPt 1 4, titsPt 2 0]

def N10 : List (List F8) :=
  [[1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [1, 5, 1, 7, 6, 1, 1, 0, 7, 3],
   [7, 3, 1, 3, 6, 3, 1, 6, 4, 0],
   [3, 7, 4, 6, 6, 0, 0, 0, 0, 0],
   [2, 5, 6, 6, 2, 6, 1, 4, 5, 3],
   [6, 0, 5, 1, 2, 2, 0, 6, 4, 0],
   [5, 1, 2, 0, 6, 5, 1, 2, 6, 0],
   [6, 4, 3, 5, 4, 0, 0, 0, 0, 0],
   [7, 7, 7, 7, 0, 0, 0, 0, 0, 0],
   [4, 6, 1, 7, 4, 3, 1, 6, 4, 0]]

def I10 : List (List F8) :=
  [[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

theorem pts10_sub : ∀ p ∈ pts10, p ∈ tits := by decide

set_option maxRecDepth 10000 in
theorem N10_cert : N10.map (fun n => comb n (pts10.map mon)) = I10 := by decide +kernel

theorem tits_not_onQuadric : ¬ OnQuadricPG3 tits := by
  rintro ⟨c, hc, h⟩
  have hE : ∀ r ∈ pts10.map mon, dotL r c.toL = 0 := by
    intro r hr
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr
    exact h p (pts10_sub p hp)
  have k := kill c.toL _ N10 I10 hE N10_cert
  cases c with
  | mk c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 =>
    simp only [I10, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      dotL, QForm.toL, one_mul, zero_mul, add_zero, zero_add] at k
    obtain ⟨k0, k1, k2, k3, k4, k5, k6, k7, k8, k9⟩ := k
    subst k0 k1 k2 k3 k4 k5 k6 k7 k8 k9
    exact hc rfl

/-! ## Non-vacuity: the elliptic quadric ovoid -/

/-- The elliptic quadric `Q(4,8) ∩ {x₄ = x₁ + x₂}`:
`x₀x₃ + x₁² + x₁x₂ + x₂² = 0` with `x² + x + 1` irreducible over `GF(8)`. -/
def ellPt (a b : F8) : V5 := ⟨1, a, b, a * a + a * b + b * b, a + b⟩

def ell : List V5 := (elems.flatMap fun a => elems.map fun b => ellPt a b) ++ [⟨0, 0, 0, 1, 0⟩]

theorem x2x1_irreducible : ∀ x : F8, x * x + x + 1 ≠ 0 := by decide

set_option maxRecDepth 100000 in
theorem ell_isOvoid : IsOvoid ell := by decide +kernel

theorem ell_inHyperplane : InHyperplane ell :=
  ⟨⟨0, 1, 1, 0, 1⟩, by decide, by decide⟩

theorem ell_onQuadric : OnQuadricPG3 ell :=
  ⟨⟨0, 0, 0, 1, 1, 1, 0, 1, 0, 0⟩, by decide, by decide⟩

/-- `tits` and `ell` are different ovoids (indeed not equal as point sets). -/
theorem tits_ne_ell : (titsPt 0 2 ∈ tits) ∧ ¬ (titsPt 0 2 ∈ ell) := by decide

/-! ## The conjecture -/

/-- The conjecture's clause for the even value `q = 8`, in its weakest form:
every ovoid of `Q(4,8)` lies in a hyperplane (as every elliptic quadric
`Q(4,8) ∩ H` does). -/
def Conjecture1007_q8 : Prop := ∀ O : List V5, IsOvoid O → InHyperplane O

/-- **Conjecture 00000001007 is false** (already for `q = 8`). -/
theorem conjecture_00000001007_false : ¬ Conjecture1007_q8 :=
  fun h => tits_not_inHyperplane (h tits tits_isOvoid)

/-- Reading-independent form: whatever precise meaning `IsElliptic` is given, as
long as an elliptic-quadric ovoid lies in a hyperplane of `PG(4,8)` (hyperplane
section model) or projects from the nucleus onto a set lying on a quadric of
`PG(3,8)` (projective-space model), the statement "every ovoid of `Q(4,8)` is
elliptic" is false; and the hypotheses are satisfiable (`ell`). -/
theorem conjecture_00000001007_false_any_reading (IsElliptic : List V5 → Prop)
    (hE : ∀ O, IsElliptic O → InHyperplane O ∨ OnQuadricPG3 O) :
    ¬ ∀ O : List V5, IsOvoid O → IsElliptic O := by
  intro h
  rcases hE tits (h tits tits_isOvoid) with h1 | h1
  · exact tits_not_inHyperplane h1
  · exact tits_not_onQuadric h1

/-- Non-vacuity of the reading-independent form: the natural reading
"`O` is a hyperplane section ovoid" satisfies the hypothesis, and the
elliptic quadric ovoid `ell` satisfies both models' conditions. -/
theorem nonvacuous :
    (∀ O, InHyperplane O → InHyperplane O ∨ OnQuadricPG3 O) ∧ IsOvoid ell ∧
      InHyperplane ell ∧ OnQuadricPG3 ell :=
  ⟨fun _ h => Or.inl h, ell_isOvoid, ell_inHyperplane, ell_onQuadric⟩

end Ovoid1007

#print axioms Ovoid1007.Q_nondegenerate
#print axioms Ovoid1007.IsOvoid.at_most_one
#print axioms Ovoid1007.tits_isOvoid
#print axioms Ovoid1007.tits_not_inHyperplane
#print axioms Ovoid1007.tits_not_onQuadric
#print axioms Ovoid1007.ell_isOvoid
#print axioms Ovoid1007.conjecture_00000001007_false
#print axioms Ovoid1007.conjecture_00000001007_false_any_reading
#print axioms Ovoid1007.nonvacuous
