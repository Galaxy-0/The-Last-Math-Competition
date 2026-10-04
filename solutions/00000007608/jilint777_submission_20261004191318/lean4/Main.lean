/-!
# Conjecture 00000007608 (reflections): the two-reflection decomposition is NOT unique

The conjecture: *"The composition of two reflections is a rotation and the decomposition is
unique; the exception of uniqueness is parallel reflections; and the exception of parallel
reflections is translation composition."*

We refute the uniqueness clause ("the decomposition of a rotation into two reflections is
unique, the only exception being parallel mirrors").  A rotation `ρ ≠ id` of the plane has
infinitely many decompositions `ρ = B ∘ A` into reflections in lines through the centre, and
none of them has parallel mirrors.  Already `R2 ∘ R1 = R4 ∘ R3 = rot90` with mirrors x-axis,
`y = x`, y-axis, `y = -x`.

Everything is built from scratch in core Lean 4 (no Mathlib):

* `M2`: integer 2×2 matrices; `QM`: rational 2×2 matrices `m / q` (`q > 0`), equality `QEq`
  (proved to be an equivalence relation).
* `IsRefl` (orthogonal, `det = -1`, involution), `IsRot` (orthogonal, `det = +1`), mirror =
  fixed line (`Fix`), parallel = same mirror (`SameMirror`; for mirrors through the origin
  "parallel" means "equal"), `Decomp ρ A B` = `A, B` reflections and `B·A = ρ`.
* Normal forms (`isRefl_iff`, `rot_form`), `refl_mul_refl` (clause 1, linear case, is true),
  `rot_mul_refl`, `decomp_of_refl`, `decomp_classification` (decompositions of `ρ` are exactly
  the pairs `(A, ρ·A)`).
* The Pythagorean family `Aref t` (`t ∈ ℕ`), the reflection in the line of slope `t`.
* `infinitely_many_decompositions`, `every_nontrivial_rotation_fails`,
  **`conjecture_00000007608_false : ¬ UniqueClause`** (weakest literal reading: unordered mirror
  pairs) and `conjecture_false_ordered` (ordered reading); sanity check `uniqueFor_id`.
* Concrete integer examples for 90° and 180°, the ℝ³ block embedding with plane mirrors, and
  affine reflections (parallel distinct mirrors give a fixed-point-free translation).
-/

namespace Refl

/-! ## 0. A small ring-normalisation tactic for `Int` (core Lean has no `ring`) -/

theorem two_mul' (a : Int) : 2 * a = a + a := by omega
theorem mul_two' (a : Int) : a * 2 = a + a := by omega

/-- Prove a polynomial identity over `Int`: expand, AC-normalise the monomials, then `omega`
treats every monomial as an atom. -/
macro "ring_z" : tactic => `(tactic| ((try simp only [two_mul', mul_two', Int.sub_eq_add_neg]) <;>
  (try simp only [Int.mul_add, Int.add_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm,
    Int.mul_one, Int.one_mul, Int.mul_zero, Int.zero_mul, Int.neg_mul, Int.mul_neg, Int.neg_add,
    Int.neg_neg]) <;> omega))

theorem sq_nonneg' (x : Int) : 0 ≤ x * x := by
  rcases Int.le_total 0 x with h | h
  · exact Int.mul_nonneg h h
  · exact Int.mul_nonneg_of_nonpos_of_nonpos h h

theorem sq_eq_zero' {x : Int} (h : x * x = 0) : x = 0 := by
  rcases Int.mul_eq_zero.mp h with h | h <;> exact h

theorem sum_sq_eq_zero {x y : Int} (h : x * x + y * y = 0) : x = 0 ∧ y = 0 := by
  have hx := sq_nonneg' x
  have hy := sq_nonneg' y
  exact ⟨sq_eq_zero' (by omega), sq_eq_zero' (by omega)⟩

/-- cancel a positive factor -/
theorem cancel_pos {k x y : Int} (hk : 0 < k) (h : k * x = k * y) : x = y :=
  Int.eq_of_mul_eq_mul_left (by omega) h

/-! ## 1. Integer 2×2 matrices -/

/-- The integer matrix `[[a, b], [c, d]]`. -/
structure M2 where
  a : Int
  b : Int
  c : Int
  d : Int
deriving DecidableEq, Repr

namespace M2
def mul (X Y : M2) : M2 :=
  ⟨X.a * Y.a + X.b * Y.c, X.a * Y.b + X.b * Y.d, X.c * Y.a + X.d * Y.c, X.c * Y.b + X.d * Y.d⟩
def tr (X : M2) : M2 := ⟨X.a, X.c, X.b, X.d⟩
def det (X : M2) : Int := X.a * X.d - X.b * X.c
/-- `k · I` -/
def scal (k : Int) : M2 := ⟨k, 0, 0, k⟩
/-- `k · X` -/
def smul (k : Int) (X : M2) : M2 := ⟨k * X.a, k * X.b, k * X.c, k * X.d⟩
/-- `X v` for a column vector `v ∈ ℤ²` -/
def app (X : M2) (v : Int × Int) : Int × Int := (X.a * v.1 + X.b * v.2, X.c * v.1 + X.d * v.2)

theorem app_mul (X Y : M2) (v : Int × Int) : (X.mul Y).app v = X.app (Y.app v) := by
  simp only [mul, app, Prod.mk.injEq]; constructor <;> ring_z

theorem mul_assoc (X Y Z : M2) : (X.mul Y).mul Z = X.mul (Y.mul Z) := by
  simp only [mul, mk.injEq]; refine ⟨?_, ?_, ?_, ?_⟩ <;> ring_z

theorem det_mul (X Y : M2) : (X.mul Y).det = X.det * Y.det := by
  simp only [mul, det]; ring_z
end M2

/-! ## 2. Rational 2×2 matrices

A rational matrix is stored as `m / q` with `m` an integer matrix and `q > 0` a common
denominator.  Every rational 2×2 matrix arises this way.  All predicates below are the
rational definitions with the denominators cleared; two pairs denote the same rational matrix
iff `QEq` holds. -/

/-- The rational matrix `m / q`. -/
structure QM where
  m : M2
  q : Int
  hq : 0 < q

namespace QM
/-- product of rational matrices: `(m/q)(n/r) = (mn)/(qr)` -/
def mul (X Y : QM) : QM := ⟨X.m.mul Y.m, X.q * Y.q, Int.mul_pos X.hq Y.hq⟩
end QM

/-- Equality of the rational matrices `X.m / X.q` and `Y.m / Y.q`. -/
def QEq (X Y : QM) : Prop := M2.smul Y.q X.m = M2.smul X.q Y.m

instance (X Y : QM) : Decidable (QEq X Y) := by unfold QEq; infer_instance

theorem QEq.refl (X : QM) : QEq X X := rfl

theorem QEq.symm {X Y : QM} (h : QEq X Y) : QEq Y X := Eq.symm h

theorem scal_trans {x y z p q r : Int} (hq : 0 < q) (h1 : q * x = p * y) (h2 : r * y = q * z) :
    r * x = p * z := by
  apply cancel_pos hq
  calc q * (r * x) = r * (q * x) := by ring_z
    _ = r * (p * y) := by rw [h1]
    _ = p * (r * y) := by ring_z
    _ = p * (q * z) := by rw [h2]
    _ = q * (p * z) := by ring_z

theorem QEq.trans {X Y Z : QM} (h1 : QEq X Y) (h2 : QEq Y Z) : QEq X Z := by
  simp only [QEq, M2.smul, M2.mk.injEq] at *
  obtain ⟨a1, b1, c1, d1⟩ := h1
  obtain ⟨a2, b2, c2, d2⟩ := h2
  exact ⟨scal_trans Y.hq a1 a2, scal_trans Y.hq b1 b2, scal_trans Y.hq c1 c2,
    scal_trans Y.hq d1 d2⟩

/-- The identity matrix. -/
def Id2 : QM := ⟨⟨1, 0, 0, 1⟩, 1, by decide⟩

/-! ## 3. Reflections, rotations, mirrors -/

/-- orthogonal: `X Xᵀ = I`, i.e. `m mᵀ = q² I` -/
def Orth (X : QM) : Prop := X.m.mul X.m.tr = M2.scal (X.q * X.q)

/-- A (linear) reflection: orthogonal, determinant `-1`, and an involution. -/
def IsRefl (X : QM) : Prop :=
  Orth X ∧ X.m.det = -(X.q * X.q) ∧ X.m.mul X.m = M2.scal (X.q * X.q)

/-- A (linear) rotation: orthogonal with determinant `+1`. -/
def IsRot (X : QM) : Prop := Orth X ∧ X.m.det = X.q * X.q

instance (X : QM) : Decidable (Orth X) := by unfold Orth; infer_instance
instance (X : QM) : Decidable (IsRefl X) := by unfold IsRefl; infer_instance
instance (X : QM) : Decidable (IsRot X) := by unfold IsRot; infer_instance

/-- `v` (a nonzero integer vector stands for the rational line through it) is fixed by `X`:
`X v = v`, i.e. `m v = q v`.  The mirror of a reflection `X` is `{v | Fix X v}`. -/
def Fix (X : QM) (v : Int × Int) : Prop := X.m.app v = (X.q * v.1, X.q * v.2)

instance (X : QM) (v : Int × Int) : Decidable (Fix X v) := by unfold Fix; infer_instance

/-- Two linear reflections have parallel mirrors.  Mirrors of linear reflections are lines
through the origin, so parallel = equal: the two fixed lines coincide.  (Integer vectors
suffice: a rational vector is fixed iff any integer multiple of it is.) -/
def SameMirror (X Y : QM) : Prop := ∀ v : Int × Int, Fix X v ↔ Fix Y v

/-- `ρ = B ∘ A`: a decomposition of `ρ` into two reflections (first `A`, then `B`). -/
def Decomp (ρ A B : QM) : Prop := IsRefl A ∧ IsRefl B ∧ QEq (B.mul A) ρ

instance (ρ A B : QM) : Decidable (Decomp ρ A B) := by unfold Decomp; infer_instance

/-! ## 4. Normal forms -/

/-- linear-combination helpers: `E = F` follows once `E - F` is a combination of quantities
known to vanish. -/
theorem lc1 {E F K S : Int} (hS : S = 0) (h : E - F = K * S) : E = F := by
  rw [hS, Int.mul_zero] at h; omega

theorem lc2 {E F K1 S1 K2 S2 : Int} (h1 : S1 = 0) (h2 : S2 = 0)
    (h : E - F = K1 * S1 + K2 * S2) : E = F := by
  rw [h1, h2, Int.mul_zero, Int.mul_zero] at h; omega

theorem lc3 {E F K1 S1 K2 S2 K3 S3 : Int} (h1 : S1 = 0) (h2 : S2 = 0) (h3 : S3 = 0)
    (h : E - F = K1 * S1 + K2 * S2 + K3 * S3) : E = F := by
  rw [h1, h2, h3, Int.mul_zero, Int.mul_zero, Int.mul_zero] at h; omega

/-- **Normal form of a reflection**: `X = [[a, b], [b, -a]] / q` with `a² + b² = q²`.
Only orthogonality and `det = -1` are used, so the involution property is automatic. -/
theorem refl_form {X : QM} (h : Orth X ∧ X.m.det = -(X.q * X.q)) :
    X.m.c = X.m.b ∧ X.m.d = -X.m.a ∧ X.m.a * X.m.a + X.m.b * X.m.b = X.q * X.q := by
  rcases X with ⟨⟨a, b, c, d⟩, q, hq⟩
  simp only [Orth, M2.mul, M2.tr, M2.scal, M2.det, M2.mk.injEq] at h ⊢
  obtain ⟨⟨h1, -, -, h3⟩, hd⟩ := h
  have : (b - c) * (b - c) + (a + d) * (a + d) = 0 := by
    have e : (b - c) * (b - c) + (a + d) * (a + d)
        = (a * a + b * b) + (c * c + d * d) + 2 * (a * d - b * c) := by ring_z
    rw [e, h1, h3, hd]; omega
  obtain ⟨e1, e2⟩ := sum_sq_eq_zero this
  exact ⟨by omega, by omega, h1⟩

/-- **Normal form of a rotation**: `X = [[x, y], [-y, x]] / p` with `x² + y² = p²`. -/
theorem rot_form {X : QM} (h : IsRot X) :
    X.m.c = -X.m.b ∧ X.m.d = X.m.a ∧ X.m.a * X.m.a + X.m.b * X.m.b = X.q * X.q := by
  rcases X with ⟨⟨a, b, c, d⟩, q, hq⟩
  simp only [IsRot, Orth, M2.mul, M2.tr, M2.scal, M2.det, M2.mk.injEq] at h ⊢
  obtain ⟨⟨h1, -, -, h3⟩, hd⟩ := h
  have : (b + c) * (b + c) + (a - d) * (a - d) = 0 := by
    have e : (b + c) * (b + c) + (a - d) * (a - d)
        = (a * a + b * b) + (c * c + d * d) - 2 * (a * d - b * c) := by ring_z
    rw [e, h1, h3, hd]; omega
  obtain ⟨e1, e2⟩ := sum_sq_eq_zero this
  exact ⟨by omega, by omega, h1⟩

/-- Conversely every `[[a, b], [b, -a]] / q` with `a² + b² = q²` is a reflection. -/
theorem refl_of_form {X : QM} (hc : X.m.c = X.m.b) (hd : X.m.d = -X.m.a)
    (h : X.m.a * X.m.a + X.m.b * X.m.b = X.q * X.q) : IsRefl X := by
  rcases X with ⟨⟨a, b, c, d⟩, q, hq⟩
  simp only at hc hd h
  subst c d
  simp only [IsRefl, Orth, M2.mul, M2.tr, M2.scal, M2.det, M2.mk.injEq]
  refine ⟨⟨h, by ring_z, by ring_z, ?_⟩, ?_, ⟨?_, by ring_z, by ring_z, ?_⟩⟩
  · (rw [← h]) <;> ring_z
  · (rw [← h]) <;> ring_z
  · (rw [← h]) <;> ring_z
  · (rw [← h]) <;> ring_z

/-- A matrix is a reflection iff it has the normal form (so "involution" is redundant). -/
theorem isRefl_iff (X : QM) : IsRefl X ↔
    X.m.c = X.m.b ∧ X.m.d = -X.m.a ∧ X.m.a * X.m.a + X.m.b * X.m.b = X.q * X.q :=
  ⟨fun h => refl_form ⟨h.1, h.2.1⟩, fun ⟨h1, h2, h3⟩ => refl_of_form h1 h2 h3⟩

/-- Every `[[x, y], [-y, x]] / p` with `x² + y² = p²` is a rotation. -/
theorem rot_of_form {X : QM} (hc : X.m.c = -X.m.b) (hd : X.m.d = X.m.a)
    (h : X.m.a * X.m.a + X.m.b * X.m.b = X.q * X.q) : IsRot X := by
  rcases X with ⟨⟨a, b, c, d⟩, q, hq⟩
  simp only at hc hd h
  subst c d
  simp only [IsRot, Orth, M2.mul, M2.tr, M2.scal, M2.det, M2.mk.injEq]
  refine ⟨⟨h, by ring_z, by ring_z, ?_⟩, ?_⟩
  · (rw [← h]) <;> ring_z
  · (rw [← h]) <;> ring_z

/-! ## 5. General theorems (every rational rotation) -/

/-- **Clause 1 (linear case) is true**: the product of two reflections is a rotation. -/
theorem refl_mul_refl {A B : QM} (hA : IsRefl A) (hB : IsRefl B) : IsRot (B.mul A) := by
  obtain ⟨hc, hd, h⟩ := refl_form ⟨hA.1, hA.2.1⟩
  obtain ⟨hc', hd', h'⟩ := refl_form ⟨hB.1, hB.2.1⟩
  rcases A with ⟨⟨a, b, c, d⟩, q, hq⟩
  rcases B with ⟨⟨e, f, g, k⟩, r, hr⟩
  simp only at hc hd h hc' hd' h'
  subst c d g k
  apply rot_of_form <;> simp only [QM.mul, M2.mul]
  · ring_z
  · ring_z
  · exact lc2 (K1 := a * a + b * b) (S1 := e * e + f * f - r * r) (K2 := r * r)
      (S2 := a * a + b * b - q * q) (by omega) (by omega) (by ring_z)

/-- `ρ · A` is a reflection whenever `ρ` is a rotation and `A` a reflection. -/
theorem rot_mul_refl {ρ A : QM} (hρ : IsRot ρ) (hA : IsRefl A) : IsRefl (ρ.mul A) := by
  obtain ⟨hc, hd, h⟩ := refl_form ⟨hA.1, hA.2.1⟩
  obtain ⟨hc', hd', h'⟩ := rot_form hρ
  rcases A with ⟨⟨a, b, c, d⟩, q, hq⟩
  rcases ρ with ⟨⟨x, y, u, w⟩, p, hp⟩
  simp only at hc hd h hc' hd' h'
  subst c d u w
  apply refl_of_form <;> simp only [QM.mul, M2.mul]
  · ring_z
  · ring_z
  · exact lc2 (K1 := a * a + b * b) (S1 := x * x + y * y - p * p) (K2 := p * p)
      (S2 := a * a + b * b - q * q) (by omega) (by omega) (by ring_z)

/-- **Existence for every rotation and every first mirror**: for each rotation `ρ` and each
reflection `A`, the pair `(A, ρ·A)` is a decomposition `ρ = (ρ·A) ∘ A`. -/
theorem decomp_of_refl {ρ A : QM} (hρ : IsRot ρ) (hA : IsRefl A) : Decomp ρ A (ρ.mul A) := by
  refine ⟨hA, rot_mul_refl hρ hA, ?_⟩
  obtain ⟨hc, hd, h⟩ := refl_form ⟨hA.1, hA.2.1⟩
  obtain ⟨hc', hd', _⟩ := rot_form hρ
  rcases A with ⟨⟨a, b, c, d⟩, q, hq⟩
  rcases ρ with ⟨⟨x, y, u, w⟩, p, hp⟩
  simp only at hc hd h hc' hd'
  subst c d u w
  have hS : a * a + b * b - q * q = 0 := by omega
  simp only [QEq, QM.mul, M2.mul, M2.smul, M2.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact lc1 (K := p * x) hS (by ring_z)
  · exact lc1 (K := p * y) hS (by ring_z)
  · exact lc1 (K := -(p * y)) hS (by ring_z)
  · exact lc1 (K := p * x) hS (by ring_z)

/-- **Classification**: every decomposition of a rotation `ρ` is of the form `(A, ρ·A)`;
i.e. the second reflection is determined by the first, and the first is arbitrary. -/
theorem decomp_classification {ρ A B : QM} (hρ : IsRot ρ) (hD : Decomp ρ A B) :
    QEq B (ρ.mul A) := by
  obtain ⟨hA, hB, hBA⟩ := hD
  obtain ⟨hc, hd, h⟩ := refl_form ⟨hA.1, hA.2.1⟩
  obtain ⟨hc2, hd2, _⟩ := refl_form ⟨hB.1, hB.2.1⟩
  obtain ⟨hc', hd', _⟩ := rot_form hρ
  rcases A with ⟨⟨a, b, c, d⟩, q, hq⟩
  rcases B with ⟨⟨e, f, g, k⟩, r, hr⟩
  rcases ρ with ⟨⟨x, y, u, w⟩, p, hp⟩
  simp only at hc hd h hc2 hd2 hc' hd'
  subst c d g k u w
  simp only [QEq, QM.mul, M2.mul, M2.smul, M2.mk.injEq] at hBA ⊢
  obtain ⟨h1, h2, -, -⟩ := hBA
  have hS : a * a + b * b - q * q = 0 := by omega
  have s1 : p * (e * a + f * b) - r * q * x = 0 := by omega
  have s2 : p * (e * b + f * -a) - r * q * y = 0 := by omega
  have ea : p * q * e = r * (x * a + y * b) := by
    apply cancel_pos hq
    exact lc3 (K1 := a) s1 (K2 := b) s2 (K3 := -(p * e)) hS (by ring_z)
  have eb : p * q * f = r * (x * b + y * -a) := by
    apply cancel_pos hq
    exact lc3 (K1 := b) s1 (K2 := -a) s2 (K3 := -(p * f)) hS (by ring_z)
  refine ⟨ea, eb, ?_, ?_⟩
  · have : r * (-y * a + x * b) = r * (x * b + y * -a) := by ring_z
    rw [this, ← eb]
  · have : r * (-y * b + x * -a) = - (r * (x * a + y * b)) := by ring_z
    rw [this, ← ea]; ring_z

/-! ## 6. Mirrors -/

theorem SameMirror.refl (X : QM) : SameMirror X X := fun _ => Iff.rfl
theorem SameMirror.symm {X Y : QM} (h : SameMirror X Y) : SameMirror Y X :=
  fun v => (h v).symm
theorem SameMirror.trans {X Y Z : QM} (h1 : SameMirror X Y) (h2 : SameMirror Y Z) :
    SameMirror X Z := fun v => (h1 v).trans (h2 v)

theorem fix_of_qeq {X Y : QM} (h : QEq X Y) {v : Int × Int} (hv : Fix X v) : Fix Y v := by
  rcases X with ⟨⟨a, b, c, d⟩, q, hq⟩
  rcases Y with ⟨⟨e, f, g, k⟩, r, hr⟩
  rcases v with ⟨v1, v2⟩
  simp only [QEq, Fix, M2.smul, M2.app, M2.mk.injEq, Prod.mk.injEq] at h hv ⊢
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨f1, f2⟩ := hv
  have s1 : r * a - q * e = 0 := by omega
  have s2 : r * b - q * f = 0 := by omega
  have s3 : r * c - q * g = 0 := by omega
  have s4 : r * d - q * k = 0 := by omega
  have t1 : a * v1 + b * v2 - q * v1 = 0 := by omega
  have t2 : c * v1 + d * v2 - q * v2 = 0 := by omega
  constructor
  · apply cancel_pos hq
    exact lc3 (K1 := -v1) s1 (K2 := -v2) s2 (K3 := r) t1 (by ring_z)
  · apply cancel_pos hq
    exact lc3 (K1 := -v1) s3 (K2 := -v2) s4 (K3 := r) t2 (by ring_z)

/-- Equal rational matrices have the same mirror. -/
theorem sameMirror_of_qeq {X Y : QM} (h : QEq X Y) : SameMirror X Y :=
  fun _ => ⟨fix_of_qeq h, fix_of_qeq (QEq.symm h)⟩

theorem not_sameMirror {X Y : QM} {v : Int × Int} (h1 : Fix X v) (h2 : ¬ Fix Y v) :
    ¬ SameMirror X Y := fun h => h2 ((h v).mp h1)

/-! ## 7. An infinite family of rational reflections (Pythagorean triples)

`Aref t = [[1 - t², 2t], [2t, t² - 1]] / (1 + t²)` is the reflection in the line spanned by
`(1, t)`, i.e. the line of slope `t`.  (`t = 0`: the x-axis; `t = 1`: the line `y = x`;
`t = 2`: `[[-3, 4], [4, 3]] / 5`.) -/

def Aref (t : Nat) : QM :=
  ⟨⟨1 - (t : Int) * t, 2 * t, 2 * t, (t : Int) * t - 1⟩, 1 + (t : Int) * t,
    by have := sq_nonneg' (t : Int); omega⟩

theorem Aref_refl (t : Nat) : IsRefl (Aref t) :=
  refl_of_form rfl (by simp only [Aref]; omega) (by simp only [Aref]; ring_z)

/-- The mirror of `Aref t` contains `(1, t)`. -/
theorem Aref_fix (t : Nat) : Fix (Aref t) (1, t) := by
  simp only [Fix, Aref, M2.app, Prod.mk.injEq]; constructor <;> ring_z

theorem Aref_fix_eq {s t : Nat} (h : Fix (Aref s) (1, t)) : s = t := by
  simp only [Fix, Aref, M2.app, Prod.mk.injEq] at h
  obtain ⟨-, h2⟩ := h
  have e : 2 * (s : Int) * 1 + ((s : Int) * s - 1) * t - (1 + (s : Int) * s) * t
      = 2 * (s : Int) - 2 * t := by ring_z
  omega

/-- Different parameters give different mirrors (hence different reflections). -/
theorem Aref_distinct {s t : Nat} (hst : s ≠ t) : ¬ SameMirror (Aref s) (Aref t) :=
  fun h => hst (Aref_fix_eq ((h (1, t)).mpr (Aref_fix t)))

theorem Aref_injective {s t : Nat} (hst : s ≠ t) : ¬ QEq (Aref s) (Aref t) :=
  fun h => Aref_distinct hst (sameMirror_of_qeq h)

/-- **Non-parallel**: if `ρ ≠ id`, the two mirrors of the decomposition `(Aref t, ρ·Aref t)`
are different lines, i.e. not parallel. -/
theorem nonparallel {ρ : QM} (hρ : IsRot ρ) (hne : ¬ QEq ρ Id2) (t : Nat) :
    ¬ SameMirror (Aref t) (ρ.mul (Aref t)) := by
  intro hs
  have hf := (hs (1, t)).mp (Aref_fix t)
  have hA : (Aref t).m.app (1, t) = ((Aref t).q * 1, (Aref t).q * t) := Aref_fix t
  simp only [Fix, QM.mul] at hf
  rw [M2.app_mul, hA] at hf
  have hQ := (Aref t).hq
  generalize (Aref t).q = Q at hf hQ
  obtain ⟨hc', hd', -⟩ := rot_form hρ
  rcases ρ with ⟨⟨x, y, u, w⟩, p, hp⟩
  simp only at hc' hd'
  subst u w
  simp only [M2.app, Prod.mk.injEq] at hf
  obtain ⟨f1, f2⟩ := hf
  have s1 : x * (Q * 1) + y * (Q * t) - p * Q * 1 = 0 := by omega
  have s2 : -y * (Q * 1) + x * (Q * t) - p * Q * t = 0 := by omega
  have e : (Q * y) * ((t : Int) * t + 1) = 0 :=
    lc2 (K1 := (t : Int)) s1 (K2 := -1) s2 (by ring_z)
  have ht := sq_nonneg' (t : Int)
  have hy : y = 0 := by
    rcases Int.mul_eq_zero.mp e with e | e
    · rcases Int.mul_eq_zero.mp e with e | e
      · omega
      · exact e
    · omega
  subst y
  have hx : x = p := cancel_pos hQ (lc1 (K := 1) s1 (by ring_z))
  subst x
  apply hne
  simp only [QEq, Id2, M2.smul, M2.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring_z

/-! ## 8. The claim and its refutation -/

/-- Two decompositions `(A, B)` and `(A', B')` use the same **unordered** pair of mirrors. -/
def SameMirrorPair (A B A' B' : QM) : Prop :=
  (SameMirror A A' ∧ SameMirror B B') ∨ (SameMirror A B' ∧ SameMirror B A')

/-- "The decomposition of `ρ` into two reflections is unique, the only exception being
parallel (here: equal) mirrors" -- in its weakest literal form: any two decompositions with
non-parallel mirrors have the same unordered pair of mirrors. -/
def UniqueFor (ρ : QM) : Prop :=
  ∀ A B A' B' : QM, Decomp ρ A B → Decomp ρ A' B' → ¬ SameMirror A B → ¬ SameMirror A' B' →
    SameMirrorPair A B A' B'

/-- The uniqueness clause of conjecture 00000007608, for all (rational) rotations. -/
def UniqueClause : Prop := ∀ ρ : QM, IsRot ρ → UniqueFor ρ

/-- A stronger (ordered, matrix-level) reading of the same clause. -/
def UniqueClauseOrdered : Prop :=
  ∀ ρ : QM, IsRot ρ → ∀ A B A' B' : QM, Decomp ρ A B → Decomp ρ A' B' →
    ¬ SameMirror A B → ¬ SameMirror A' B' → QEq A A' ∧ QEq B B'

theorem ordered_implies_unordered : UniqueClauseOrdered → UniqueClause :=
  fun h ρ hρ A B A' B' hD hD' hn hn' =>
    let ⟨e1, e2⟩ := h ρ hρ A B A' B' hD hD' hn hn'
    Or.inl ⟨sameMirror_of_qeq e1, sameMirror_of_qeq e2⟩

/-- The decompositions `D_t = (Aref t, ρ·Aref t)` of a nontrivial rotation: no three of them
share an unordered mirror pair. -/
theorem no_three_same {ρ : QM} {s t u : Nat} (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) :
    ¬ (SameMirrorPair (Aref s) (ρ.mul (Aref s)) (Aref t) (ρ.mul (Aref t)) ∧
       SameMirrorPair (Aref s) (ρ.mul (Aref s)) (Aref u) (ρ.mul (Aref u))) := by
  rintro ⟨⟨h, -⟩ | ⟨-, h1⟩, ⟨h', -⟩ | ⟨-, h2⟩⟩
  · exact Aref_distinct hst h
  · exact Aref_distinct hst h
  · exact Aref_distinct hsu h'
  · exact Aref_distinct htu (h1.symm.trans h2)

/-- **Main general theorem.** For EVERY rational rotation `ρ ≠ id` there are infinitely many
decompositions `ρ = B_t ∘ A_t` (`t ∈ ℕ`), with non-parallel mirrors, pairwise different first
mirrors (so pairwise different as ordered pairs), and no three with the same unordered
mirror pair. -/
theorem infinitely_many_decompositions {ρ : QM} (hρ : IsRot ρ) (hne : ¬ QEq ρ Id2) :
    (∀ t : Nat, Decomp ρ (Aref t) (ρ.mul (Aref t)) ∧ ¬ SameMirror (Aref t) (ρ.mul (Aref t))) ∧
    (∀ s t : Nat, s ≠ t → ¬ QEq (Aref s) (Aref t) ∧ ¬ SameMirror (Aref s) (Aref t)) ∧
    (∀ s t u : Nat, s ≠ t → s ≠ u → t ≠ u →
      ¬ (SameMirrorPair (Aref s) (ρ.mul (Aref s)) (Aref t) (ρ.mul (Aref t)) ∧
         SameMirrorPair (Aref s) (ρ.mul (Aref s)) (Aref u) (ρ.mul (Aref u)))) :=
  ⟨fun t => ⟨decomp_of_refl hρ (Aref_refl t), nonparallel hρ hne t⟩,
   fun _ _ h => ⟨Aref_injective h, Aref_distinct h⟩,
   fun _ _ _ h1 h2 h3 => no_three_same h1 h2 h3⟩

/-- **Uniqueness fails for every nontrivial rational rotation.** -/
theorem not_uniqueFor {ρ : QM} (hρ : IsRot ρ) (hne : ¬ QEq ρ Id2) : ¬ UniqueFor ρ := by
  intro hU
  have D := fun t => decomp_of_refl hρ (Aref_refl t)
  have N := fun t => nonparallel hρ hne t
  exact no_three_same (s := 0) (t := 1) (u := 2) (by decide) (by decide) (by decide)
    ⟨hU _ _ _ _ (D 0) (D 1) (N 0) (N 1), hU _ _ _ _ (D 0) (D 2) (N 0) (N 2)⟩

theorem Id2_isRot : IsRot Id2 := by decide

/-- Sanity check (the predicate is not trivially false): for the identity rotation, every
decomposition has equal ("parallel") mirrors, so `UniqueFor Id2` holds. -/
theorem uniqueFor_id : UniqueFor Id2 := by
  intro A B _ _ hD _ hn _
  exfalso; apply hn
  have h1 := decomp_classification Id2_isRot hD
  have h2 : QEq (Id2.mul A) A := by
    rcases A with ⟨⟨a, b, c, d⟩, q, hq⟩
    simp only [QEq, QM.mul, Id2, M2.mul, M2.smul, M2.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> ring_z
  exact (sameMirror_of_qeq (h1.trans h2)).symm

/-! ## 9. Concrete integer examples: the 90° and 180° rotations -/

/-- reflection in the x-axis, `diag(1, -1)` -/
def R1 : QM := ⟨⟨1, 0, 0, -1⟩, 1, by decide⟩
/-- reflection in the line `y = x`, `[[0, 1], [1, 0]]` -/
def R2 : QM := ⟨⟨0, 1, 1, 0⟩, 1, by decide⟩
/-- reflection in the y-axis, `diag(-1, 1)` -/
def R3 : QM := ⟨⟨-1, 0, 0, 1⟩, 1, by decide⟩
/-- reflection in the line `y = -x`, `[[0, -1], [-1, 0]]` -/
def R4 : QM := ⟨⟨0, -1, -1, 0⟩, 1, by decide⟩
/-- rotation by 90°, `[[0, -1], [1, 0]]` -/
def rot90 : QM := ⟨⟨0, -1, 1, 0⟩, 1, by decide⟩
/-- rotation by 180°, `-I` -/
def rot180 : QM := ⟨⟨-1, 0, 0, -1⟩, 1, by decide⟩

theorem rot90_isRot : IsRot rot90 := by decide
theorem rot90_ne_id : ¬ QEq rot90 Id2 := by decide
theorem rot180_isRot : IsRot rot180 := by decide
theorem rot180_ne_id : ¬ QEq rot180 Id2 := by decide

/-- The four mirrors x-axis, `y = x`, y-axis, `y = -x` are pairwise different lines. -/
theorem four_mirrors_distinct :
    ¬ SameMirror R1 R2 ∧ ¬ SameMirror R1 R3 ∧ ¬ SameMirror R1 R4 ∧
    ¬ SameMirror R2 R3 ∧ ¬ SameMirror R2 R4 ∧ ¬ SameMirror R3 R4 :=
  ⟨not_sameMirror (v := (1, 0)) (by decide) (by decide),
   not_sameMirror (v := (1, 0)) (by decide) (by decide),
   not_sameMirror (v := (1, 0)) (by decide) (by decide),
   not_sameMirror (v := (1, 1)) (by decide) (by decide),
   not_sameMirror (v := (1, 1)) (by decide) (by decide),
   not_sameMirror (v := (0, 1)) (by decide) (by decide)⟩

/-- **The 90° rotation**: `R2 ∘ R1 = R4 ∘ R3 = rot90`, four reflections, four different
mirrors, both pairs non-parallel. -/
theorem rot90_two_decompositions :
    IsRefl R1 ∧ IsRefl R2 ∧ IsRefl R3 ∧ IsRefl R4 ∧
    Decomp rot90 R1 R2 ∧ Decomp rot90 R3 R4 ∧ ¬ SameMirror R1 R2 ∧ ¬ SameMirror R3 R4 ∧
    ¬ SameMirrorPair R1 R2 R3 R4 := by
  obtain ⟨h12, h13, h14, h23, h24, h34⟩ := four_mirrors_distinct
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, h12, h34, ?_⟩
  rintro (⟨h, -⟩ | ⟨h, -⟩)
  · exact h13 h
  · exact h14 h

/-- **The 180° rotation**: `R3 ∘ R1 = -I` and `R4 ∘ R2 = -I` (and `R2 ∘ R4 = -I`). -/
theorem rot180_two_decompositions :
    Decomp rot180 R1 R3 ∧ Decomp rot180 R2 R4 ∧ Decomp rot180 R4 R2 ∧
    ¬ SameMirror R1 R3 ∧ ¬ SameMirror R2 R4 ∧ ¬ SameMirrorPair R1 R3 R2 R4 := by
  obtain ⟨h12, h13, h14, h23, h24, h34⟩ := four_mirrors_distinct
  refine ⟨by decide, by decide, by decide, h13, h24, ?_⟩
  rintro (⟨h, -⟩ | ⟨h, -⟩)
  · exact h12 h
  · exact h14 h

/-- A non-integral member of the family: `Aref 2 = [[-3, 4], [4, 3]] / 5`, and
`rot90 · Aref 2 = [[-4, -3], [-3, 4]] / 5`. -/
theorem Aref2_example :
    (Aref 2).m = ⟨-3, 4, 4, 3⟩ ∧ (Aref 2).q = 5 ∧ (rot90.mul (Aref 2)).m = ⟨-4, -3, -3, 4⟩ ∧
    Decomp rot90 (Aref 2) (rot90.mul (Aref 2)) := by decide

/-! ## 10. Higher dimension: hyperplane reflections of ℝ³ (block embedding) -/

/-- integer 3×3 matrix, rows `(a b c) (d e f) (g h i)` -/
structure M3 where
  a : Int
  b : Int
  c : Int
  d : Int
  e : Int
  f : Int
  g : Int
  h : Int
  i : Int
deriving DecidableEq, Repr

namespace M3
def mul (X Y : M3) : M3 :=
  ⟨X.a * Y.a + X.b * Y.d + X.c * Y.g, X.a * Y.b + X.b * Y.e + X.c * Y.h,
   X.a * Y.c + X.b * Y.f + X.c * Y.i,
   X.d * Y.a + X.e * Y.d + X.f * Y.g, X.d * Y.b + X.e * Y.e + X.f * Y.h,
   X.d * Y.c + X.e * Y.f + X.f * Y.i,
   X.g * Y.a + X.h * Y.d + X.i * Y.g, X.g * Y.b + X.h * Y.e + X.i * Y.h,
   X.g * Y.c + X.h * Y.f + X.i * Y.i⟩
def tr (X : M3) : M3 := ⟨X.a, X.d, X.g, X.b, X.e, X.h, X.c, X.f, X.i⟩
def det (X : M3) : Int :=
  X.a * (X.e * X.i - X.f * X.h) - X.b * (X.d * X.i - X.f * X.g) + X.c * (X.d * X.h - X.e * X.g)
def one : M3 := ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩
def app (X : M3) (v : Int × Int × Int) : Int × Int × Int :=
  (X.a * v.1 + X.b * v.2.1 + X.c * v.2.2, X.d * v.1 + X.e * v.2.1 + X.f * v.2.2,
   X.g * v.1 + X.h * v.2.1 + X.i * v.2.2)
/-- block embedding `diag(X, 1)` of an integer 2×2 matrix -/
def blk (X : M2) : M3 := ⟨X.a, X.b, 0, X.c, X.d, 0, 0, 0, 1⟩
end M3

/-- orthogonal reflection of ℤ³ ⊂ ℝ³ (integer entries): orthogonal, det `-1`, involution -/
def IsRefl3 (X : M3) : Prop := X.mul X.tr = M3.one ∧ X.det = -1 ∧ X.mul X = M3.one
def IsRot3 (X : M3) : Prop := X.mul X.tr = M3.one ∧ X.det = 1
instance (X : M3) : Decidable (IsRefl3 X) := by unfold IsRefl3; infer_instance
instance (X : M3) : Decidable (IsRot3 X) := by unfold IsRot3; infer_instance
def Fix3 (X : M3) (v : Int × Int × Int) : Prop := X.app v = v
instance (X : M3) (v : Int × Int × Int) : Decidable (Fix3 X v) := by unfold Fix3; infer_instance

/-- **ℝ³**: `diag(rot90, 1)` (the rotation by 90° about the z-axis) equals
`blk R2 ∘ blk R1 = blk R4 ∘ blk R3`; the four mirrors are planes (each fixes two independent
vectors, one of them the axis `e₃`) through the axis, pairwise different. -/
theorem r3_two_decompositions :
    IsRot3 (M3.blk rot90.m) ∧
    IsRefl3 (M3.blk R1.m) ∧ IsRefl3 (M3.blk R2.m) ∧ IsRefl3 (M3.blk R3.m) ∧
    IsRefl3 (M3.blk R4.m) ∧
    (M3.blk R2.m).mul (M3.blk R1.m) = M3.blk rot90.m ∧
    (M3.blk R4.m).mul (M3.blk R3.m) = M3.blk rot90.m ∧
    -- mirror planes: spanned by e₃ and (1,0,0) / (1,1,0) / (0,1,0) / (1,-1,0)
    Fix3 (M3.blk R1.m) (0, 0, 1) ∧ Fix3 (M3.blk R1.m) (1, 0, 0) ∧
    Fix3 (M3.blk R2.m) (0, 0, 1) ∧ Fix3 (M3.blk R2.m) (1, 1, 0) ∧
    Fix3 (M3.blk R3.m) (0, 0, 1) ∧ Fix3 (M3.blk R3.m) (0, 1, 0) ∧
    Fix3 (M3.blk R4.m) (0, 0, 1) ∧ Fix3 (M3.blk R4.m) (1, -1, 0) ∧
    -- pairwise different planes
    ¬ Fix3 (M3.blk R2.m) (1, 0, 0) ∧ ¬ Fix3 (M3.blk R3.m) (1, 0, 0) ∧
    ¬ Fix3 (M3.blk R4.m) (1, 0, 0) ∧ ¬ Fix3 (M3.blk R3.m) (1, 1, 0) ∧
    ¬ Fix3 (M3.blk R4.m) (1, 1, 0) ∧ ¬ Fix3 (M3.blk R4.m) (0, 1, 0) := by decide

/-! ## 11. Affine reflections: parallel mirrors give translations -/

/-- integer affine map `v ↦ m v + u` -/
structure Aff where
  m : M2
  u : Int × Int
deriving DecidableEq

namespace Aff
def app (F : Aff) (v : Int × Int) : Int × Int := ((F.m.app v).1 + F.u.1, (F.m.app v).2 + F.u.2)
/-- `G ∘ F` -/
def comp (G F : Aff) : Aff := ⟨G.m.mul F.m, ((G.m.app F.u).1 + G.u.1, (G.m.app F.u).2 + G.u.2)⟩
def id : Aff := ⟨⟨1, 0, 0, 1⟩, (0, 0)⟩
end Aff

/-- affine reflection: linear part is a reflection, and the map is an involution -/
def IsAffRefl (F : Aff) : Prop := IsRefl ⟨F.m, 1, by decide⟩ ∧ F.comp F = Aff.id
instance (F : Aff) : Decidable (IsAffRefl F) := by unfold IsAffRefl; infer_instance

/-- reflection in the line `x = 0` -/
def Sx0 : Aff := ⟨R3.m, (0, 0)⟩
/-- reflection in the line `x = 1` -/
def Sx1 : Aff := ⟨R3.m, (2, 0)⟩

/-- **Parallel distinct mirrors compose to a translation, which is not a rotation**: `x = 0`
and `x = 1` have the same direction but are different lines; `Sx1 ∘ Sx0` is the translation by
`(2, 0)` and has no fixed point at all. -/
theorem parallel_gives_translation :
    IsAffRefl Sx0 ∧ IsAffRefl Sx1 ∧ Sx0.m = Sx1.m ∧ Sx0.app (0, 0) = (0, 0) ∧
    Sx1.app (0, 0) ≠ (0, 0) ∧ Sx1.comp Sx0 = ⟨⟨1, 0, 0, 1⟩, (2, 0)⟩ ∧
    ∀ v : Int × Int, (Sx1.comp Sx0).app v ≠ v := by
  refine ⟨by decide, by decide, rfl, by decide, by decide, by decide, ?_⟩
  rintro ⟨v1, v2⟩ h
  simp only [Aff.app, Aff.comp, Sx1, Sx0, R3, M2.mul, M2.app, Prod.mk.injEq] at h
  omega

/-- reflections in the lines `y = 1`, `y = x`, `x = 1`, `x + y = 2` (all through `(1, 1)`) -/
def Sy1 : Aff := ⟨R1.m, (0, 2)⟩
def Sdiag : Aff := ⟨R2.m, (0, 0)⟩
def Santi : Aff := ⟨R4.m, (2, 2)⟩
/-- rotation by 90° about the point `c = (1, 1)` -/
def RotC : Aff := ⟨rot90.m, (2, 0)⟩

/-- **Affine reading**: the rotation by 90° about `(1, 1)` has (at least) two decompositions
into affine reflections with non-parallel mirrors, `Sdiag ∘ Sy1 = Santi ∘ Sx1`, and the four
mirrors are four different lines (their directions are the four different mirrors of
`four_mirrors_distinct`). -/
theorem affine_two_decompositions :
    RotC.app (1, 1) = (1, 1) ∧
    IsAffRefl Sy1 ∧ IsAffRefl Sdiag ∧ IsAffRefl Sx1 ∧ IsAffRefl Santi ∧
    Sdiag.comp Sy1 = RotC ∧ Santi.comp Sx1 = RotC ∧
    Sy1.app (0, 1) = (0, 1) ∧ Sdiag.app (0, 0) = (0, 0) ∧ Sx1.app (1, 0) = (1, 0) ∧
    Santi.app (0, 2) = (0, 2) := by decide

/-! ## 12. Main theorem -/

/-- **Conjecture 00000007608 is false**: the clause "the decomposition of a rotation into two
reflections is unique, the exception of uniqueness being parallel reflections" fails -- even
in its weakest literal form (unordered pairs of mirrors, mirrors compared as lines). -/
theorem conjecture_00000007608_false : ¬ UniqueClause :=
  fun h => not_uniqueFor rot90_isRot rot90_ne_id (h rot90 rot90_isRot)

/-- The same, directly from the explicit integer example `R2 ∘ R1 = R4 ∘ R3`. -/
theorem conjecture_false_rot90_explicit : ¬ UniqueClause := by
  intro h
  obtain ⟨-, -, -, -, d1, d2, n1, n2, hne⟩ := rot90_two_decompositions
  exact hne (h rot90 rot90_isRot R1 R2 R3 R4 d1 d2 n1 n2)

/-- The stronger ordered reading is false too. -/
theorem conjecture_false_ordered : ¬ UniqueClauseOrdered :=
  fun h => conjecture_00000007608_false (ordered_implies_unordered h)

/-- Uniqueness fails for EVERY rational rotation other than the identity. -/
theorem every_nontrivial_rotation_fails :
    ∀ ρ : QM, IsRot ρ → ¬ QEq ρ Id2 → ¬ UniqueFor ρ :=
  fun _ hρ hne => not_uniqueFor hρ hne

end Refl

#print axioms Refl.conjecture_00000007608_false
#print axioms Refl.conjecture_false_rot90_explicit
#print axioms Refl.conjecture_false_ordered
#print axioms Refl.every_nontrivial_rotation_fails
#print axioms Refl.infinitely_many_decompositions
#print axioms Refl.decomp_classification
#print axioms Refl.refl_mul_refl
#print axioms Refl.isRefl_iff
#print axioms Refl.uniqueFor_id
#print axioms Refl.rot90_two_decompositions
#print axioms Refl.rot180_two_decompositions
#print axioms Refl.Aref2_example
#print axioms Refl.r3_two_decompositions
#print axioms Refl.parallel_gives_translation
#print axioms Refl.affine_two_decompositions
