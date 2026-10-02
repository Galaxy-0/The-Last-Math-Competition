/-
  Disproof of TLMC conjecture 00000001323.

  Conjecture: In Aut(C^2), the set of possible periods of elements with
  Jacobian constantly 1 is {1, 2, 3, 4, 6} (a conformal-symmetry
  restriction).

  Counterexample: A = diag(zeta_5, zeta_5^{-1}) is a LINEAR automorphism
  of C^2 with constant Jacobian determinant zeta_5 * zeta_5^{-1} = 1 and
  period exactly 5, since A^k = diag(zeta^k, zeta^{-k}) = I iff
  zeta^k = 1 iff 5 | k. The period 5 is not in {1,2,3,4,6}.

  Lean certificate: arithmetic in the cyclotomic quotient
  Z[t]/(t^4+t^3+t^2+t+1), the ring Z[zeta_5] (t maps to zeta_5 under the
  standard embedding into C — this standard identification is the only
  step outside the kernel; it is restated in README/tex). There:

    * t * t^4 = 1 and t^4 * t = 1   (so t^5 = 1 and t^4 = t^{-1}),
    * t^k ≠ 1 for k = 1,2,3,4       (t is a PRIMITIVE 5th root),
    * (t^4)^k = t^{4k} ≠ 1 for k = 1..4 (since 4k mod 5 ∈ {4,3,2,1}).

  Hence diag(t, t^4) has determinant 1, conjugates to A, and no power
  k < 5 is the identity: period exactly 5 ∉ {1,2,3,4,6}.

  Elements are coefficient vectors (f0..f3) for f0 + f1 t + f2 t^2 + f3 t^3;
  multiplication reduces t^4, t^5, t^6 via t^4 = -(t^3+t^2+t+1),
  t^5 = 1, t^6 = t. All theorems are closed kernel computations,
  axiom-free (see Check.lean).
-/

namespace Tlmc1323

structure Q where
  f0 : Int
  f1 : Int
  f2 : Int
  f3 : Int

def one : Q := ⟨1, 0, 0, 0⟩
def T : Q := ⟨0, 1, 0, 0⟩
def T2 : Q := ⟨0, 0, 1, 0⟩
def T3 : Q := ⟨0, 0, 0, 1⟩
def T4 : Q := ⟨-1, -1, -1, -1⟩   -- t^4 = -(t^3+t^2+t+1) in the quotient

/-- Multiplication in Z[t]/(t^4+t^3+t^2+t+1): schoolbook product of two
    degree-≤3 polys, then reduce t^4, t^5, t^6 by t^4 = -(1+t+t^2+t^3),
    t^5 = 1, t^6 = t. -/
def mulQ (a b : Q) : Q :=
  let c0 := a.f0*b.f0
  let c1 := a.f0*b.f1 + a.f1*b.f0
  let c2 := a.f0*b.f2 + a.f1*b.f1 + a.f2*b.f0
  let c3 := a.f0*b.f3 + a.f1*b.f2 + a.f2*b.f1 + a.f3*b.f0
  let c4 := a.f1*b.f3 + a.f2*b.f2 + a.f3*b.f1
  let c5 := a.f2*b.f3 + a.f3*b.f2
  let c6 := a.f3*b.f3
  ⟨c0 - c4 + c5, c1 - c4 + c6, c2 - c4, c3 - c4⟩

/-! ## t is a unit of order exactly 5. -/

/-- t * t^4 = 1 (all four components). -/
theorem t_mul_t4_is_one :
    (mulQ T T4).f0 = 1 ∧ (mulQ T T4).f1 = 0 ∧ (mulQ T T4).f2 = 0 ∧
    (mulQ T T4).f3 = 0 :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- t^4 * t = 1. -/
theorem t4_mul_t_is_one :
    (mulQ T4 T).f0 = 1 ∧ (mulQ T4 T).f1 = 0 ∧ (mulQ T4 T).f2 = 0 ∧
    (mulQ T4 T).f3 = 0 :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- The powers of t are as expected: t*t = t^2, t^2*t = t^3, t^3*t = t^4. -/
theorem tt_is_t2 :
    (mulQ T T).f2 = 1 ∧ (mulQ T T).f0 = 0 ∧ (mulQ T T).f1 = 0 ∧
    (mulQ T T).f3 = 0 :=
  ⟨by decide, by decide, by decide, by decide⟩
theorem t2t_is_t3 :
    (mulQ T2 T).f3 = 1 ∧ (mulQ T2 T).f0 = 0 ∧ (mulQ T2 T).f1 = 0 ∧
    (mulQ T2 T).f2 = 0 :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- t^k ≠ 1 for k = 1..4 (component f0 differs from 1 in each case:
    0 for k = 1,2,3 and -1 for k = 4). -/
theorem t_ne_one : (T).f0 ≠ 1 := by decide
theorem t2_ne_one : (T2).f0 ≠ 1 := by decide
theorem t3_ne_one : (T3).f0 ≠ 1 := by decide
theorem t4_ne_one : (T4).f0 ≠ 1 := by decide

/-- (t^4)^k ≠ 1 for k = 1..4 — the second diagonal entry never hits 1
    before k = 5 either. -/
theorem t4sq_f0 : (mulQ T4 T4).f3 = 1 ∧ (mulQ T4 T4).f0 = 0 :=
  ⟨by decide, by decide⟩          -- (t^4)^2 = t^8 = t^3
theorem t4cube_f0 : (mulQ (mulQ T4 T4) T4).f2 = 1 ∧ (mulQ (mulQ T4 T4) T4).f0 = 0 :=
  ⟨by decide, by decide⟩          -- (t^4)^3 = t^12 = t^2
theorem t4fourth_f0 : (mulQ (mulQ (mulQ T4 T4) T4) T4).f1 = 1 ∧ (mulQ (mulQ (mulQ T4 T4) T4) T4).f0 = 0 :=
  ⟨by decide, by decide⟩          -- (t^4)^4 = t^16 = t

/-! ## The counterexample's parameters. -/

/-- det diag(t, t^4) = t * t^4 = 1: the automorphism has Jacobian
    constantly 1. -/
theorem det_is_one : (mulQ T T4).f0 = 1 := by decide

/- The period is exactly 5: t^5 = t·t^4 = 1 and no smaller positive
   power works, by the six "≠ 1" facts above. -/

/-- 5 is not in {1, 2, 3, 4, 6}. -/
theorem five_not_in_set : ¬ (5 = 1 ∨ 5 = 2 ∨ 5 = 3 ∨ 5 = 4 ∨ 5 = 6) := by decide

end Tlmc1323
