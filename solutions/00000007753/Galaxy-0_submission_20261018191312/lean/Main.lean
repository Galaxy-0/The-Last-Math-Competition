import Std
import Init.Data.Rat.Lemmas

namespace TLMC7753


/-- Coefficients are ordered from constant term upwards. -/
abbrev Poly := List Rat

def eval : Poly → Rat → Rat
  | [], _ => 0
  | a :: p, x => a + x * eval p x

def add : Poly → Poly → Poly
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a+b) :: add p q

def scale (a : Rat) (p : Poly) : Poly := p.map (a * ·)

def mul : Poly → Poly → Poly
  | [], _ => []
  | a :: p, q => add (scale a q) (0 :: mul p q)

/-- Remove trailing zero coefficients; this fixes the coefficient representation. -/
def trim : Poly → Poly
  | [] => []
  | a :: p => match trim p with
    | [] => if a = 0 then [] else [a]
    | b :: q => a :: b :: q

abbrev EqPoly (p q : Poly) : Prop := trim p = trim q

def IsUnit (p : Poly) : Prop := ∃ q, EqPoly (mul p q) [1]

def Reducible (p : Poly) : Prop :=
  ¬ EqPoly p [] ∧ ∃ a b, ¬ IsUnit a ∧ ¬ IsUnit b ∧ EqPoly (mul a b) p

theorem eval_add (p q : Poly) (x : Rat) : eval (add p q) x = eval p x + eval q x := by
  induction p generalizing q with
  | nil => simp [add, eval, Rat.zero_add]
  | cons a p ih =>
    cases q with
    | nil => simp [add, eval, Rat.add_zero]
    | cons b q =>
      simp only [add, eval, ih, Rat.mul_add]
      simp only [Rat.add_assoc, Rat.add_left_comm]

theorem eval_scale (a : Rat) (p : Poly) (x : Rat) :
    eval (scale a p) x = a * eval p x := by
  induction p with
  | nil => simp [scale, eval]
  | cons b p ih =>
    simp only [scale, List.map_cons, eval] at *
    rw [ih, Rat.mul_add]
    rw [← Rat.mul_assoc x a, Rat.mul_comm x a, Rat.mul_assoc]

theorem eval_mul (p q : Poly) (x : Rat) : eval (mul p q) x = eval p x * eval q x := by
  induction p with
  | nil => simp [mul, eval]
  | cons a p ih =>
    simp only [mul, eval_add, eval_scale, eval, Rat.zero_add, ih, Rat.add_mul,
      Rat.mul_assoc]

theorem eval_trim (p : Poly) (x : Rat) : eval (trim p) x = eval p x := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [trim]
    cases h : trim p with
    | nil =>
      have hp : eval p x = 0 := by rw [← ih, h]; rfl
      simp only [eval, hp, Rat.mul_zero, Rat.add_zero]
      split
      · rename_i ha; subst a; rfl
      · simp [eval, Rat.add_zero]
    | cons b q =>
      simp only [eval]
      rw [← ih, h]
      rfl

theorem eqPoly_eval {p q : Poly} (h : EqPoly p q) (x : Rat) : eval p x = eval q x := by
  rw [← eval_trim p x, ← eval_trim q x, h]

theorem root_not_unit {p : Poly} {r : Rat} (h : eval p r = 0) : ¬ IsUnit p := by
  intro ⟨q, hq⟩
  have e := eqPoly_eval hq r
  rw [eval_mul, h, Rat.zero_mul] at e
  have hz : (0 : Rat) ≠ 1 := by decide +kernel
  apply hz
  simpa only [eval, Rat.mul_zero, Rat.add_zero] using e

/-- For n=1, the sole divisor is 1 and mu(1)=1, so Phi_(1,c)=f_c-X. -/
def phiOne (c : Rat) : Poly := [c, -1, 1]

def quadraticMap (c : Rat) : Poly := [c, 0, 1]
def indeterminate : Poly := [0, 1]
def sub (p q : Poly) : Poly := add p (scale (-1) q)
/-- The n=1 instance of the divisor-product definition is exactly f_c(X)-X. -/
def firstDynatomic (c : Rat) : Poly := sub (quadraticMap c) indeterminate

theorem firstDynatomic_coeffs (c : Rat) : firstDynatomic c = phiOne c := by
  simp [firstDynatomic, quadraticMap, indeterminate, sub, add, scale, phiOne,
    Rat.add_zero, Rat.zero_add]


def leftA : Poly := [-2, 1]
def rightA : Poly := [1, 1]
def leftB : Poly := [-3, 1]
def rightB : Poly := [2, 1]

theorem factorA : EqPoly (mul leftA rightA) (phiOne (-2)) := by decide +kernel
theorem factorB : EqPoly (mul leftB rightB) (phiOne (-6)) := by decide +kernel

theorem reducibleA : Reducible (phiOne (-2)) := by
  refine ⟨by decide +kernel, leftA, rightA, ?_, ?_, factorA⟩
  · exact root_not_unit (r := 2) (by decide +kernel)
  · exact root_not_unit (r := -1) (by decide +kernel)

theorem reducibleB : Reducible (phiOne (-6)) := by
  refine ⟨by decide +kernel, leftB, rightB, ?_, ?_, factorB⟩
  · exact root_not_unit (r := 3) (by decide +kernel)
  · exact root_not_unit (r := -2) (by decide +kernel)

/-- Cardinality at most k, expressed by a list covering every member. -/
def HasAtMost (P : Rat → Prop) (k : Nat) : Prop :=
  ∃ xs : List Rat, xs.length ≤ k ∧ ∀ c, P c → c ∈ xs

/-- A set has cardinality at most one precisely when all its members coincide. -/
def AtMostOne (P : Rat → Prop) : Prop := ∀ a b, P a → P b → a = b

/-- The conjecture's exceptional-parameter bound at n=1. -/
def ClaimedBoundAtOne : Prop := AtMostOne (fun c => Reducible (phiOne c))

theorem bound_at_one : 2 ^ (1 - 1 : Nat) = 1 := by decide +kernel

theorem disproof : ¬ ClaimedBoundAtOne := by
  intro h
  have e : (-2 : Rat) = -6 := h (-2) (-6) reducibleA reducibleB
  exact (by decide +kernel : (-2 : Rat) ≠ -6) e

theorem hasAtMostOne_implies_atMostOne {P : Rat → Prop}
    (h : HasAtMost P 1) : AtMostOne P := by
  obtain ⟨xs, hlen, hcover⟩ := h
  intro a b ha hb
  have hma := hcover a ha
  have hmb := hcover b hb
  cases xs with
  | nil => simp at hma
  | cons c xs =>
    cases xs with
    | nil => simpa using (List.mem_singleton.mp hma).trans (List.mem_singleton.mp hmb).symm
    | cons d ys => simp at hlen

/-- Negation of the printed exceptional-parameter bound, at its allowed index n=1. -/
theorem exceptional_parameter_bound_false :
    ¬ HasAtMost (fun c => Reducible (firstDynatomic c)) (2 ^ (1 - 1 : Nat)) := by
  rw [bound_at_one]
  simp only [firstDynatomic_coeffs]
  intro h
  exact disproof (hasAtMostOne_implies_atMostOne h)

end TLMC7753
