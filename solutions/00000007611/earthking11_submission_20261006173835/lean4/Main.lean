import Std

namespace Tlmc7611

/-- A real two-by-two matrix, stored by rows. -/
structure Mat2 where
  a : Int
  b : Int
  c : Int
  d : Int
deriving DecidableEq, Repr

def ident : Mat2 := ⟨1, 0, 0, 1⟩
def zero : Mat2 := ⟨0, 0, 0, 0⟩

def mul (A B : Mat2) : Mat2 :=
  ⟨A.a * B.a + A.b * B.c,
   A.a * B.b + A.b * B.d,
   A.c * B.a + A.d * B.c,
   A.c * B.b + A.d * B.d⟩

def add (A B : Mat2) : Mat2 :=
  ⟨A.a + B.a, A.b + B.b, A.c + B.c, A.d + B.d⟩

def gamma1 : Mat2 := ⟨1, 0, 0, -1⟩
def gamma2 : Mat2 := ⟨0, 1, 1, 0⟩

theorem gamma1_sq : mul gamma1 gamma1 = ident := by
  rfl

theorem gamma2_sq : mul gamma2 gamma2 = ident := by
  rfl

theorem gamma_anticommute : add (mul gamma1 gamma2) (mul gamma2 gamma1) = zero := by
  rfl

/-- The exhibited two-generator system has size 2, below the proposed size 2*n = 4. -/
theorem two_by_two_is_not_four : (2 : Int) < 2 * 2 := by
  decide

end Tlmc7611
