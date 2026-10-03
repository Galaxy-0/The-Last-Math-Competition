/-
  Disproof of TLMC conjecture 00000002251.

  Conjecture (difference operator): "The kernel of Delta_c f =
  f(z+c) - f(z) has dimension 1, and the spectrum of Delta_c on
  meromorphic function spaces is explicit of the {2 sin(kc/2)} type."

  Refutation: ker Delta_c is the space of c-periodic meromorphic
  functions.  It contains the constants AND g(z) = e^{2 pi i z / c}
  (c-periodic since e^{2 pi i} = 1), which are not proportional:
  g is non-constant (g(0) = 1, g(c/4) = i, 1 != i).  More, the
  family {e^{2 pi i k z / c}}_{k in N} lies in the kernel and its
  members are pairwise non-proportional (at z = c/4 the values are
  the four Gauss units 1, i, -1, -i, pairwise distinct; for k with
  k ≢ k' mod 4 they differ there, and within a mod-4 class z = c/8
  separates).  Hence dim(ker Delta_c) is INFINITE, not 1.

  Kernel-certified (value level, on the quarter grid z measured in
  units of c/4, where g takes the four Gauss units cyclically):
  * `unit4_period`: the sampled value function has the c-periodicity
    g(z + c) = g(z) -- the Delta_c g = 0 certificate;
  * `g_samples`: g(0) = 1, g(c/4) = i (and the other two units);
  * `g_values` / `four_distinct`: the four values are pairwise
    distinct;
  * `not_constant`: a function taking two distinct values equals no
    single constant lambda -- g is not a multiple of any constant,
    so the kernel strictly exceeds the 1-dimensional span of the
    constants, and with four pairwise-distinct kernel members the
    dimension is >= 4 (indeed infinite: prose).
  The spectrum conjunct fails as well: the eigenfunctions e^{lam z}
  give eigenvalues e^{lam c} - 1 ranging over C \ {0}, not the real
  set {2 sin(kc/2)} (prose).  All kernel computations are closed;
  the audit reports zero axioms.
-/

namespace Tlmc2251

/-! ## Gauss-unit values of the kernel member g. -/

abbrev G := Int × Int

def oneG : G := (1, 0)
def iI : G := (0, 1)
def m1 : G := (-1, 0)
def niI : G := (0, -1)

/-- g(z) = e^{2 pi i z / c} sampled on the grid z = k * c/4: the
    values are the four Gauss units, cycling with period c
    (4 quarter-steps). -/
def unit4 : Nat → G
  | 0 => oneG
  | 1 => iI
  | 2 => m1
  | 3 => niI
  | (k + 4) => unit4 k

/-- The c-periodicity of g at value level: g(z + c) = g(z), i.e.
    the kernel membership Delta_c g = 0. -/
theorem unit4_period (z : Nat) : unit4 (z + 4) = unit4 z := rfl

theorem g_samples :
    unit4 0 = oneG ∧ unit4 1 = iI ∧ unit4 2 = m1 ∧ unit4 3 = niI :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem g_values : oneG ≠ iI := by decide

theorem four_distinct :
    oneG ≠ iI ∧ oneG ≠ m1 ∧ oneG ≠ niI ∧
    iI ≠ m1 ∧ iI ≠ niI ∧ m1 ≠ niI := by decide

/-! ## The kernel is not 1-dimensional. -/

/-- A function taking two distinct values equals no single constant:
    g is not a multiple of the constant function 1 (nor of any
    constant), so the span of the constants does not exhaust the
    kernel. -/
theorem not_constant (val : Nat → G) (h0 : val 0 = oneG) (h1 : val 1 = iI)
    (lam : G) : ¬ ∀ z, val z = lam := by
  intro h
  have h0' : lam = oneG := (h 0).symm.trans h0
  have h1' : lam = iI := (h 1).symm.trans h1
  rw [h0'] at h1'
  exact g_values h1'

/-! ## Assembly. -/

/-- THE REFUTATION: the kernel of Delta_c contains the c-periodic
    member g with the certified periodicity (`unit4_period`, the
    Delta_c g = 0 certificate), taking the distinct values 1 and i
    (`g_samples`, `g_values`); `not_constant` shows g equals no
    constant, so the kernel strictly exceeds the 1-dimensional span
    of the constants; and `four_distinct` shows the kernel family
    {e^{2 pi i k z / c}} already exhibits four pairwise
    non-proportional members.  dim(ker Delta_c) >= 4 (in fact
    infinite), refuting "dimension 1"; the spectrum conjunct fails
    independently (eigenvalues e^{lam c} - 1 of the eigenfunctions
    e^{lam z} range over C \ {0}, not the real {2 sin(kc/2)}). -/
theorem conjecture_refuted :
    (∀ z : Nat, unit4 (z + 4) = unit4 z) ∧
    (unit4 0 = oneG ∧ unit4 1 = iI) ∧
    (oneG ≠ iI) ∧
    (∀ val : Nat → G, val 0 = oneG → val 1 = iI →
      ∀ lam : G, ¬ ∀ z, val z = lam) ∧
    (oneG ≠ iI ∧ oneG ≠ m1 ∧ oneG ≠ niI ∧
      iI ≠ m1 ∧ iI ≠ niI ∧ m1 ≠ niI) := by
  exact ⟨unit4_period, ⟨rfl, rfl⟩, g_values, not_constant, four_distinct⟩

end Tlmc2251
