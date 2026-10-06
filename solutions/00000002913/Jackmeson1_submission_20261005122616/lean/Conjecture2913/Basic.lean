import Mathlib

/-!
# Conjecture 00000002913: the "injectivity threshold" `q > d²` is false

The conjecture (a finite-field version of the Jacobian conjecture for the plane) asserts that a
degree-`d` polynomial map over `F_q` is injective when `q > d²` (and adds a garbled clause about
the case `q ≤ d`). We refute the first clause, both for arbitrary polynomial maps and for Keller
maps (Jacobian determinant a nonzero constant):

* `asMap p m = (x^p - x + y^m, y)` over any field of characteristic `p` has Jacobian
  determinant `-1`, total degree `max p m`, and is not injective (`(0,0)` and `(1,0)` have the
  same image);
* over `F_q = GaloisField p k` with `q = p^k > (max p m)²` this violates the threshold;
* for every `d ≥ 2` and every `k` with `2^k > d²`, the Keller map `asMap 2 d` of degree `d` is not
  injective on `F_{2^k}²` (`keller_counterexample_every_degree`);
* reading (R1) (no Jacobian hypothesis) fails over every field, finite or not, for every `d ≥ 2`
  (`plain_counterexample`);
* the one-variable map `x ↦ x^d - x` (degree `d ≥ 2`) is not injective on any field
  (`univariate_counterexample`); for `d = p = char K` its derivative is `-1`.
-/

open MvPolynomial

namespace Tlmc2913

/-- A polynomial map of the plane `K² → K²`, given by its two coordinate polynomials. -/
abbrev PlaneMap (K : Type*) [CommRing K] := Fin 2 → MvPolynomial (Fin 2) K

namespace PlaneMap

variable {K : Type*} [Field K]

/-- The induced map on `K`-points `K² → K²`. -/
noncomputable def toFun (f : PlaneMap K) (x : Fin 2 → K) : Fin 2 → K := fun i => eval x (f i)

/-- The degree of a polynomial map: the maximum of the total degrees of its components. -/
def degree (f : PlaneMap K) : ℕ := max (f 0).totalDegree (f 1).totalDegree

/-- The Jacobian determinant `det (∂ fᵢ / ∂ xⱼ)`. -/
noncomputable def jacobian (f : PlaneMap K) : MvPolynomial (Fin 2) K :=
  (Matrix.of fun i j => pderiv j (f i)).det

end PlaneMap

variable {K : Type*} [Field K]

/-- The Artin–Schreier type map `(x, y) ↦ (x^p - x + y^m, y)`. -/
noncomputable def asMap (p m : ℕ) : PlaneMap K := ![X 0 ^ p - X 0 + X 1 ^ m, X 1]

/-- `(0,0)` and `(1,0)` have the same image, so the map is not injective (any field). -/
theorem asMap_not_injective {p m : ℕ} (hp : p ≠ 0) (hm : m ≠ 0) :
    ¬ Function.Injective (asMap (K := K) p m).toFun := by
  intro hinj
  have h : (asMap (K := K) p m).toFun ![0, 0] = (asMap (K := K) p m).toFun ![1, 0] := by
    funext i
    fin_cases i <;> simp [PlaneMap.toFun, asMap, zero_pow hp, zero_pow hm]
  have := congrFun (hinj h) 0
  simp at this

/-- In characteristic `p` the Jacobian determinant is the nonzero constant `-1`. -/
theorem asMap_jacobian (p m : ℕ) [CharP K p] : (asMap (K := K) p m).jacobian = -1 := by
  rw [PlaneMap.jacobian, Matrix.det_fin_two]
  simp [asMap, Derivation.leibniz_pow, pderiv_X]

/-- The first component has total degree `max p m`. -/
theorem totalDegree_first {p m : ℕ} (hp : 2 ≤ p) (hm : 1 ≤ m) :
    (X 0 ^ p - X 0 + X 1 ^ m : MvPolynomial (Fin 2) K).totalDegree = max p m := by
  apply le_antisymm
  · refine (totalDegree_add _ _).trans (max_le ?_ (by rw [totalDegree_X_pow]; exact le_max_right _ _))
    refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
    · rw [totalDegree_X_pow]; exact le_max_left _ _
    · rw [totalDegree_X]; omega
  · have h1 : Finsupp.single (0 : Fin 2) p ∈
        (X 0 ^ p - X 0 + X 1 ^ m : MvPolynomial (Fin 2) K).support := by
      rw [mem_support_iff, coeff_add, coeff_sub, coeff_X_pow, coeff_X_pow, coeff_X]
      simp [Finsupp.single_eq_single_iff, show 1 ≠ p by omega, show p ≠ 0 by omega,
        show m ≠ 0 by omega]
    have h2 : Finsupp.single (1 : Fin 2) m ∈
        (X 0 ^ p - X 0 + X 1 ^ m : MvPolynomial (Fin 2) K).support := by
      rw [mem_support_iff, coeff_add, coeff_sub, coeff_X_pow, coeff_X_pow, coeff_X]
      simp [Finsupp.single_eq_single_iff, show p ≠ 0 by omega, show m ≠ 0 by omega]
    have l1 := le_totalDegree h1
    have l2 := le_totalDegree h2
    rw [Finsupp.sum_single_index rfl] at l1 l2
    exact max_le l1 l2

theorem asMap_degree {p m : ℕ} (hp : 2 ≤ p) (hm : 1 ≤ m) :
    (asMap (K := K) p m).degree = max p m := by
  simp only [PlaneMap.degree, asMap, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [totalDegree_first hp hm, totalDegree_X]
  omega

/-- **Reading (R1), every finite field.** For every field `K` (in particular every finite field
with `Nat.card K > d²`, prime fields included) and every `d ≥ 2`, the map `(x² - x + y^d, y)` has
degree exactly `d` and is not injective on `K²`. -/
theorem plain_counterexample (d : ℕ) (hd : 2 ≤ d) :
    (asMap (K := K) 2 d).degree = d ∧ ¬ Function.Injective (asMap (K := K) 2 d).toFun :=
  ⟨(asMap_degree le_rfl (by omega)).trans (max_eq_right hd),
    asMap_not_injective (by norm_num) (by omega)⟩

/-- **Reading (R2), every field of characteristic `p`.** Over any field of prime characteristic
`p`, `(x^p - x + y^m, y)` (`m ≥ 1`) has degree `max p m`, Jacobian determinant `-1`, and is not
injective. -/
theorem keller_counterexample (p : ℕ) [hp : Fact p.Prime] [CharP K p] (m : ℕ) (hm : 1 ≤ m) :
    (asMap (K := K) p m).degree = max p m ∧ (asMap (K := K) p m).jacobian = -1 ∧
    ¬ Function.Injective (asMap (K := K) p m).toFun :=
  ⟨asMap_degree hp.out.two_le hm, asMap_jacobian p m,
    asMap_not_injective hp.out.ne_zero (by omega)⟩

/-- **Conjecture 00000002913 is false (plane, Keller maps).** For every prime `p`, every `m ≥ 1`
and every `k` with `q = p^k > (max p m)²`, the map `(x, y) ↦ (x^p - x + y^m, y)` over
`F_q = GaloisField p k` has degree `d = max p m` with `q > d²` and Jacobian determinant `-1`,
yet is not injective on `F_q²`. -/
theorem conjecture_00000002913_false (p : ℕ) [hp : Fact p.Prime] (m k : ℕ) (hm : 1 ≤ m)
    (hk : (max p m) ^ 2 < p ^ k) :
    Nat.card (GaloisField p k) = p ^ k ∧
    (asMap (K := GaloisField p k) p m).degree = max p m ∧
    (asMap (K := GaloisField p k) p m).degree ^ 2 < Nat.card (GaloisField p k) ∧
    (asMap (K := GaloisField p k) p m).jacobian = -1 ∧
    ¬ Function.Injective (asMap (K := GaloisField p k) p m).toFun := by
  have hp2 := hp.out.two_le
  have hk0 : k ≠ 0 := by
    rintro rfl
    have : 2 ≤ max p m := le_max_of_le_left hp2
    simp at hk
    nlinarith
  have hcard := GaloisField.card p k hk0
  refine ⟨hcard, asMap_degree hp2 hm, ?_, asMap_jacobian p m, asMap_not_injective (by omega) (by omega)⟩
  rw [asMap_degree hp2 hm, hcard]
  exact hk

/-- **Every degree `d ≥ 2` fails.** For each `d ≥ 2` and each `k` with `2^k > d²` (for instance
`k = 2d`), the Keller map `(x² - x + y^d, y)` of degree `d` is not injective on `F_{2^k}²`. -/
theorem keller_counterexample_every_degree (d k : ℕ) (hd : 2 ≤ d) (hk : d ^ 2 < 2 ^ k) :
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    Nat.card (GaloisField 2 k) = 2 ^ k ∧
    (asMap (K := GaloisField 2 k) 2 d).degree = d ∧
    (asMap (K := GaloisField 2 k) 2 d).jacobian = -1 ∧
    ¬ Function.Injective (asMap (K := GaloisField 2 k) 2 d).toFun := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmax : max 2 d = d := max_eq_right hd
  obtain ⟨h1, h2, -, h4, h5⟩ := conjecture_00000002913_false 2 d k (by omega) (by rwa [hmax])
  exact ⟨h1, h2.trans hmax, h4, h5⟩

/-- The threshold of `keller_counterexample_every_degree` is met by `k = 2d`. -/
theorem sq_lt_two_pow_two_mul (d : ℕ) : d ^ 2 < 2 ^ (2 * d) := by
  rw [pow_mul', sq, sq]
  exact Nat.mul_self_lt_mul_self (Nat.lt_two_pow_self)

/-! ## One variable -/

open Polynomial in
/-- **One-variable reading.** For every `d ≥ 2` the polynomial `x^d - x` has degree `d` and is
not injective on any field (`0` and `1` are both roots); in characteristic `p` the polynomial
`x^p - x` moreover has derivative `-1`. -/
theorem univariate_counterexample (d : ℕ) (hd : 2 ≤ d) :
    ((Polynomial.X ^ d - Polynomial.X : K[X])).natDegree = d ∧
    ¬ Function.Injective (fun x : K => (Polynomial.X ^ d - Polynomial.X : K[X]).eval x) := by
  refine ⟨?_, fun hinj => ?_⟩
  · rw [natDegree_sub_eq_left_of_natDegree_lt] <;> simp; omega
  · have h := @hinj 0 1 (by simp [zero_pow (by omega : d ≠ 0)])
    exact zero_ne_one h

open Polynomial in
theorem univariate_derivative (p : ℕ) [CharP K p] :
    derivative (Polynomial.X ^ p - Polynomial.X : K[X]) = -1 := by
  simp [derivative_X_pow, CharP.cast_eq_zero]

end Tlmc2913
