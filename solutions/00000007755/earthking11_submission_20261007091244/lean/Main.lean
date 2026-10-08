import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Tactic.LinearCombination

/-!
Counterexample to the first assertion of conjecture 00000007755, in the
normalized quadratic parameter line. Distinct parameters are proved to be
inequivalent under affine conjugacy.
-/

namespace TLMC7755

abbrev K := AlgebraicClosure ℚ

def Preperiodic (p : Polynomial K) (x : K) : Prop :=
  ∃ m n : ℕ, m < n ∧ (p.eval^[m]) x = (p.eval^[n]) x

def PCF (p : Polynomial K) : Prop :=
  ∀ x : K, p.derivative.eval x = 0 → Preperiodic p x

/- The normalized family has a critical point at zero.  The polynomials
   `orbitPoly n` record its orbit as the parameter varies. -/
noncomputable def normalized (c : K) : Polynomial K :=
  Polynomial.X ^ 2 + Polynomial.C c

noncomputable def orbitPoly : ℕ → Polynomial K
  | 0 => 0
  | n + 1 => orbitPoly n ^ 2 + Polynomial.X

theorem orbitPoly_eval (c : K) (n : ℕ) :
    (orbitPoly n).eval c = ((normalized c).eval^[n]) 0 := by
  induction n with
  | zero => simp [orbitPoly]
  | succ n ih =>
    simp only [orbitPoly, Polynomial.eval_add, Polynomial.eval_pow,
      Polynomial.eval_X, ih, Function.iterate_succ_apply']
    simp [normalized]

noncomputable def rootPoly : ℕ → Polynomial K
  | 0 => 1
  | n + 1 => Polynomial.X * (rootPoly n) ^ 2 + 1

theorem rootPoly_const (n : ℕ) : (rootPoly n).eval 0 = 1 := by
  induction n with
  | zero => simp [rootPoly]
  | succ n ih => simp [rootPoly]

theorem rootPoly_linear (n : ℕ) : (rootPoly (n + 1)).coeff 1 = 1 := by
  have h1 : (1 : Polynomial K).coeff 1 = 0 := by
    change (Polynomial.C (1 : K)).coeff 1 = 0
    rw [Polynomial.coeff_C]
    simp
  simp [rootPoly, Polynomial.coeff_X_mul, Polynomial.coeff_zero_eq_eval_zero,
    rootPoly_const, h1]

theorem rootPoly_nondegree_zero (n : ℕ) : (rootPoly (n + 1)).degree ≠ 0 := by
  intro h
  have heq := Polynomial.eq_C_of_degree_le_zero (le_of_eq h)
  have hcoeff := congrArg (fun p : Polynomial K => p.coeff 1) heq
  norm_num [rootPoly_linear] at hcoeff

theorem rootPoly_has_nonzero_root (n : ℕ) :
    ∃ c : K, c ≠ 0 ∧ (rootPoly (n + 1)).eval c = 0 := by
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_root (rootPoly (n + 1))
    (rootPoly_nondegree_zero n)
  refine ⟨c, ?_, hc⟩
  intro h
  subst c
  simp [rootPoly_const] at hc

theorem orbitPoly_succ_eq (n : ℕ) :
    orbitPoly (n + 1) = Polynomial.X * rootPoly n := by
  induction n with
  | zero => simp [orbitPoly, rootPoly]
  | succ n ih =>
    change (orbitPoly (n + 1)) ^ 2 + Polynomial.X =
      Polynomial.X * (Polynomial.X * (rootPoly n) ^ 2 + 1)
    rw [ih]
    ring

theorem normalized_eval (c x : K) : (normalized c).eval x = x ^ 2 + c := by
  simp [normalized]

theorem normalized_derivative (c : K) :
    (normalized c).derivative = 2 * Polynomial.X := by
  simp [normalized, Polynomial.derivative_pow]
  exact Polynomial.C_ofNat 2

theorem normalized_critical_iff (c x : K) :
    (normalized c).derivative.eval x = 0 ↔ x = 0 := by
  rw [normalized_derivative]
  simp

theorem normalized_pcf_of_period (c : K) (n : ℕ) (hn : 0 < n)
    (hper : ((normalized c).eval^[n]) 0 = 0) : PCF (normalized c) := by
  intro x hx
  have hx0 := (normalized_critical_iff c x).mp hx
  subst x
  exact ⟨0, n, hn, by simpa using hper.symm⟩

theorem normalized_root_period (n : ℕ) (c : K)
    (h : (rootPoly n).eval c = 0) :
    ((normalized c).eval^[n + 1]) 0 = 0 := by
  rw [← orbitPoly_eval, orbitPoly_succ_eq]
  simp [h]

theorem exists_normalized_pcf_exact_prime_period (p : ℕ) (hp : p.Prime) :
    ∃ c : K, PCF (normalized c) ∧
      Function.minimalPeriod (normalized c).eval 0 = p := by
  have hp2 : 2 ≤ p := hp.two_le
  obtain ⟨c, hc0, hcroot⟩ := rootPoly_has_nonzero_root (p - 2)
  have hidx : p - 2 + 1 = p - 1 := by omega
  have hidx2 : p - 1 + 1 = p := by omega
  have hper : ((normalized c).eval^[p]) 0 = 0 := by
    simpa [hidx2] using normalized_root_period (p - 1) c
      (by simpa [hidx] using hcroot)
  have hfix : ¬ Function.IsFixedPt (normalized c).eval 0 := by
    simpa [Function.IsFixedPt, normalized_eval] using hc0
  haveI : Fact p.Prime := ⟨hp⟩
  exact ⟨c, normalized_pcf_of_period c p (by omega) hper,
    Function.minimalPeriod_eq_prime (by simpa [Function.IsPeriodicPt,
      Function.IsFixedPt] using hper) hfix⟩

theorem infinite_normalized_pcf_parameters :
    Set.Infinite {c : K | PCF (normalized c)} := by
  let s : Set K := {c | PCF (normalized c)}
  let period : K → ℕ := fun c => Function.minimalPeriod (normalized c).eval 0
  have hprimes : {p : ℕ | p.Prime} ⊆ period '' s := by
    intro p hp
    obtain ⟨c, hc, hperiod⟩ := exists_normalized_pcf_exact_prime_period p hp
    exact ⟨c, hc, hperiod⟩
  intro hfinite
  exact Nat.infinite_setOfPred_prime ((hfinite.image period).subset hprimes)

theorem normalized_injective : Function.Injective normalized := by
  intro c d h
  have he := congrArg (fun p : Polynomial K => p.eval 0) h
  simpa [normalized_eval] using he

theorem normalized_degree (c : K) : (normalized c).degree = 2 := by
  unfold normalized
  have hd : (Polynomial.X ^ 2 : Polynomial K).degree = 2 := by simp
  rw [Polynomial.degree_add_C (by rw [hd]; decide)]
  exact hd

theorem infinite_normalized_quadratic_pcf :
    Set.Infinite {p : Polynomial K | p.degree = 2 ∧ PCF p} := by
  have hi : Set.Infinite (normalized '' {c : K | PCF (normalized c)}) :=
    infinite_normalized_pcf_parameters.image normalized_injective.injOn
  exact hi.mono (by
    rintro p ⟨c, hc, rfl⟩
    exact ⟨normalized_degree c, hc⟩)

def AffineConjugate (c d : K) : Prop :=
  ∃ a b : K, a ≠ 0 ∧ ∀ x : K,
    a * (normalized c).eval x + b = (normalized d).eval (a * x + b)

theorem normalized_affine_conjugate_iff (c d : K) :
    AffineConjugate c d ↔ c = d := by
  constructor
  · rintro ⟨a, b, ha, h⟩
    have h0 := h 0
    have h1 := h 1
    have hm1 := h (-1)
    simp [normalized_eval] at h0 h1 hm1
    have hab : 4 * (a * b) = 0 := by
      linear_combination hm1 - h1
    have hb : b = 0 := by
      have h4 : (4 : K) ≠ 0 := by norm_num
      have hab0 : a * b = 0 := (mul_eq_zero.mp hab).resolve_left h4
      exact (mul_eq_zero.mp hab0).resolve_left ha
    subst b
    have ha2 : a * a = a := by
      linear_combination h0 - h1
    have ha1 : a = 1 := by
      have hmul : a * a = a * 1 := by simpa using ha2
      exact mul_left_cancel₀ ha hmul
    subst a
    simpa using h0
  · intro h
    subst d
    refine ⟨1, 0, one_ne_zero, ?_⟩
    intro x
    simp

#print axioms infinite_normalized_pcf_parameters
#print axioms infinite_normalized_quadratic_pcf
#print axioms normalized_affine_conjugate_iff

end TLMC7755
