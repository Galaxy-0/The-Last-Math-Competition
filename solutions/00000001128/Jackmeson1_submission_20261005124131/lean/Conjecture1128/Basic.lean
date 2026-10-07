import Mathlib

/-!
# Conjecture 00000001128 (disproof)

`M(w, j)` is the largest monomial coefficient in the degree-`j` part of the Schubert polynomial
`𝔖_w`. The conjecture says `M(w, j) = min(j, ℓ(w), ⌈ℓ(w)/2⌉)! · C(w)` with `C(w)` a
lattice-path count.

Schubert polynomials (Lascoux–Schützenberger) in `S_{n+1}`, variables `x_0, …, x_n`
(0-indexed here):
* `𝔖_{w₀} = x_0^n x_1^(n-1) ⋯ x_{n-1}`, `w₀` the longest permutation;
* `∂_i 𝔖_w = 𝔖_{w s_i}` if `w(i) > w(i+1)`, and `∂_i 𝔖_w = 0` if `w(i) < w(i+1)`;
where `∂_i P = (P - s_i P) / (x_i - x_{i+1})` is the divided difference.

`∂_i` is the exact quotient (divisibility proved for every polynomial); the characterization is
`IsSchubert`; the families for `S_3` and `S_4` are constructed and verified. `w = 321 = w₀ ∈ S_3`
has `ℓ = 3`, `𝔖_321 = x_0² x_1`, `M(321, 3) = 1`, but the formula gives `min(3, 3, 2)! · C = 2C`.
The 321-avoiding `w = 4123 ∈ S_4` has `ℓ = 3`, `𝔖_4123 = x_0³`, `M = 1`, the same contradiction.
-/

open MvPolynomial Equiv Finset

namespace C1128

variable {n : ℕ}

/-- Adjacent transposition `s_i = (i, i+1)` of `Fin (n+1)`, for `i : Fin n`. -/
def s (i : Fin n) : Perm (Fin (n + 1)) := swap i.castSucc i.succ

/-- `s_i` acting on polynomials (swap `x_i` and `x_{i+1}`). -/
noncomputable def sAct (i : Fin n) (P : MvPolynomial (Fin (n + 1)) ℤ) :
    MvPolynomial (Fin (n + 1)) ℤ := rename (s i) P

theorem dvd_sub_sAct (i : Fin n) (P : MvPolynomial (Fin (n + 1)) ℤ) :
    (X i.castSucc - X i.succ) ∣ P - sAct i P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [sAct]
  | add p q hp hq =>
    have : p + q - sAct i (p + q) = (p - sAct i p) + (q - sAct i q) := by
      simp [sAct]; ring
    rw [this]; exact dvd_add hp hq
  | mul_X p k hp =>
    have hk : (X i.castSucc - X i.succ : MvPolynomial (Fin (n + 1)) ℤ) ∣ X k - X (s i k) := by
      by_cases h1 : k = i.castSucc
      · subst h1; simp [s]
      · by_cases h2 : k = i.succ
        · subst h2; simp only [s, swap_apply_right]
          exact ⟨-1, by ring⟩
        · simp [s, swap_apply_of_ne_of_ne h1 h2]
    have : p * X k - sAct i (p * X k) = (p - sAct i p) * X k + sAct i p * (X k - X (s i k)) := by
      simp [sAct]; ring
    rw [this]
    exact dvd_add (dvd_mul_of_dvd_left hp _) (dvd_mul_of_dvd_right hk _)

/-- Divided difference `∂_i P = (P - s_i P) / (x_i - x_{i+1})` (an exact quotient). -/
noncomputable def dd (i : Fin n) (P : MvPolynomial (Fin (n + 1)) ℤ) :
    MvPolynomial (Fin (n + 1)) ℤ := (dvd_sub_sAct i P).choose

theorem dd_spec (i : Fin n) (P : MvPolynomial (Fin (n + 1)) ℤ) :
    (X i.castSucc - X i.succ) * dd i P = P - sAct i P :=
  (dvd_sub_sAct i P).choose_spec.symm

/-- `∂_i P` is the unique `Q` with `(x_i - x_{i+1}) Q = P - s_i P`. -/
theorem dd_eq {i : Fin n} {P Q : MvPolynomial (Fin (n + 1)) ℤ}
    (h : (X i.castSucc - X i.succ) * Q = P - sAct i P) : dd i P = Q := by
  have hne : (X i.castSucc - X i.succ : MvPolynomial (Fin (n + 1)) ℤ) ≠ 0 :=
    sub_ne_zero.mpr fun h' => (Fin.castSucc_lt_succ (i := i)).ne (X_injective h')
  exact mul_left_cancel₀ hne ((dd_spec i P).trans h.symm)

theorem ddSwap {i : Fin n} {a b : Fin (n + 1)} (hs : s i = swap a b) (ha : i.castSucc = a)
    (hb : i.succ = b) {P Q : MvPolynomial (Fin (n + 1)) ℤ}
    (h : (X a - X b) * Q = P - rename (swap a b) P) : dd i P = Q := by
  subst ha hb; exact dd_eq (by rw [sAct, hs]; exact h)

/-- `x^δ = x_0^n x_1^(n-1) ⋯ x_n^0`. -/
noncomputable def xDelta (n : ℕ) : MvPolynomial (Fin (n + 1)) ℤ :=
  ∏ k : Fin (n + 1), X k ^ (n - k.val)

/-- Lascoux–Schützenberger characterization of the Schubert polynomials of `S_{n+1}`. -/
structure IsSchubert (S : Perm (Fin (n + 1)) → MvPolynomial (Fin (n + 1)) ℤ) : Prop where
  top : S Fin.revPerm = xDelta n
  step : ∀ (w : Perm (Fin (n + 1))) (i : Fin n),
    w i.succ < w i.castSucc → dd i (S w) = S (w * s i)
  zero : ∀ (w : Perm (Fin (n + 1))) (i : Fin n),
    w i.castSucc < w i.succ → dd i (S w) = 0

/-- Coxeter length = number of inversions. -/
def len {m : ℕ} (w : Perm (Fin m)) : ℕ := #{p : Fin m × Fin m | p.1 < p.2 ∧ w p.2 < w p.1}

/-- `M(P, j)`: maximal coefficient among monomials of total degree `j` in `P`
(`⊥` if the degree-`j` part is zero). -/
noncomputable def maxCoeff {σ : Type*} (P : MvPolynomial σ ℤ) (j : ℕ) : WithBot ℤ :=
  ((P.support.filter fun m => m.degree = j).image fun m => P.coeff m).max

/-- The conjecture's right-hand side `min(j, ℓ, ⌈ℓ/2⌉)! · C`. -/
def formula (l j : ℕ) (C : ℤ) : ℤ := ((min j (min l ((l + 1) / 2))).factorial : ℤ) * C

/-! ### `S_3` -/

/-- Explicit Schubert polynomials of `S_3`, indexed by `(w 0, w 1)`. -/
noncomputable def sch3 : Fin 3 → Fin 3 → MvPolynomial (Fin 3) ℤ
  | 2, 1 => X 0 ^ 2 * X 1   -- 321
  | 1, 2 => X 0 * X 1       -- 231
  | 2, 0 => X 0 ^ 2         -- 312
  | 0, 2 => X 0 + X 1       -- 132
  | 1, 0 => X 0             -- 213
  | _, _ => 1               -- 123

noncomputable def S3 (w : Perm (Fin 3)) : MvPolynomial (Fin 3) ℤ := sch3 (w 0) (w 1)

theorem s0 : (s (0 : Fin 2)) = swap 0 1 := rfl
theorem s1 : (s (1 : Fin 2)) = swap 1 2 := rfl

theorem perm3_cases (w : Perm (Fin 3)) :
    (w 0 = 0 ∧ w 1 = 1 ∧ w 2 = 2) ∨ (w 0 = 0 ∧ w 1 = 2 ∧ w 2 = 1) ∨
    (w 0 = 1 ∧ w 1 = 0 ∧ w 2 = 2) ∨ (w 0 = 1 ∧ w 1 = 2 ∧ w 2 = 0) ∨
    (w 0 = 2 ∧ w 1 = 0 ∧ w 2 = 1) ∨ (w 0 = 2 ∧ w 1 = 1 ∧ w 2 = 0) := by
  revert w; decide

@[simp] theorem sw01_2 : swap (0 : Fin 3) 1 2 = 2 := by decide
@[simp] theorem sw12_0 : swap (1 : Fin 3) 2 0 = 0 := by decide

set_option hygiene false in
/-- Split `w ∈ S_3` into its 6 one-line forms and discharge each case. -/
macro "s3cases " t:term : tactic => `(tactic| (
  rcases perm3_cases w with ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ |
    ⟨a, b, c⟩ <;> simp only [a, b, c] at h' ⊢ <;>
  first | (exfalso; revert h'; decide) | exact ddSwap $t rfl rfl (by simp [sch3] <;> ring)))

/-- The explicit `S_3` family satisfies the Lascoux–Schützenberger characterization. -/
theorem isSchubert_S3 : IsSchubert (n := 2) S3 := by
  refine ⟨?_, ?_, ?_⟩
  · have h0 : (Fin.revPerm : Perm (Fin 3)) 0 = 2 := by decide
    have h1 : (Fin.revPerm : Perm (Fin 3)) 1 = 1 := by decide
    simp [S3, h0, h1, sch3, xDelta, Fin.prod_univ_three]
  · intro w i h
    fin_cases i
    · have h' : w 1 < w 0 := h
      have e0 : (w * s (0 : Fin 2)) 0 = w 1 := by simp [s0]
      have e1 : (w * s (0 : Fin 2)) 1 = w 0 := by simp [s0]
      change dd 0 (sch3 (w 0) (w 1)) = sch3 ((w * s (0 : Fin 2)) 0) ((w * s (0 : Fin 2)) 1)
      rw [e0, e1]; s3cases s0
    · have h' : w 2 < w 1 := h
      have e0 : (w * s (1 : Fin 2)) 0 = w 0 := by simp [s1]
      have e1 : (w * s (1 : Fin 2)) 1 = w 2 := by simp [s1]
      change dd 1 (sch3 (w 0) (w 1)) = sch3 ((w * s (1 : Fin 2)) 0) ((w * s (1 : Fin 2)) 1)
      rw [e0, e1]; s3cases s1
  · intro w i h
    fin_cases i
    · have h' : w 0 < w 1 := h
      change dd 0 (sch3 (w 0) (w 1)) = 0; s3cases s0
    · have h' : w 1 < w 2 := h
      change dd 1 (sch3 (w 0) (w 1)) = 0; s3cases s1

/-- `w = 321` in one-line notation, i.e. `w₀ ∈ S_3`. -/
def w321 : Perm (Fin 3) := Fin.revPerm

theorem w321_oneLine : w321 0 = 2 ∧ w321 1 = 1 ∧ w321 2 = 0 := by decide
theorem len_w321 : len w321 = 3 := by decide

/-- For any family satisfying the characterization, `𝔖_321 = x_0² x_1`. -/
theorem schubert_321 {S : Perm (Fin 3) → MvPolynomial (Fin 3) ℤ} (hS : IsSchubert (n := 2) S) :
    S w321 = X 0 ^ 2 * X 1 := by
  rw [w321, hS.top]; simp [xDelta, Fin.prod_univ_three]

theorem maxCoeff_x0sq_x1 : maxCoeff (X 0 ^ 2 * X 1 : MvPolynomial (Fin 3) ℤ) 3 = 1 := by
  have hm : (X 0 ^ 2 * X 1 : MvPolynomial (Fin 3) ℤ) =
      monomial (Finsupp.single 0 2 + Finsupp.single 1 1) 1 := by
    rw [X_pow_eq_monomial, X, monomial_mul, one_mul]
  rw [maxCoeff, hm, support_monomial, if_neg one_ne_zero]
  have hd : (Finsupp.single (0 : Fin 3) 2 + Finsupp.single 1 1).degree = 3 := by
    rw [map_add, Finsupp.degree_single, Finsupp.degree_single]
  rw [Finset.filter_singleton, if_pos hd, Finset.image_singleton, coeff_monomial, if_pos rfl,
    Finset.max_singleton]
  rfl

/-- **Disproof (instance `w = 321`, `j = ℓ(w) = 3`).** No integer `C` satisfies
`M(321, 3) = min(3, ℓ(321), ⌈ℓ(321)/2⌉)! · C`. -/
theorem disproof_321 {S : Perm (Fin 3) → MvPolynomial (Fin 3) ℤ} (hS : IsSchubert (n := 2) S) :
    ¬ ∃ C : ℤ, maxCoeff (S w321) (len w321) = (formula (len w321) (len w321) C : WithBot ℤ) := by
  rintro ⟨C, hC⟩
  rw [schubert_321 hS, len_w321, maxCoeff_x0sq_x1] at hC
  have h1 : (1 : ℤ) = formula 3 3 C := WithBot.coe_injective hC
  simp [formula] at h1
  omega

/-- **Disproof (family form).** The Schubert family of `S_3` exists, and no function
`C : S_3 → ℤ` satisfies `M(w, ℓ(w)) = min(ℓ(w), ℓ(w), ⌈ℓ(w)/2⌉)! · C(w)` for all `w`. -/
theorem disproof :
    IsSchubert (n := 2) S3 ∧
    ∀ S : Perm (Fin 3) → MvPolynomial (Fin 3) ℤ, IsSchubert (n := 2) S →
      ¬ ∃ C : Perm (Fin 3) → ℤ, ∀ w j, j = len w →
        maxCoeff (S w) j = (formula (len w) j (C w) : WithBot ℤ) := by
  refine ⟨isSchubert_S3, fun S hS ⟨C, hC⟩ => disproof_321 hS ⟨C w321, hC w321 _ rfl⟩⟩

/-! ### `S_4` and the 321-avoiding reading -/

/-- Explicit Schubert polynomials of `S_4`, indexed by `(w 0, w 1, w 2)`. -/
noncomputable def sch4 : Fin 4 → Fin 4 → Fin 4 → MvPolynomial (Fin 4) ℤ
  | 0, 1, 2 => 1
  | 0, 1, 3 => X 0 + X 1 + X 2
  | 0, 2, 1 => X 0 + X 1
  | 0, 2, 3 => X 0 * X 1 + X 0 * X 2 + X 1 * X 2
  | 0, 3, 1 => X 0 ^ 2 + X 0 * X 1 + X 1 ^ 2
  | 0, 3, 2 => X 0 ^ 2 * X 1 + X 0 ^ 2 * X 2 + X 0 * X 1 ^ 2 + X 0 * X 1 * X 2 + X 1 ^ 2 * X 2
  | 1, 0, 2 => X 0
  | 1, 0, 3 => X 0 ^ 2 + X 0 * X 1 + X 0 * X 2
  | 1, 2, 0 => X 0 * X 1
  | 1, 2, 3 => X 0 * X 1 * X 2
  | 1, 3, 0 => X 0 ^ 2 * X 1 + X 0 * X 1 ^ 2
  | 1, 3, 2 => X 0 ^ 2 * X 1 * X 2 + X 0 * X 1 ^ 2 * X 2
  | 2, 0, 1 => X 0 ^ 2
  | 2, 0, 3 => X 0 ^ 2 * X 1 + X 0 ^ 2 * X 2
  | 2, 1, 0 => X 0 ^ 2 * X 1
  | 2, 1, 3 => X 0 ^ 2 * X 1 * X 2
  | 2, 3, 0 => X 0 ^ 2 * X 1 ^ 2
  | 2, 3, 1 => X 0 ^ 2 * X 1 ^ 2 * X 2
  | 3, 0, 1 => X 0 ^ 3
  | 3, 0, 2 => X 0 ^ 3 * X 1 + X 0 ^ 3 * X 2
  | 3, 1, 0 => X 0 ^ 3 * X 1
  | 3, 1, 2 => X 0 ^ 3 * X 1 * X 2
  | 3, 2, 0 => X 0 ^ 3 * X 1 ^ 2
  | 3, 2, 1 => X 0 ^ 3 * X 1 ^ 2 * X 2
  | _, _, _ => 0

theorem perm4_cases (w : Perm (Fin 4)) :
    (w 0, w 1, w 2, w 3) ∈ ([
      (0, 1, 2, 3), (0, 1, 3, 2), (0, 2, 1, 3), (0, 2, 3, 1), (0, 3, 1, 2), (0, 3, 2, 1),
      (1, 0, 2, 3), (1, 0, 3, 2), (1, 2, 0, 3), (1, 2, 3, 0), (1, 3, 0, 2), (1, 3, 2, 0),
      (2, 0, 1, 3), (2, 0, 3, 1), (2, 1, 0, 3), (2, 1, 3, 0), (2, 3, 0, 1), (2, 3, 1, 0),
      (3, 0, 1, 2), (3, 0, 2, 1), (3, 1, 0, 2), (3, 1, 2, 0), (3, 2, 0, 1), (3, 2, 1, 0)
    ] : List (Fin 4 × Fin 4 × Fin 4 × Fin 4)) := by
  revert w; decide

noncomputable def S4 (w : Perm (Fin 4)) : MvPolynomial (Fin 4) ℤ := sch4 (w 0) (w 1) (w 2)

@[simp] theorem q01_2 : swap (0 : Fin 4) 1 2 = 2 := by decide
@[simp] theorem q01_3 : swap (0 : Fin 4) 1 3 = 3 := by decide
@[simp] theorem q12_0 : swap (1 : Fin 4) 2 0 = 0 := by decide
@[simp] theorem q12_3 : swap (1 : Fin 4) 2 3 = 3 := by decide
@[simp] theorem q23_0 : swap (2 : Fin 4) 3 0 = 0 := by decide
@[simp] theorem q23_1 : swap (2 : Fin 4) 3 1 = 1 := by decide


theorem t0 : s (0 : Fin 3) = swap 0 1 := rfl
theorem t1 : s (1 : Fin 3) = swap 1 2 := rfl
theorem t2 : s (2 : Fin 3) = swap 2 3 := rfl

set_option hygiene false in
/-- Split `w ∈ S_4` into its 24 one-line forms, then discharge each case with the
characterization of `∂_i` (`t` is the matching `s i = swap _ _` lemma). -/
macro "s4cases " t:term : tactic => `(tactic| (
  have e := perm4_cases w
  simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at e
  casesm* _ ∨ _ <;> obtain ⟨a, b, c, d⟩ := ‹_ ∧ _ ∧ _ ∧ _› <;>
  simp only [a, b, c, d] at h' ⊢ <;>
  first
    | (exfalso; revert h'; decide)
    | exact ddSwap $t rfl rfl (by simp [sch4] <;> ring)))

theorem S4_step0 (w : Perm (Fin 4)) (h' : w 1 < w 0) :
    dd (0 : Fin 3) (S4 w) = S4 (w * s (0 : Fin 3)) := by
  have e0 : (w * s (0 : Fin 3)) 0 = w 1 := by simp [t0]
  have e1 : (w * s (0 : Fin 3)) 1 = w 0 := by simp [t0]
  have e2 : (w * s (0 : Fin 3)) 2 = w 2 := by simp [t0]
  simp only [S4]; rw [e0, e1, e2]; s4cases t0

theorem S4_step1 (w : Perm (Fin 4)) (h' : w 2 < w 1) :
    dd (1 : Fin 3) (S4 w) = S4 (w * s (1 : Fin 3)) := by
  have e0 : (w * s (1 : Fin 3)) 0 = w 0 := by simp [t1]
  have e1 : (w * s (1 : Fin 3)) 1 = w 2 := by simp [t1]
  have e2 : (w * s (1 : Fin 3)) 2 = w 1 := by simp [t1]
  simp only [S4]; rw [e0, e1, e2]; s4cases t1

theorem S4_step2 (w : Perm (Fin 4)) (h' : w 3 < w 2) :
    dd (2 : Fin 3) (S4 w) = S4 (w * s (2 : Fin 3)) := by
  have e0 : (w * s (2 : Fin 3)) 0 = w 0 := by simp [t2]
  have e1 : (w * s (2 : Fin 3)) 1 = w 1 := by simp [t2]
  have e2 : (w * s (2 : Fin 3)) 2 = w 3 := by simp [t2]
  simp only [S4]; rw [e0, e1, e2]; s4cases t2

theorem S4_zero0 (w : Perm (Fin 4)) (h' : w 0 < w 1) : dd (0 : Fin 3) (S4 w) = 0 := by
  simp only [S4]; s4cases t0

theorem S4_zero1 (w : Perm (Fin 4)) (h' : w 1 < w 2) : dd (1 : Fin 3) (S4 w) = 0 := by
  simp only [S4]; s4cases t1

theorem S4_zero2 (w : Perm (Fin 4)) (h' : w 2 < w 3) : dd (2 : Fin 3) (S4 w) = 0 := by
  simp only [S4]; s4cases t2

theorem S4_top : S4 Fin.revPerm = xDelta 3 := by
  have h : ((Fin.revPerm : Perm (Fin 4)) 0, (Fin.revPerm : Perm (Fin 4)) 1,
      (Fin.revPerm : Perm (Fin 4)) 2) = (3, 2, 1) := by decide
  simp only [Prod.mk.injEq] at h
  rw [S4, h.1, h.2.1, h.2.2]
  simp [sch4, xDelta, Fin.prod_univ_four]

/-- The explicit `S_4` family satisfies the Lascoux–Schützenberger characterization. -/
theorem isSchubert_S4 : IsSchubert (n := 3) S4 := by
  refine ⟨S4_top, fun w i h => ?_, fun w i h => ?_⟩ <;> fin_cases i
  exacts [S4_step0 w h, S4_step1 w h, S4_step2 w h, S4_zero0 w h, S4_zero1 w h, S4_zero2 w h]

/-- `w = 4123` (0-indexed values `3, 0, 1, 2`), reached from `w₀ = 4321` via `4312, 4132`. -/
def w4123 : Perm (Fin 4) := Fin.revPerm * s 2 * s 1 * s 2

/-- `w` avoids the pattern 321. -/
def Avoids321 {m : ℕ} (w : Perm (Fin m)) : Prop :=
  ∀ a b c : Fin m, a < b → b < c → ¬ (w c < w b ∧ w b < w a)

theorem w4123_facts : w4123 0 = 3 ∧ w4123 1 = 0 ∧ w4123 2 = 1 ∧ w4123 3 = 2 ∧
    len w4123 = 3 ∧ Avoids321 w4123 := by
  unfold Avoids321; decide

/-- Any family satisfying the characterization has `𝔖_4123 = x_0³`. -/
theorem schubert_4123 {S : Perm (Fin 4) → MvPolynomial (Fin 4) ℤ} (hS : IsSchubert (n := 3) S) :
    S w4123 = X 0 ^ 3 := by
  have chain : ∀ T : Perm (Fin 4) → MvPolynomial (Fin 4) ℤ, IsSchubert (n := 3) T →
      T w4123 = dd 2 (dd 1 (dd 2 (xDelta 3))) := by
    intro T hT
    rw [← hT.top, hT.step _ 2 (by decide), hT.step _ 1 (by decide), hT.step _ 2 (by decide)]
    rfl
  rw [chain S hS, ← chain S4 isSchubert_S4]
  obtain ⟨h0, h1, h2, -⟩ := w4123_facts
  simp only [S4, h0, h1, h2, sch4]

theorem maxCoeff_x0cube : maxCoeff (X 0 ^ 3 : MvPolynomial (Fin 4) ℤ) 3 = 1 := by
  rw [maxCoeff, X_pow_eq_monomial, support_monomial, if_neg one_ne_zero,
    Finset.filter_singleton, if_pos (Finsupp.degree_single _ _), Finset.image_singleton,
    coeff_monomial, if_pos rfl, Finset.max_singleton]
  rfl

/-- **Disproof on 321-avoiding permutations.** `4123 ∈ S_4` avoids 321, `ℓ = 3`,
`𝔖_4123 = x_0³`, so `M(4123, 3) = 1`, while the formula gives `2 C`. -/
theorem disproof_321_avoiding :
    IsSchubert (n := 3) S4 ∧ Avoids321 w4123 ∧
    ∀ S : Perm (Fin 4) → MvPolynomial (Fin 4) ℤ, IsSchubert (n := 3) S →
      ¬ ∃ C : ℤ, maxCoeff (S w4123) (len w4123) =
        (formula (len w4123) (len w4123) C : WithBot ℤ) := by
  obtain ⟨-, -, -, -, hl, hav⟩ := w4123_facts
  refine ⟨isSchubert_S4, hav, fun S hS ⟨C, hC⟩ => ?_⟩
  rw [schubert_4123 hS, hl, maxCoeff_x0cube] at hC
  have h1 : (1 : ℤ) = formula 3 3 C := WithBot.coe_injective hC
  simp [formula] at h1
  omega

end C1128
