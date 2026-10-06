import Mathlib

/-!
# Conjecture 00000002478: the q-binomial (Gauss) expansion and its finite-field counting content

* `gaussBinom n k` is the Gaussian binomial `[n choose k]_q` (q-Pascal recursion); it satisfies
  the textbook product formula (`gaussBinom_mul_qDen`).
* **Expansion** (`qBinomial_expansion`): `∏_{i<n} (1 + q^i t) = ∑_{k ≤ n} q^(k(k-1)/2) [n choose k]_q t^k`
  as polynomials in `q` and `t`, and its evaluation in every commutative semiring.
* **Counting content** (`card_subspaces_eq_gaussBinom`, `qBinomial_expansion_count`): over a finite
  field `F` with `q` elements, `[n choose k]_q` is the number of `k`-dimensional subspaces of `F^n`,
  so `∏_{i<n} (1 + q^i t) = ∑_k q^(k(k-1)/2) N_q(n,k) t^k`, and the counts obey q-Pascal.

All of this is classical. The subspace-count core is shared with our package for 00000002490.
-/

open Polynomial Module

universe u

namespace C2478

/-- The Gaussian binomial coefficient `[n choose k]_q` as a polynomial in `q` (natural
coefficients): `[n choose 0] = 1`, `[0 choose k+1] = 0`,
`[n+1 choose k+1] = [n choose k] + q^(k+1) [n choose k+1]`. -/
noncomputable def gaussBinom : ℕ → ℕ → ℕ[X]
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => gaussBinom n k + X ^ (k + 1) * gaussBinom n (k + 1)

@[simp] lemma gaussBinom_zero_right (n : ℕ) : gaussBinom n 0 = 1 := by
  cases n <;> simp [gaussBinom]

@[simp] lemma gaussBinom_zero_succ (k : ℕ) : gaussBinom 0 (k + 1) = 0 := by
  simp [gaussBinom]

lemma gaussBinom_succ_succ (n k : ℕ) :
    gaussBinom (n + 1) (k + 1) = gaussBinom n k + X ^ (k + 1) * gaussBinom n (k + 1) := by
  simp [gaussBinom]

lemma gaussBinom_eq_zero_of_lt : ∀ {n k : ℕ}, n < k → gaussBinom n k = 0
  | _, 0, h => absurd h (Nat.not_lt_zero _)
  | 0, _ + 1, _ => gaussBinom_zero_succ _
  | n + 1, k + 1, h => by
    rw [gaussBinom_succ_succ, gaussBinom_eq_zero_of_lt (by omega : n < k),
      gaussBinom_eq_zero_of_lt (by omega : n < k + 1)]
    simp

/-! ## The q-binomial expansion -/

/-- The q-binomial expansion evaluated at `x` (for `q`) and `t` in any commutative semiring:
`∏_{i<n} (1 + x^i t) = ∑_{k ≤ n} x^(k choose 2) [n choose k]_x t^k`. -/
theorem qBinomial_eval {R : Type*} [CommSemiring R] (x : R) (n : ℕ) : ∀ t : R,
    ∏ i ∈ Finset.range n, (1 + x ^ i * t) =
      ∑ k ∈ Finset.range (n + 1), x ^ k.choose 2 * aeval x (gaussBinom n k) * t ^ k := by
  induction n with
  | zero => intro t; simp
  | succ n ih =>
    intro t
    set f : ℕ → R := fun k => x ^ k.choose 2 * aeval x (gaussBinom n k) * (x * t) ^ k with hf
    have hprod : ∏ i ∈ Finset.range n, (1 + x ^ (i + 1) * t) =
        ∏ i ∈ Finset.range n, (1 + x ^ i * (x * t)) :=
      Finset.prod_congr rfl fun i _ => by ring
    have hlast : f (n + 1) = 0 := by
      simp [hf, gaussBinom_eq_zero_of_lt (Nat.lt_succ_self n)]
    have hS : ∑ k ∈ Finset.range (n + 1), f k = ∑ k ∈ Finset.range (n + 1), f (k + 1) + 1 := by
      have h1 := Finset.sum_range_succ f (n + 1)
      have h2 := Finset.sum_range_succ' f (n + 1)
      rw [hlast, add_zero] at h1
      rw [← h1, h2]
      simp [hf]
    rw [Finset.prod_range_succ', pow_zero, one_mul, hprod, ih (x * t)]
    change (∑ k ∈ Finset.range (n + 1), f k) * (1 + t) = _
    rw [mul_add, mul_one, Finset.sum_mul]
    conv_lhs => rw [hS]
    rw [Finset.sum_range_succ' _ (n + 1), add_assoc, add_comm 1, ← add_assoc,
      ← Finset.sum_add_distrib]
    simp only [Nat.choose_zero_succ, pow_zero, gaussBinom_zero_right, map_one, mul_one]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hf, gaussBinom_succ_succ, map_add, map_mul, map_pow, aeval_X,
      Nat.choose_succ_succ k 1, Nat.choose_one_right]
    ring

/-- **Gauss's q-binomial expansion** (Wikipedia: the "Cauchy binomial theorem") as an identity
of polynomials in two variables `q` (inner variable) and `t` (outer variable):
`∏_{i<n} (1 + q^i t) = ∑_{k=0}^{n} q^(k(k-1)/2) [n choose k]_q t^k` in `ℕ[q][t]`. -/
theorem qBinomial_expansion (n : ℕ) :
    ∏ i ∈ Finset.range n, (1 + C ((X : ℕ[X]) ^ i) * (X : ℕ[X][X])) =
      ∑ k ∈ Finset.range (n + 1), C (X ^ (k * (k - 1) / 2) * gaussBinom n k) * X ^ k := by
  have hC : ∀ p : ℕ[X], @aeval ℕ ℕ[X][X] _ _ Semiring.toNatAlgebra (C X) p = C p := fun p => by
    have : (Semiring.toNatAlgebra : Algebra ℕ ℕ[X][X]) = Polynomial.algebraOfAlgebra := Subsingleton.elim _ _
    rw [this, ← Polynomial.algebraMap_eq, Polynomial.aeval_algebraMap_apply, aeval_X_left_apply]
  rw [Finset.prod_congr rfl fun i _ => by rw [map_pow], qBinomial_eval (C (X : ℕ[X])) n X]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hC, Nat.choose_two_right, map_mul, map_pow]

/-! ## The textbook product formula -/

section prod
variable {R : Type*} [CommRing R] (x : R)

/-- `(1 - x^n)(1 - x^(n-1)) ⋯ (1 - x^(n-k+1))`. -/
def qNum (n k : ℕ) : R := ∏ i ∈ Finset.range k, (1 - x ^ (n - i))

/-- `(1 - x)(1 - x^2) ⋯ (1 - x^k)`. -/
def qDen (k : ℕ) : R := ∏ i ∈ Finset.range k, (1 - x ^ (i + 1))

/-- The textbook product formula `[n choose k]_x (1-x)⋯(1-x^k) = (1-x^n)⋯(1-x^(n-k+1))`, in every
commutative ring (both sides vanish for `k > n`). -/
theorem gaussBinom_mul_qDen (n k : ℕ) : aeval x (gaussBinom n k) * qDen x k = qNum x n k := by
  induction n generalizing k with
  | zero => cases k <;> simp [qDen, qNum]
  | succ n ih =>
    cases k with
    | zero => simp [qDen, qNum]
    | succ k =>
      have hN1 : qNum x (n + 1) (k + 1) = (1 - x ^ (n + 1)) * qNum x n k := by
        unfold qNum; rw [Finset.prod_range_succ', mul_comm]; simp
      have hN2 : qNum x n (k + 1) = qNum x n k * (1 - x ^ (n - k)) := Finset.prod_range_succ _ _
      have hD : qDen x (k + 1) = qDen x k * (1 - x ^ (k + 1)) := Finset.prod_range_succ _ _
      have h1 := ih k
      have h2 := ih (k + 1)
      rw [hD, hN2] at h2
      rw [gaussBinom_succ_succ, hN1, hD]
      simp only [map_add, map_mul, map_pow, aeval_X]
      rcases le_or_gt k n with hk | hk
      · have hp : x ^ (k + 1) * x ^ (n - k) = x ^ (n + 1) := by rw [← pow_add]; congr 1; omega
        linear_combination (1 - x ^ (k + 1)) * h1 + x ^ (k + 1) * h2 - qNum x n k * hp
      · have h0 : qNum x n k = 0 := Finset.prod_eq_zero (Finset.mem_range.2 hk) (by simp)
        rw [h0] at h1 h2
        rw [h0]
        linear_combination (1 - x ^ (k + 1)) * h1 + x ^ (k + 1) * h2

/-- `liProd x n k = ∏_{i<k} (x^n - x^i)`. -/
def liProd (n k : ℕ) : R := ∏ i ∈ Finset.range k, (x ^ n - x ^ i)

lemma liProd_succ_succ (n k : ℕ) :
    liProd x (n + 1) (k + 1) = (x ^ (n + 1) - 1) * x ^ k * liProd x n k := by
  unfold liProd
  rw [Finset.prod_range_succ']
  have h : ∀ i, x ^ (n + 1) - x ^ (i + 1) = x * (x ^ n - x ^ i) := fun i => by ring
  simp only [h, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, pow_zero]
  ring

/-- `[n choose k]_x ∏_{i<k}(x^k - x^i) = ∏_{i<k}(x^n - x^i)` in every commutative ring. -/
theorem gaussBinom_mul_liProd (n k : ℕ) :
    aeval x (gaussBinom n k) * liProd x k k = liProd x n k := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => simp [liProd]
    | succ k => simp [liProd, Finset.prod_range_succ']
  | succ n ih =>
    cases k with
    | zero => simp [liProd]
    | succ k =>
      have h1 := ih k
      have h2 := ih (k + 1)
      rw [liProd_succ_succ x k k, show liProd x n (k + 1) = liProd x n k * (x ^ n - x ^ k) from
        Finset.prod_range_succ _ _] at h2
      rw [gaussBinom_succ_succ, liProd_succ_succ x k k, liProd_succ_succ x n k]
      simp only [map_add, map_mul, map_pow, aeval_X]
      linear_combination ((x ^ (k + 1) - 1) * x ^ k) * h1 + x ^ (k + 1) * h2

end prod

/-! ## Counting content: subspaces of finite vector spaces -/

section count
variable {F V : Type*} [Field F] [Fintype F] [AddCommGroup V] [Module F V] [Finite V]

instance : Finite (Submodule F V) :=
  Finite.of_injective (fun W : Submodule F V => (W : Set V)) SetLike.coe_injective

/-- A linearly independent `k`-tuple spans a `k`-dimensional subspace. -/
noncomputable def spanMap (k : ℕ) :
    {s : Fin k → V // LinearIndependent F s} → {W : Submodule F V // finrank F W = k} :=
  fun s => ⟨Submodule.span F (Set.range s.1), by rw [finrank_span_eq_card s.2, Fintype.card_fin]⟩

/-- The tuples spanning `W` are the linearly independent `k`-tuples of `W`. -/
noncomputable def fibreEquiv {k : ℕ} (W : {W : Submodule F V // finrank F W = k}) :
    {s // spanMap (F := F) k s = W} ≃ {t : Fin k → W.1 // LinearIndependent F t} where
  toFun s := ⟨fun i => ⟨s.1.1 i, by
      rw [← congrArg Subtype.val s.2]; exact Submodule.subset_span ⟨i, rfl⟩⟩, by
      apply LinearIndependent.of_comp W.1.subtype
      exact s.1.2⟩
  invFun t := ⟨⟨fun i => (t.1 i : V), t.2.map' W.1.subtype (Submodule.ker_subtype _)⟩, by
      apply Subtype.ext
      have htop : Submodule.span F (Set.range t.1) = ⊤ :=
        t.2.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, W.2])
      change Submodule.span F (Set.range (W.1.subtype ∘ t.1)) = W.1
      rw [Set.range_comp, Submodule.span_image, htop, Submodule.map_subtype_top]⟩
  left_inv s := by rfl
  right_inv t := by rfl

/-- Double counting: `#{LI k-tuples} = #{k-subspaces} * ∏_{i<k}(q^k - q^i)`. -/
theorem card_li_eq (k : ℕ) :
    Nat.card {s : Fin k → V // LinearIndependent F s} =
      Nat.card {W : Submodule F V // finrank F W = k} *
        ∏ i : Fin k, (Fintype.card F ^ k - Fintype.card F ^ (i : ℕ)) := by
  classical
  have := Fintype.ofFinite {W : Submodule F V // finrank F W = k}
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv (spanMap (F := F) k)), Nat.card_sigma]
  rw [Finset.sum_congr rfl (fun W _ => ((Nat.card_congr (fibreEquiv W)).trans
    (card_linearIndependent (K := F) (V := W.1) (k := k) W.2.ge)).trans
    (show (∏ i : Fin k, (Fintype.card F ^ finrank F W.1 - Fintype.card F ^ (i : ℕ))) =
      ∏ i : Fin k, (Fintype.card F ^ k - Fintype.card F ^ (i : ℕ)) by rw [W.2]))]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]

lemma cast_prod_pow_sub (q m k : ℕ) (hq : 1 ≤ q) (hk : k ≤ m) :
    ((∏ i : Fin k, (q ^ m - q ^ (i : ℕ)) : ℕ) : ℤ) = liProd (q : ℤ) m k := by
  rw [liProd, ← Fin.prod_univ_eq_prod_range, Nat.cast_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Nat.cast_sub (Nat.pow_le_pow_right hq (by omega)), Nat.cast_pow, Nat.cast_pow]

lemma natCast_eval (p : ℕ[X]) (q : ℕ) : ((p.eval q : ℕ) : ℤ) = aeval (q : ℤ) p := by
  rw [← Polynomial.coe_aeval_eq_eval, ← map_natCast (algebraMap ℕ ℤ) q,
    Polynomial.aeval_algebraMap_apply]
  rfl

/-- Over a finite field `F` with `q` elements, the number of `k`-dimensional subspaces of an
`n`-dimensional `F`-vector space is `[n choose k]_q`. -/
theorem card_subspaces_eq_gaussBinom (k : ℕ) :
    Nat.card {W : Submodule F V // finrank F W = k} =
      (gaussBinom (finrank F V) k).eval (Fintype.card F) := by
  have hq : 2 ≤ Fintype.card F := Fintype.one_lt_card
  have key := gaussBinom_mul_liProd (Fintype.card F : ℤ) (finrank F V) k
  rw [← natCast_eval] at key
  have hne : liProd (Fintype.card F : ℤ) k k ≠ 0 := by
    rw [liProd, Finset.prod_ne_zero_iff]
    intro i hi
    have : (Fintype.card F : ℤ) ^ i < (Fintype.card F : ℤ) ^ k :=
      pow_lt_pow_right₀ (by exact_mod_cast hq) (Finset.mem_range.1 hi)
    omega
  apply Nat.cast_injective (R := ℤ)
  apply mul_right_cancel₀ hne
  rw [key]
  rcases le_or_gt k (finrank F V) with hk | hk
  · rw [← cast_prod_pow_sub _ _ _ (by omega) le_rfl, ← Nat.cast_mul, ← card_li_eq k,
      card_linearIndependent hk, cast_prod_pow_sub _ _ _ (by omega) hk]
  · have h0 : Nat.card {W : Submodule F V // finrank F W = k} = 0 := by
      rw [Nat.card_eq_zero]
      left
      exact ⟨fun W => by have := Submodule.finrank_le W.1; omega⟩
    rw [h0, Nat.cast_zero, zero_mul, liProd]
    exact (Finset.prod_eq_zero (Finset.mem_range.2 hk) (sub_self _)).symm

end count

section coord
variable (F : Type*) [Field F] [Fintype F]

/-- `N_q(n,k)`: the number of `k`-dimensional subspaces of `F^n = Fin n → F`. -/
noncomputable def subCount (n k : ℕ) : ℕ :=
  Nat.card {W : Submodule F (Fin n → F) // finrank F W = k}

theorem subCount_eq (n k : ℕ) : subCount F n k = (gaussBinom n k).eval (Fintype.card F) := by
  rw [subCount, card_subspaces_eq_gaussBinom, Module.finrank_fin_fun]

/-- q-Pascal for the counts: `N(n+1,k+1) = N(n,k) + q^(k+1) N(n,k+1)`. -/
theorem subCount_pascal (n k : ℕ) :
    subCount F (n + 1) (k + 1) =
      subCount F n k + Fintype.card F ^ (k + 1) * subCount F n (k + 1) := by
  simp only [subCount_eq, gaussBinom_succ_succ, eval_add, eval_mul, eval_pow, eval_X]

/-- **Counting form of the expansion.** With `q = |F|`, as polynomials in `t`:
`∏_{i<n} (1 + q^i t) = ∑_{k=0}^{n} q^(k(k-1)/2) N_q(n,k) t^k`. -/
theorem qBinomial_expansion_count (n : ℕ) :
    ∏ i ∈ Finset.range n, (1 + C (Fintype.card F ^ i) * (X : ℕ[X])) =
      ∑ k ∈ Finset.range (n + 1),
        C (Fintype.card F ^ (k * (k - 1) / 2) * subCount F n k) * X ^ k := by
  have hC : ∀ p : ℕ[X], @aeval ℕ ℕ[X] _ _ Semiring.toNatAlgebra (C (Fintype.card F)) p =
      C (p.eval (Fintype.card F)) := fun p => by
    have : (Semiring.toNatAlgebra : Algebra ℕ ℕ[X]) = Polynomial.algebraOfAlgebra := Subsingleton.elim _ _
    rw [this, ← Polynomial.algebraMap_eq, Polynomial.aeval_algebraMap_apply,
      Polynomial.coe_aeval_eq_eval]
  rw [Finset.prod_congr rfl fun i _ => by rw [map_pow],
    qBinomial_eval (C (Fintype.card F : ℕ)) n (X : ℕ[X])]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hC, ← subCount_eq, Nat.choose_two_right, map_mul, map_pow]

end coord

/-- **Conjecture 00000002478 (classical theorems).** (1) Gauss's q-binomial expansion
`∏_{i<n}(1 + q^i t) = ∑_k q^(k(k-1)/2) [n choose k]_q t^k` holds in `ℕ[q][t]`; and for every
finite field `F` with `q` elements: (2) `[n choose k]_q` counts the `k`-dimensional subspaces of
`F^n`; (3) hence the expansion holds with the subspace counts as coefficients; (4) the counts obey
the q-Pascal recursion. -/
theorem conjecture_2478 :
    (∀ n : ℕ, ∏ i ∈ Finset.range n, (1 + C ((X : ℕ[X]) ^ i) * (X : ℕ[X][X])) =
      ∑ k ∈ Finset.range (n + 1), C (X ^ (k * (k - 1) / 2) * gaussBinom n k) * X ^ k) ∧
    ∀ (F : Type u) [Field F] [Fintype F],
      (∀ n k : ℕ, Nat.card {W : Submodule F (Fin n → F) // finrank F W = k} =
        (gaussBinom n k).eval (Fintype.card F)) ∧
      (∀ n : ℕ, ∏ i ∈ Finset.range n, (1 + C (Fintype.card F ^ i) * (X : ℕ[X])) =
        ∑ k ∈ Finset.range (n + 1),
          C (Fintype.card F ^ (k * (k - 1) / 2) * subCount F n k) * X ^ k) ∧
      (∀ n k : ℕ, subCount F (n + 1) (k + 1) =
        subCount F n k + Fintype.card F ^ (k + 1) * subCount F n (k + 1)) :=
  ⟨qBinomial_expansion, fun F _ _ =>
    ⟨subCount_eq F, qBinomial_expansion_count F, subCount_pascal F⟩⟩

end C2478
