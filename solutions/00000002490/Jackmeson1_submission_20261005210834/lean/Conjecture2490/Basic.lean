import Mathlib

/-!
# Conjecture 00000002490: subspace counts over finite fields are Gaussian binomials

For every finite field `F` with `q` elements, every finite (equivalently, finite-dimensional)
`F`-vector space `V` of dimension `n`, and every `k`, the number of `k`-dimensional subspaces of `V` equals the
Gaussian binomial coefficient `[n choose k]_q` evaluated at `q = |F|`.

This is a classical theorem; the proof is the standard double count of ordered linearly
independent `k`-tuples, using Mathlib's `card_linearIndependent`.
-/

open Polynomial Module

universe u

namespace C2490

/-! ## The Gaussian binomial coefficient -/

/-- The Gaussian binomial coefficient `[n choose k]_q`, as a polynomial in `q` with natural
coefficients, defined by `[n choose 0] = 1`, `[0 choose k+1] = 0` and the q-Pascal rule
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

/-- `liProd x n k = ∏_{i<k} (x^n - x^i)`. At `x = q` and `k ≤ n` this is the number of ordered
linearly independent `k`-tuples in an `n`-dimensional space over `F_q` (Mathlib's
`card_linearIndependent`). -/
def liProd {R : Type*} [CommRing R] (x : R) (n k : ℕ) : R :=
  ∏ i ∈ Finset.range k, (x ^ n - x ^ i)

section liProd
variable {R : Type*} [CommRing R] (x : R)

lemma liProd_zero_right (n : ℕ) : liProd x n 0 = 1 := by simp [liProd]

lemma liProd_succ_right (n k : ℕ) : liProd x n (k + 1) = liProd x n k * (x ^ n - x ^ k) :=
  Finset.prod_range_succ _ _

lemma liProd_zero_succ (k : ℕ) : liProd x 0 (k + 1) = 0 :=
  Finset.prod_eq_zero (i := 0) (by simp) (by simp)

lemma liProd_succ_succ (n k : ℕ) :
    liProd x (n + 1) (k + 1) = (x ^ (n + 1) - 1) * x ^ k * liProd x n k := by
  unfold liProd
  rw [Finset.prod_range_succ']
  have h : ∀ i, x ^ (n + 1) - x ^ (i + 1) = x * (x ^ n - x ^ i) := fun i => by ring
  simp only [h, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, pow_zero]
  ring

/-- Key algebraic identity: `[n choose k]_x * ∏_{i<k}(x^k - x^i) = ∏_{i<k}(x^n - x^i)` in every
commutative ring. -/
theorem gaussBinom_mul_liProd (n k : ℕ) :
    aeval x (gaussBinom n k) * liProd x k k = liProd x n k := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => simp [liProd_zero_right]
    | succ k => simp [liProd_zero_succ]
  | succ n ih =>
    cases k with
    | zero => simp [liProd_zero_right]
    | succ k =>
      have h1 := ih k
      have h2 := ih (k + 1)
      rw [liProd_succ_succ x k k, liProd_succ_right x n k] at h2
      rw [gaussBinom_succ_succ, liProd_succ_succ x k k, liProd_succ_succ x n k]
      simp only [map_add, map_mul, map_pow, aeval_X]
      linear_combination ((x ^ (k + 1) - 1) * x ^ k) * h1 + x ^ (k + 1) * h2

/-- Numerator `(1 - x^n)(1 - x^(n-1)) ⋯ (1 - x^(n-k+1))` of the textbook product formula. -/
def qNum (n k : ℕ) : R := ∏ i ∈ Finset.range k, (1 - x ^ (n - i))

/-- Denominator `(1 - x)(1 - x^2) ⋯ (1 - x^k)` of the textbook product formula. -/
def qDen (k : ℕ) : R := ∏ i ∈ Finset.range k, (1 - x ^ (i + 1))

lemma qNum_succ_succ (n k : ℕ) : qNum x (n + 1) (k + 1) = (1 - x ^ (n + 1)) * qNum x n k := by
  unfold qNum; rw [Finset.prod_range_succ', mul_comm]; simp

lemma qNum_succ_right (n k : ℕ) : qNum x n (k + 1) = qNum x n k * (1 - x ^ (n - k)) :=
  Finset.prod_range_succ _ _

lemma qDen_succ (k : ℕ) : qDen x (k + 1) = qDen x k * (1 - x ^ (k + 1)) := Finset.prod_range_succ _ _

/-- The textbook product formula: `[n choose k]_x * (1-x)⋯(1-x^k) = (1-x^n)⋯(1-x^(n-k+1))`,
in every commutative ring (for `k > n` both sides vanish). -/
theorem gaussBinom_mul_qDen (n k : ℕ) : aeval x (gaussBinom n k) * qDen x k = qNum x n k := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => simp [qDen, qNum]
    | succ k => simp [qNum]
  | succ n ih =>
    cases k with
    | zero => simp [qDen, qNum]
    | succ k =>
      have h1 := ih k
      have h2 := ih (k + 1)
      rw [qDen_succ, qNum_succ_right] at h2
      rw [gaussBinom_succ_succ, qNum_succ_succ, qDen_succ]
      simp only [map_add, map_mul, map_pow, aeval_X]
      rcases le_or_gt k n with hk | hk
      · have hp : x ^ (k + 1) * x ^ (n - k) = x ^ (n + 1) := by rw [← pow_add]; congr 1; omega
        linear_combination (1 - x ^ (k + 1)) * h1 + x ^ (k + 1) * h2 - qNum x n k * hp
      · have h0 : qNum x n k = 0 :=
          Finset.prod_eq_zero (Finset.mem_range.2 hk) (by simp)
        rw [h0] at h1 h2
        rw [h0]
        linear_combination (1 - x ^ (k + 1)) * h1 + x ^ (k + 1) * h2

/-- The second q-Pascal rule `[n+1 choose k+1] = [n choose k+1] + x^(n-k) [n choose k]`
(`k ≤ n`), in every integral domain where `(1-x)⋯(1-x^(k+1)) ≠ 0`. -/
theorem gaussBinom_pascal' [IsDomain R] (n k : ℕ) (hk : k ≤ n) (hD : qDen x (k + 1) ≠ 0) :
    aeval x (gaussBinom (n + 1) (k + 1)) =
      aeval x (gaussBinom n (k + 1)) + x ^ (n - k) * aeval x (gaussBinom n k) := by
  apply mul_right_cancel₀ hD
  have e1 := gaussBinom_mul_qDen x (n + 1) (k + 1)
  have e2 := gaussBinom_mul_qDen x n (k + 1)
  have e3 := gaussBinom_mul_qDen x n k
  have hp : x ^ (n - k) * x ^ (k + 1) = x ^ (n + 1) := by rw [← pow_add]; congr 1; omega
  rw [qNum_succ_succ] at e1
  rw [qNum_succ_right] at e2
  rw [qDen_succ] at e1 e2 ⊢
  linear_combination e1 - e2 - x ^ (n - k) * (1 - x ^ (k + 1)) * e3 + qNum x n k * hp

end liProd

/-- In `ℤ[X]` the denominator `(1-X)⋯(1-X^k)` is nonzero (its value at `0` is `1`), so the
product formula determines `[n choose k]_X` as the quotient of the two products. -/
theorem qDen_X_ne_zero (k : ℕ) : qDen (X : ℤ[X]) k ≠ 0 := by
  intro h
  have := congrArg (Polynomial.eval 0) h
  simp [qDen, Polynomial.eval_prod] at this

/-! ## Counting subspaces -/

section count
variable {F V : Type*} [Field F] [Fintype F] [AddCommGroup V] [Module F V] [Finite V]

instance : Finite (Submodule F V) :=
  Finite.of_injective (fun W : Submodule F V => (W : Set V)) SetLike.coe_injective

/-- An ordered linearly independent `k`-tuple spans a `k`-dimensional subspace. -/
noncomputable def spanMap (k : ℕ) :
    {s : Fin k → V // LinearIndependent F s} → {W : Submodule F V // finrank F W = k} :=
  fun s => ⟨Submodule.span F (Set.range s.1), by rw [finrank_span_eq_card s.2, Fintype.card_fin]⟩

/-- The tuples spanning a fixed `k`-dimensional `W` are exactly the linearly independent
`k`-tuples of `W`. -/
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

/-- Double counting: `#LI k-tuples = #(k-subspaces) * ∏_{i<k}(q^k - q^i)`. -/
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

/-- Casting the `ℕ` product `∏_{i<k}(q^m - q^i)` (`k ≤ m`) to `ℤ`. -/
lemma cast_prod_pow_sub (q m k : ℕ) (hq : 1 ≤ q) (hk : k ≤ m) :
    ((∏ i : Fin k, (q ^ m - q ^ (i : ℕ)) : ℕ) : ℤ) = liProd (q : ℤ) m k := by
  rw [liProd, ← Fin.prod_univ_eq_prod_range, Nat.cast_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Nat.cast_sub (Nat.pow_le_pow_right hq (by omega)), Nat.cast_pow, Nat.cast_pow]

lemma liProd_self_ne_zero (q k : ℕ) (hq : 2 ≤ q) : liProd (q : ℤ) k k ≠ 0 := by
  rw [liProd, Finset.prod_ne_zero_iff]
  intro i hi
  rw [Finset.mem_range] at hi
  have : (q : ℤ) ^ i < (q : ℤ) ^ k := pow_lt_pow_right₀ (by exact_mod_cast hq) hi
  omega

lemma natCast_eval (p : ℕ[X]) (q : ℕ) : ((p.eval q : ℕ) : ℤ) = aeval (q : ℤ) p := by
  rw [← Polynomial.coe_aeval_eq_eval, ← map_natCast (algebraMap ℕ ℤ) q,
    Polynomial.aeval_algebraMap_apply]
  rfl

/-- **Main theorem.** Over a finite field `F` with `q` elements, the number of `k`-dimensional
subspaces of an `n`-dimensional `F`-vector space is the Gaussian binomial `[n choose k]_q`. -/
theorem card_subspaces_eq_gaussBinom (k : ℕ) :
    Nat.card {W : Submodule F V // finrank F W = k} =
      (gaussBinom (finrank F V) k).eval (Fintype.card F) := by
  have hq : 2 ≤ Fintype.card F := Fintype.one_lt_card
  have key := gaussBinom_mul_liProd (Fintype.card F : ℤ) (finrank F V) k
  rw [← natCast_eval] at key
  apply Nat.cast_injective (R := ℤ)
  apply mul_right_cancel₀ (liProd_self_ne_zero _ k hq)
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

/-! ## Intervals of the subspace lattice -/

omit [Fintype F] in
lemma finrank_comap_mkQ (U : Submodule F V) (W' : Submodule F (V ⧸ U)) :
    finrank F (W'.comap U.mkQ) = finrank F W' + finrank F U := by
  have hUW : U ≤ W'.comap U.mkQ := Submodule.le_comap_mkQ U W'
  have h := LinearMap.finrank_range_add_finrank_ker (U.mkQ.domRestrict (W'.comap U.mkQ))
  rw [LinearMap.range_domRestrict,
    Submodule.map_comap_eq_of_surjective (Submodule.mkQ_surjective U),
    LinearMap.ker_domRestrict, Submodule.ker_mkQ] at h
  rw [← h, (Submodule.comapSubtypeEquivOfLe hUW).finrank_eq]

/-- Subspaces of `V ⧸ U` of dimension `k - dim U` ↔ subspaces of `V` of dimension `k`
containing `U`. -/
noncomputable def aboveEquiv (U : Submodule F V) (k : ℕ) (hk : finrank F U ≤ k) :
    {W' : Submodule F (V ⧸ U) // finrank F W' = k - finrank F U} ≃
      {W : Submodule F V // U ≤ W ∧ finrank F W = k} where
  toFun W' := ⟨W'.1.comap U.mkQ, Submodule.le_comap_mkQ U _, by
    rw [finrank_comap_mkQ, W'.2]; omega⟩
  invFun W := ⟨W.1.map U.mkQ, by
    have := finrank_comap_mkQ U (W.1.map U.mkQ)
    rw [Submodule.comap_map_mkQ, sup_eq_right.2 W.2.1, W.2.2] at this
    omega⟩
  left_inv W' := Subtype.ext (Submodule.map_comap_eq_of_surjective (Submodule.mkQ_surjective U) _)
  right_inv W := Subtype.ext (by simp only [Submodule.comap_map_mkQ, sup_eq_right.2 W.2.1])

/-- Upper intervals: the `k`-dimensional subspaces containing a fixed subspace `U` (with
`dim U ≤ k`) are counted by `[n - dim U choose k - dim U]_q`. -/
theorem card_subspaces_above (U : Submodule F V) (k : ℕ) (hk : finrank F U ≤ k) :
    Nat.card {W : Submodule F V // U ≤ W ∧ finrank F W = k} =
      (gaussBinom (finrank F V - finrank F U) (k - finrank F U)).eval (Fintype.card F) := by
  have : Finite (V ⧸ U) := Finite.of_surjective U.mkQ (Submodule.mkQ_surjective U)
  rw [← Submodule.finrank_quotient, ← card_subspaces_eq_gaussBinom]
  exact (Nat.card_congr (aboveEquiv U k hk)).symm

/-- Subspaces `W` of `V` with `U ≤ W ≤ T` ↔ subspaces of `T` containing `U` (viewed in `T`). -/
noncomputable def intervalEquiv (U T : Submodule F V) (hUT : U ≤ T) (k : ℕ) :
    {W : Submodule F V // (U ≤ W ∧ W ≤ T) ∧ finrank F W = k} ≃
      {W₁ : Submodule F T // U.comap T.subtype ≤ W₁ ∧ finrank F W₁ = k} where
  toFun W := ⟨W.1.comap T.subtype, Submodule.comap_mono W.2.1.1, by
    rw [(Submodule.comapSubtypeEquivOfLe W.2.1.2).finrank_eq, W.2.2]⟩
  invFun W₁ := ⟨W₁.1.map T.subtype, ⟨by
      calc U = (U.comap T.subtype).map T.subtype := by
            rw [Submodule.map_comap_subtype, inf_eq_right.2 hUT]
        _ ≤ W₁.1.map T.subtype := Submodule.map_mono W₁.2.1,
      Submodule.map_subtype_le _ _⟩, by
    rw [← (Submodule.equivMapOfInjective _ T.injective_subtype W₁.1).finrank_eq, W₁.2.2]⟩
  left_inv W := Subtype.ext (by
    simp only [Submodule.map_comap_subtype, inf_eq_right.2 W.2.1.2])
  right_inv W₁ := Subtype.ext (Submodule.comap_map_eq_of_injective T.injective_subtype _)

/-- **Interval closure.** For subspaces `U ≤ T` of `V` and `dim U ≤ k`, the number of
`k`-dimensional subspaces `W` with `U ≤ W ≤ T` is `[dim T - dim U choose k - dim U]_q`.
(`U = ⊥`, `T = ⊤` recovers the main theorem.) -/
theorem card_subspaces_interval (U T : Submodule F V) (hUT : U ≤ T) (k : ℕ)
    (hk : finrank F U ≤ k) :
    Nat.card {W : Submodule F V // (U ≤ W ∧ W ≤ T) ∧ finrank F W = k} =
      (gaussBinom (finrank F T - finrank F U) (k - finrank F U)).eval (Fintype.card F) := by
  have hU : finrank F (U.comap T.subtype) = finrank F U :=
    (Submodule.comapSubtypeEquivOfLe hUT).finrank_eq
  rw [Nat.card_congr (intervalEquiv U T hUT k),
    card_subspaces_above (U.comap T.subtype) k (by rwa [hU]), hU]

end count

/-! ## The coordinate space `F^n` -/

section coord
variable (F : Type*) [Field F] [Fintype F]

/-- The number of `k`-dimensional subspaces of `F^n = Fin n → F`. -/
noncomputable def subCount (n k : ℕ) : ℕ :=
  Nat.card {W : Submodule F (Fin n → F) // finrank F W = k}

/-- The number of `k`-dimensional subspaces of `F^n` is `[n choose k]_q`, `q = |F|`. -/
theorem subCount_eq (n k : ℕ) : subCount F n k = (gaussBinom n k).eval (Fintype.card F) := by
  rw [subCount, card_subspaces_eq_gaussBinom, Module.finrank_fin_fun]

/-- First q-Pascal rule for the counts: `N(n+1,k+1) = N(n,k) + q^(k+1) N(n,k+1)`. -/
theorem subCount_pascal (n k : ℕ) :
    subCount F (n + 1) (k + 1) =
      subCount F n k + Fintype.card F ^ (k + 1) * subCount F n (k + 1) := by
  simp only [subCount_eq, gaussBinom_succ_succ, eval_add, eval_mul, eval_pow, eval_X]

/-- Second q-Pascal rule for the counts: `N(n+1,k+1) = N(n,k+1) + q^(n-k) N(n,k)`, `k ≤ n`. -/
theorem subCount_pascal' (n k : ℕ) (hk : k ≤ n) :
    subCount F (n + 1) (k + 1) =
      subCount F n (k + 1) + Fintype.card F ^ (n - k) * subCount F n k := by
  apply Nat.cast_injective (R := ℤ)
  have hq : 2 ≤ Fintype.card F := Fintype.one_lt_card
  have hD : qDen (Fintype.card F : ℤ) (k + 1) ≠ 0 := by
    rw [qDen, Finset.prod_ne_zero_iff]
    intro i _ h
    have : (2 : ℤ) ≤ (Fintype.card F : ℤ) ^ (i + 1) :=
      calc (2 : ℤ) ≤ Fintype.card F := by exact_mod_cast hq
        _ ≤ _ := le_self_pow₀ (by exact_mod_cast (by omega : 1 ≤ Fintype.card F)) (by omega)
    linarith
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, subCount_eq, natCast_eval]
  exact gaussBinom_pascal' _ n k hk hD

/-- Textbook product formula for the counts:
`N(n,k) (1-q)(1-q^2)⋯(1-q^k) = (1-q^n)(1-q^(n-1))⋯(1-q^(n-k+1))`. -/
theorem subCount_product_formula (n k : ℕ) :
    (subCount F n k : ℤ) * qDen (Fintype.card F : ℤ) k = qNum (Fintype.card F : ℤ) n k := by
  rw [subCount_eq, natCast_eval, gaussBinom_mul_qDen]

end coord

/-- Sanity check: `F_2^4` has `[4 choose 2]_2 = 35` two-dimensional subspaces. -/
example : subCount (ZMod 2) 4 2 = 35 := by
  rw [subCount_eq, ZMod.card]
  simp [gaussBinom]

/-- **Conjecture 00000002490 (classical theorem).** For every finite field `F` with `q`
elements: (1) for all `n, k` the number of `k`-dimensional subspaces of `F^n` is the Gaussian
binomial `[n choose k]_q`; (2), (3) these counts satisfy both q-Pascal recursions; (4) in every
finite `F`-vector space `V`, for subspaces `U ≤ T` and `dim U ≤ k`, the number of
`k`-dimensional `W` with `U ≤ W ≤ T` is `[dim T - dim U choose k - dim U]_q`. -/
theorem conjecture_2490 (F : Type*) [Field F] [Fintype F] :
    (∀ n k : ℕ, Nat.card {W : Submodule F (Fin n → F) // finrank F W = k} =
        (gaussBinom n k).eval (Fintype.card F)) ∧
    (∀ n k : ℕ, subCount F (n + 1) (k + 1) =
        subCount F n k + Fintype.card F ^ (k + 1) * subCount F n (k + 1)) ∧
    (∀ n k : ℕ, k ≤ n → subCount F (n + 1) (k + 1) =
        subCount F n (k + 1) + Fintype.card F ^ (n - k) * subCount F n k) ∧
    (∀ (V : Type u) [AddCommGroup V] [Module F V] [Finite V] (U T : Submodule F V) (k : ℕ),
      U ≤ T → finrank F U ≤ k →
      Nat.card {W : Submodule F V // (U ≤ W ∧ W ≤ T) ∧ finrank F W = k} =
        (gaussBinom (finrank F T - finrank F U) (k - finrank F U)).eval (Fintype.card F)) :=
  ⟨subCount_eq F, subCount_pascal F, subCount_pascal' F,
    fun _ _ _ _ U T k hUT hk => card_subspaces_interval U T hUT k hk⟩

end C2490
