import Mathlib

/-!
# Conjecture 00000000037: large Sidon sets of primes

"Among the primes there exists a Sidon set of size `(N / log N)^(1/2 - o(1))`."

Reading formalized here: there is a family `A N` of Sidon sets with every element of `A N` a prime
`≤ N`, such that `log |A N| / log (N / log N) → 1/2`, i.e. for every `ε > 0` and every
sufficiently large `N`,
`(N / log N)^(1/2 - ε) ≤ |A N| ≤ (N / log N)^(1/2 + ε)`.
The upper half holds for *every* Sidon set of naturals `≤ N` (`sidon_upper`), so the exponent
`1/2` is optimal.

Proof: the Erdős–Turán Sidon set `{2pk + (k² mod p) : k < p}` (with `p` a Bertrand prime, `p ≈ √(π(N/2))/4`),
translated by a shift `b ≤ N/2` chosen by averaging, contains `≫ p·π(N/2)/N` primes;
Chebyshev's lower bound `Chebyshev.pi_ge` finishes.
-/

open Finset Real Filter Asymptotics
open scoped Nat.Prime

namespace C37

/-- A finite set `A` of natural numbers is a *Sidon set* if `a + b = c + d` with
`a, b, c, d ∈ A` forces `{a, b} = {c, d}` (as multisets). -/
def IsSidon (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A, a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- The Erdős–Turán map `k ↦ 2pk + (k² mod p)`. -/
def et (p k : ℕ) : ℕ := 2 * p * k + k ^ 2 % p

lemma et_lt {p k : ℕ} (hp : 0 < p) (hk : k < p) : et p k < 2 * p ^ 2 := by
  unfold et
  have h1 : k ^ 2 % p < p := Nat.mod_lt _ hp
  have h2 : 2 * p * k + p ≤ 2 * p ^ 2 := by nlinarith
  omega

lemma zmod_key {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {a b c d : ZMod p}
    (h1 : a + b = c + d) (h2 : a ^ 2 + b ^ 2 = c ^ 2 + d ^ 2) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have hb : b = c + d - a := by linear_combination h1
  subst hb
  have h3 : 2 * ((a - c) * (a - d)) = 0 := by linear_combination h2
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd two_pos h'
    have := (Fact.out : p.Prime).two_le
    omega
  rcases mul_eq_zero.1 ((mul_eq_zero.1 h3).resolve_left h2ne) with h | h
  · left; exact ⟨by linear_combination h, by linear_combination -h⟩
  · right; exact ⟨by linear_combination h, by linear_combination -h⟩

/-- Erdős–Turán: for an odd prime `p`, the values `et p k` (`k < p`) have distinct pairwise sums. -/
lemma et_sidon {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {k₁ k₂ k₃ k₄ : ℕ}
    (h₁ : k₁ < p) (h₂ : k₂ < p) (h₃ : k₃ < p) (h₄ : k₄ < p)
    (h : et p k₁ + et p k₂ = et p k₃ + et p k₄) :
    (k₁ = k₃ ∧ k₂ = k₄) ∨ (k₁ = k₄ ∧ k₂ = k₃) := by
  have := Fact.mk hp
  have hp0 := hp.pos
  have := Nat.mod_lt (k₁ ^ 2) hp0; have := Nat.mod_lt (k₂ ^ 2) hp0
  have := Nat.mod_lt (k₃ ^ 2) hp0; have := Nat.mod_lt (k₄ ^ 2) hp0
  have e1 : et p k₁ + et p k₂ = (k₁ ^ 2 % p + k₂ ^ 2 % p) + 2 * p * (k₁ + k₂) := by
    unfold et; ring
  have e2 : et p k₃ + et p k₄ = (k₃ ^ 2 % p + k₄ ^ 2 % p) + 2 * p * (k₃ + k₄) := by
    unfold et; ring
  have hs : k₁ + k₂ = k₃ + k₄ := by
    have := congrArg (· / (2 * p)) h
    simp only [e1, e2] at this
    rwa [Nat.add_mul_div_left _ _ (by omega), Nat.add_mul_div_left _ _ (by omega),
      Nat.div_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega), zero_add, zero_add] at this
  have hr : k₁ ^ 2 % p + k₂ ^ 2 % p = k₃ ^ 2 % p + k₄ ^ 2 % p := by
    rw [e1, e2, hs] at h; exact Nat.add_right_cancel h
  have hz1 : (k₁ : ZMod p) + k₂ = k₃ + k₄ := by exact_mod_cast congrArg (Nat.cast : ℕ → ZMod p) hs
  have hz2 : (k₁ : ZMod p) ^ 2 + (k₂ : ZMod p) ^ 2 = (k₃ : ZMod p) ^ 2 + (k₄ : ZMod p) ^ 2 := by
    have := congrArg (Nat.cast : ℕ → ZMod p) hr
    push_cast [ZMod.natCast_mod] at this
    exact this
  have inj : ∀ {x y : ℕ}, x < p → y < p → (x : ZMod p) = y → x = y := by
    intro x y hx hy hxy
    rw [ZMod.natCast_eq_natCast_iff'] at hxy
    rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at hxy
  rcases zmod_key hp2 hz1 hz2 with ⟨a, b⟩ | ⟨a, b⟩
  · left; exact ⟨inj h₁ h₃ a, inj h₂ h₄ b⟩
  · right; exact ⟨inj h₁ h₄ a, inj h₂ h₃ b⟩

/-- Indices `k < p` whose shifted Erdős–Turán element `et p k + b` is prime. -/
def goodIdx (p b : ℕ) : Finset ℕ := (range p).filter (fun k => (et p k + b).Prime)

/-- The primes in the translate `b + {et p k : k < p}`. -/
def T (p b : ℕ) : Finset ℕ := (goodIdx p b).image (fun k => et p k + b)

lemma T_sidon {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (b : ℕ) : IsSidon (T p b) := by
  intro a ha c hc d hd e he h
  simp only [T, goodIdx, mem_image, mem_filter, mem_range] at ha hc hd he
  obtain ⟨k₁, ⟨h₁, -⟩, rfl⟩ := ha
  obtain ⟨k₂, ⟨h₂, -⟩, rfl⟩ := hc
  obtain ⟨k₃, ⟨h₃, -⟩, rfl⟩ := hd
  obtain ⟨k₄, ⟨h₄, -⟩, rfl⟩ := he
  rcases et_sidon hp hp2 h₁ h₂ h₃ h₄ (by omega) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · left; exact ⟨rfl, rfl⟩
  · right; exact ⟨rfl, rfl⟩

lemma T_card {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (b : ℕ) : (T p b).card = (goodIdx p b).card := by
  refine card_image_of_injOn fun x hx y hy hxy => ?_
  simp only [goodIdx, coe_filter, mem_range, Set.mem_ofPred_eq] at hx hy
  have hxy : et p x + b = et p y + b := hxy
  rcases et_sidon hp hp2 hx.1 hx.1 hy.1 hy.1 (by omega) with ⟨h, -⟩ | ⟨h, -⟩ <;> exact h

lemma T_mem {p b a : ℕ} (hp : 0 < p) (ha : a ∈ T p b) : a.Prime ∧ a < 2 * p ^ 2 + b := by
  simp only [T, goodIdx, mem_image, mem_filter, mem_range] at ha
  obtain ⟨k, ⟨hk, hpr⟩, rfl⟩ := ha
  exact ⟨hpr, by have := et_lt hp hk; omega⟩

/-- Averaging over the shifts `b ≤ L`: some translate captures its share of the primes. -/
lemma exists_shift {p : ℕ} (hp : 0 < p) (L : ℕ) :
    ∃ b ≤ L, p * (π L - 2 * p ^ 2) ≤ (L + 1) * (goodIdx p b).card := by
  set K := 2 * p ^ 2
  have hP : π L - K ≤ ((Ico K (L + 1)).filter Nat.Prime).card := by
    have hpi : π L = ((range (L + 1)).filter Nat.Prime).card := by
      rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
    have hsub : (range (L + 1)).filter Nat.Prime ⊆ range K ∪ (Ico K (L + 1)).filter Nat.Prime := by
      intro q hq
      simp only [mem_filter, mem_range, mem_union, mem_Ico] at hq ⊢
      by_cases hqK : q < K
      · exact Or.inl hqK
      · exact Or.inr ⟨⟨by omega, hq.1⟩, hq.2⟩
    have h1 := card_le_card hsub
    have h2 := card_union_le (range K) ((Ico K (L + 1)).filter Nat.Prime)
    rw [card_range] at h2
    omega
  have hk : ∀ k ∈ range p, ((Ico K (L + 1)).filter Nat.Prime).card ≤
      ((range (L + 1)).filter (fun b => (et p k + b).Prime)).card := by
    intro k hk
    have hlt := et_lt hp (mem_range.1 hk)
    refine card_le_card_of_injOn (fun q => q - et p k) ?_ ?_
    · intro q hq
      simp only [coe_filter, mem_Ico, Set.mem_ofPred_eq, mem_range] at hq ⊢
      refine ⟨by omega, ?_⟩
      rw [Nat.add_sub_cancel' (by omega)]; exact hq.2
    · intro x hx y hy hxy
      simp only [coe_filter, mem_Ico, Set.mem_ofPred_eq] at hx hy hxy
      omega
  have hsum : ∑ b ∈ range (L + 1), (goodIdx p b).card =
      ∑ k ∈ range p, ((range (L + 1)).filter (fun b => (et p k + b).Prime)).card := by
    simp only [goodIdx, card_filter]; exact sum_comm
  have hge : p * (π L - K) ≤ ∑ b ∈ range (L + 1), (goodIdx p b).card := by
    rw [hsum]
    calc p * (π L - K) ≤ ∑ _k ∈ range p, ((Ico K (L + 1)).filter Nat.Prime).card := by
          rw [sum_const, card_range, smul_eq_mul]; exact Nat.mul_le_mul_left _ hP
      _ ≤ _ := sum_le_sum hk
  obtain ⟨b, hb, hb'⟩ := exists_le_of_sum_le (s := range (L + 1)) nonempty_range_add_one
    (f := fun _ => p * (π L - K)) (g := fun b => (L + 1) * (goodIdx p b).card)
    (by rw [sum_const, card_range, smul_eq_mul, ← mul_sum]; exact Nat.mul_le_mul_left _ hge)
  exact ⟨b, by simpa [Nat.lt_succ_iff] using hb, hb'⟩

lemma primeCounting_le_succ (L : ℕ) : π L ≤ L + 1 := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  exact (card_filter_le _ _).trans (card_range _).le

/-- The finite construction: if `π(N/2) ≥ 64`, a translate of an Erdős–Turán set gives a Sidon set
of primes `≤ N` with `π(N/2)^3 < 64 N^2 |A|^2`. -/
lemma construct (N : ℕ) (hN : 64 ≤ π (N / 2)) :
    ∃ A : Finset ℕ, (∀ a ∈ A, a.Prime ∧ a ≤ N) ∧ IsSidon A ∧
      (π (N / 2)) ^ 3 < 64 * N ^ 2 * A.card ^ 2 := by
  set L := N / 2 with hL
  set x := π L with hx
  have hxL : x ≤ L + 1 := primeCounting_le_succ L
  set m := Nat.sqrt (x / 16)
  have hm1 : m ^ 2 ≤ x / 16 := Nat.sqrt_le' _
  have hm2 : x / 16 < (m + 1) ^ 2 := Nat.lt_succ_sqrt' _
  have hm0 : 2 ≤ m := Nat.le_sqrt'.2 (by omega)
  obtain ⟨p, hp, hmp, hpm⟩ := Nat.exists_prime_lt_and_le_two_mul m (by omega)
  have hp2 : p ≠ 2 := by omega
  have hP1 : 4 * p ^ 2 ≤ x := by
    have h1 : p ^ 2 ≤ (2 * m) ^ 2 := Nat.pow_le_pow_left hpm 2
    have h2 : (2 * m) ^ 2 = 4 * m ^ 2 := by ring
    omega
  have hP2 : x < 16 * p ^ 2 := by
    have : (m + 1) ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hmp 2
    omega
  obtain ⟨b, hbL, hb⟩ := exists_shift hp.pos L
  refine ⟨T p b, fun a ha => ?_, T_sidon hp hp2 b, ?_⟩
  · obtain ⟨h1, h2⟩ := T_mem hp.pos ha
    exact ⟨h1, by omega⟩
  · rw [T_card hp hp2]
    set c := (goodIdx p b).card
    have hLN : L + 1 ≤ N := by omega
    have h1 : p * x ≤ 2 * N * c := by
      have h3 : x ≤ 2 * (x - 2 * p ^ 2) := by omega
      calc p * x ≤ p * (2 * (x - 2 * p ^ 2)) := Nat.mul_le_mul_left _ h3
        _ = 2 * (p * (x - 2 * p ^ 2)) := by ring
        _ ≤ 2 * ((L + 1) * c) := Nat.mul_le_mul_left _ hb
        _ ≤ 2 * (N * c) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hLN)
        _ = 2 * N * c := by ring
    have e1 : (p * x) ^ 2 ≤ (2 * N * c) ^ 2 := Nat.pow_le_pow_left h1 2
    have hx0 : 0 < x ^ 2 := by positivity
    have e2 : x ^ 3 < 16 * (p * x) ^ 2 := by
      calc x ^ 3 = x * x ^ 2 := by ring
        _ < (16 * p ^ 2) * x ^ 2 := Nat.mul_lt_mul_of_pos_right hP2 hx0
        _ = 16 * (p * x) ^ 2 := by ring
    calc x ^ 3 < 16 * (p * x) ^ 2 := e2
      _ ≤ 16 * (2 * N * c) ^ 2 := Nat.mul_le_mul_left _ e1
      _ = 64 * N ^ 2 * c ^ 2 := by ring

/-- Chebyshev-type lower bound in the form used below: `4 N^(1-η) ≤ π(N/2)` eventually. -/
lemma pi_lower {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ∀ᶠ N : ℕ in atTop, 4 * (N : ℝ) ^ (1 - η) ≤ π (N / 2) := by
  have l2 : 0 < log 2 := log_pos one_lt_two
  have hA := (isLittleO_log_rpow_atTop hη).bound (c := log 2 / 24) (by positivity)
  have hB := (tendsto_atTop_add_const_right atTop 1 tendsto_id).eventually
    (isLittleO_log_id_atTop.bound (c := log 2 / 4) (by positivity))
  have hreal : ∀ᶠ x : ℝ in atTop, 12 * x ^ (1 - η) * log x + log (x + 1) ≤ x * log 2 := by
    filter_upwards [hA, hB, eventually_ge_atTop 1] with x hA hB hx
    have hx0 : 0 < x := by linarith
    rw [norm_of_nonneg (log_nonneg hx), norm_of_nonneg (rpow_nonneg hx0.le _)] at hA
    simp only [id] at hB
    rw [norm_of_nonneg (log_nonneg (by linarith)), norm_of_nonneg (by linarith)] at hB
    have key : x ^ (1 - η) * x ^ η = x := by rw [← rpow_add hx0]; simp
    have h1 := mul_le_mul_of_nonneg_left hA (by positivity : 0 ≤ 12 * x ^ (1 - η))
    nlinarith
  have hN := (tendsto_natCast_atTop_atTop.comp (Nat.tendsto_div_const_atTop two_ne_zero)).eventually
    hreal
  filter_upwards [hN, eventually_ge_atTop 4] with N hN hN4
  simp only [Function.comp] at hN
  set n := N / 2
  have hn : (2 : ℝ) ≤ n := by exact_mod_cast (by omega : 2 ≤ n)
  have hlogn : 0 < log n := log_pos (by linarith)
  have hpi := Chebyshev.pi_ge n
  have h12 : 12 * (n : ℝ) ^ (1 - η) ≤ π n := by
    refine le_trans ?_ hpi
    rw [le_div_iff₀ hlogn]; linarith
  have hNn : (N : ℝ) ≤ 3 * n := by exact_mod_cast (by omega : N ≤ 3 * n)
  have h3 : (N : ℝ) ^ (1 - η) ≤ 3 * (n : ℝ) ^ (1 - η) := by
    calc (N : ℝ) ^ (1 - η) ≤ (3 * n) ^ (1 - η) := rpow_le_rpow (by positivity) hNn (by linarith)
      _ = 3 ^ (1 - η) * (n : ℝ) ^ (1 - η) := mul_rpow (by norm_num) (by positivity)
      _ ≤ 3 * (n : ℝ) ^ (1 - η) := by
        gcongr
        calc (3 : ℝ) ^ (1 - η) ≤ 3 ^ (1 : ℝ) := rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          _ = 3 := rpow_one 3
  linarith

lemma one_le_log {N : ℕ} (hN : 3 ≤ N) : 1 ≤ log N := by
  rw [le_log_iff_exp_le (by positivity)]
  have := exp_one_lt_d9
  have h3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  linarith

/-- Turning the finite inequality into the exponent bound, for `0 < ε ≤ 1/2`. -/
lemma lower_of {N : ℕ} {A : Finset ℕ} (hA : (π (N / 2)) ^ 3 < 64 * N ^ 2 * A.card ^ 2)
    {ε : ℝ} (hε2 : ε ≤ 1 / 2) (hpi : 4 * (N : ℝ) ^ (1 - 2 * ε / 3) ≤ π (N / 2)) (hN : 3 ≤ N) :
    ((N : ℝ) / log N) ^ (1 / 2 - ε) ≤ A.card := by
  have hN0 : (0 : ℝ) < N := by positivity
  have hA' : ((π (N / 2) : ℕ) : ℝ) ^ 3 < 64 * (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2 := by exact_mod_cast hA
  have h1 : (4 * (N : ℝ) ^ (1 - 2 * ε / 3)) ^ 3 ≤ ((π (N / 2) : ℕ) : ℝ) ^ 3 :=
    pow_le_pow_left₀ (by positivity) hpi 3
  have h2 : (4 * (N : ℝ) ^ (1 - 2 * ε / 3)) ^ 3 = 64 * (N : ℝ) ^ 2 * ((N : ℝ) ^ (1 / 2 - ε)) ^ 2 := by
    have e1 : ((N : ℝ) ^ (1 - 2 * ε / 3)) ^ 3 = (N : ℝ) ^ ((1 - 2 * ε / 3) * ((3 : ℕ) : ℝ)) :=
      (rpow_mul_natCast hN0.le _ 3).symm
    have e2 : ((N : ℝ) ^ (1 / 2 - ε)) ^ 2 = (N : ℝ) ^ ((1 / 2 - ε) * ((2 : ℕ) : ℝ)) :=
      (rpow_mul_natCast hN0.le _ 2).symm
    have e3 : (N : ℝ) ^ 2 = (N : ℝ) ^ ((2 : ℕ) : ℝ) := (rpow_natCast _ 2).symm
    rw [mul_pow, e1, e2, e3, mul_assoc, ← rpow_add hN0,
      show (1 - 2 * ε / 3) * ((3 : ℕ) : ℝ) = ((2 : ℕ) : ℝ) + (1 / 2 - ε) * ((2 : ℕ) : ℝ) by
        push_cast; ring]
    norm_num
  have h3 : ((N : ℝ) ^ (1 / 2 - ε)) ^ 2 < (A.card : ℝ) ^ 2 := by
    have : (0 : ℝ) < 64 * (N : ℝ) ^ 2 := by positivity
    nlinarith
  have h4 := lt_of_pow_lt_pow_left₀ 2 (by positivity) h3
  have h5 : ((N : ℝ) / log N) ^ (1 / 2 - ε) ≤ (N : ℝ) ^ (1 / 2 - ε) :=
    rpow_le_rpow (div_nonneg hN0.le (by linarith [one_le_log hN])) (div_le_self hN0.le (one_le_log hN))
      (by linarith)
  linarith

/-- Upper bound: a Sidon set of naturals `≤ N` has `|A|² - |A| ≤ 2N` (distinct differences). -/
lemma sidon_card_sq {A : Finset ℕ} (hA : IsSidon A) {N : ℕ} (hle : ∀ a ∈ A, a ≤ N) :
    A.card * A.card - A.card ≤ 2 * N := by
  rw [← offDiag_card]
  have hcard : ((Icc (-(N : ℤ)) N).erase 0).card = 2 * N := by
    rw [card_erase_of_mem (by simp), Int.card_Icc]; omega
  rw [← hcard]
  refine card_le_card_of_injOn (fun q : ℕ × ℕ => (q.1 : ℤ) - q.2) ?_ ?_
  · intro q hq
    simp only [coe_offDiag] at hq
    have h1 := hle _ hq.1
    have h2 := hle _ hq.2.1
    have h3 := hq.2.2
    simp only [coe_erase, coe_Icc, Set.mem_sdiff, Set.mem_Icc, Set.mem_singleton_iff]
    omega
  · rintro ⟨a, b⟩ hq ⟨c, d⟩ hq' h
    simp only [coe_offDiag] at hq hq' h
    rcases hA a hq.1 d hq'.2.1 c hq'.1 b hq.2.1 (by omega) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp [h1, h2]
    · exact absurd h1 hq.2.2

/-- Upper bound, for every Sidon set of naturals `≤ N`: eventually `|A| ≤ (N / log N)^(1/2 + ε)`. -/
lemma sidon_upper {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℕ, IsSidon A → (∀ a ∈ A, a ≤ N) →
      (A.card : ℝ) ≤ ((N : ℝ) / log N) ^ (1 / 2 + ε) := by
  have h := (isLittleO_log_rpow_rpow_atTop (1 + 2 * ε) (by linarith : (0 : ℝ) < 2 * ε)).bound
    (c := 1 / 4) (by norm_num)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually h, eventually_ge_atTop 3]
    with N hN hN3 A hA hle
  have hN0 : (0 : ℝ) < N := by positivity
  have hlog := one_le_log hN3
  rw [norm_of_nonneg (rpow_nonneg (by linarith) _), norm_of_nonneg (rpow_nonneg hN0.le _)] at hN
  have key : 4 * (N : ℝ) ≤ ((N : ℝ) / log N) ^ (1 + 2 * ε) := by
    rw [div_rpow hN0.le (by linarith), le_div_iff₀ (rpow_pos_of_pos (by linarith) _),
      rpow_add hN0, rpow_one]
    have : 0 ≤ (N : ℝ) := hN0.le
    nlinarith
  have hc : A.card ≤ N + 1 :=
    calc A.card ≤ (range (N + 1)).card :=
          card_le_card fun a ha => mem_range.2 (Nat.lt_succ_of_le (hle a ha))
      _ = N + 1 := card_range _
  have hsq := sidon_card_sq hA hle
  have hc2 : A.card ^ 2 ≤ 4 * N := by
    have : A.card ^ 2 = A.card * A.card := sq _
    omega
  have hc2' : (A.card : ℝ) ^ 2 ≤ (((N : ℝ) / log N) ^ (1 / 2 + ε)) ^ 2 := by
    rw [← rpow_mul_natCast (div_nonneg hN0.le (by linarith)),
      show (1 / 2 + ε) * ((2 : ℕ) : ℝ) = 1 + 2 * ε by push_cast; ring]
    have : ((A.card ^ 2 : ℕ) : ℝ) ≤ ((4 * N : ℕ) : ℝ) := by exact_mod_cast hc2
    push_cast at this
    linarith
  exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) hc2'

/-- **Conjecture 00000000037 (ε-form).** There are Sidon sets `A N` of primes `≤ N` such that for
every `ε > 0` and every sufficiently large `N`,
`(N / log N)^(1/2 - ε) ≤ |A N| ≤ (N / log N)^(1/2 + ε)`. -/
theorem conjecture_37 :
    ∃ A : ℕ → Finset ℕ, (∀ N, (∀ a ∈ A N, a.Prime ∧ a ≤ N) ∧ IsSidon (A N)) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
        ((N : ℝ) / log N) ^ (1 / 2 - ε) ≤ (A N).card ∧
          ((A N).card : ℝ) ≤ ((N : ℝ) / log N) ^ (1 / 2 + ε) := by
  have hex : ∀ N : ℕ, ∃ A : Finset ℕ, ((∀ a ∈ A, a.Prime ∧ a ≤ N) ∧ IsSidon A) ∧
      (64 ≤ π (N / 2) → (π (N / 2)) ^ 3 < 64 * N ^ 2 * A.card ^ 2) := by
    intro N
    by_cases h : 64 ≤ π (N / 2)
    · obtain ⟨A, h1, h2, h3⟩ := construct N h
      exact ⟨A, ⟨h1, h2⟩, fun _ => h3⟩
    · exact ⟨∅, ⟨by simp, by intro a ha; simp at ha⟩, fun h' => absurd h' h⟩
  choose A hA hAbig using hex
  refine ⟨A, hA, fun ε hε => ?_⟩
  set ε' := min ε (1 / 2) with hε'
  have hε'0 : 0 < ε' := lt_min hε (by norm_num)
  have hε'1 : ε' ≤ 1 / 2 := min_le_right _ _
  have h64 : ∀ᶠ N : ℕ in atTop, 64 ≤ π (N / 2) :=
    (Nat.tendsto_primeCounting.comp (Nat.tendsto_div_const_atTop two_ne_zero)).eventually_ge_atTop 64
  filter_upwards [h64, pi_lower (η := 2 * ε' / 3) (by positivity) (by linarith), sidon_upper hε,
    eventually_ge_atTop 3] with N h64 hpi hup hN3
  refine ⟨?_, hup _ (hA N).2 fun a ha => ((hA N).1 a ha).2⟩
  have hlow := lower_of (hAbig N h64) hε'1 hpi hN3
  have hN0 : (0 : ℝ) < N := by positivity
  have hlog := one_le_log hN3
  have hbase : 1 ≤ (N : ℝ) / log N := by
    rw [le_div_iff₀ (by linarith), one_mul]; exact log_le_self hN0.le
  calc ((N : ℝ) / log N) ^ (1 / 2 - ε) ≤ ((N : ℝ) / log N) ^ (1 / 2 - ε') :=
        rpow_le_rpow_of_exponent_le hbase (by linarith [min_le_left ε (1 / 2)])
    _ ≤ _ := hlow

/-- **Conjecture 00000000037 (literal `o(1)` form).** There are Sidon sets `A N` of primes `≤ N`
and a function `δ N → 0` with `|A N| = (N / log N)^(1/2 - δ N)` for all large `N`. -/
theorem conjecture_37_littleO :
    ∃ A : ℕ → Finset ℕ, (∀ N, (∀ a ∈ A N, a.Prime ∧ a ≤ N) ∧ IsSidon (A N)) ∧
      ∃ δ : ℕ → ℝ, Tendsto δ atTop (nhds 0) ∧
        ∀ᶠ N : ℕ in atTop, ((A N).card : ℝ) = ((N : ℝ) / log N) ^ (1 / 2 - δ N) := by
  obtain ⟨A, hA, hb⟩ := conjecture_37
  have hpos : ∀ᶠ N : ℕ in atTop,
      0 < (N : ℝ) / log N ∧ 0 < log ((N : ℝ) / log N) ∧ 0 < ((A N).card : ℝ) := by
    filter_upwards [hb (1 / 4) (by norm_num), eventually_ge_atTop 3] with N ⟨h1, _⟩ hN3
    have hN0 : (0 : ℝ) < N := by positivity
    have hB1 : 1 < (N : ℝ) / log N := by
      rw [lt_div_iff₀ (by linarith [one_le_log hN3]), one_mul]
      linarith [log_le_sub_one_of_pos hN0]
    exact ⟨by linarith, log_pos hB1, lt_of_lt_of_le (rpow_pos_of_pos (by linarith) _) h1⟩
  refine ⟨A, hA, fun N => 1 / 2 - log (A N).card / log ((N : ℝ) / log N), ?_, ?_⟩
  · rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [hb (ε / 2) (by positivity), hpos] with N ⟨h1, h2⟩ ⟨hBpos, hlB, hc⟩
    have l1 := log_le_log (rpow_pos_of_pos hBpos _) h1
    have l2 := log_le_log hc h2
    rw [log_rpow hBpos] at l1 l2
    rw [Real.dist_eq, sub_zero, abs_lt]
    constructor
    · have : log ((A N).card : ℝ) / log ((N : ℝ) / log N) ≤ 1 / 2 + ε / 2 := by
        rw [div_le_iff₀ hlB]; linarith
      linarith
    · have : 1 / 2 - ε / 2 ≤ log ((A N).card : ℝ) / log ((N : ℝ) / log N) := by
        rw [le_div_iff₀ hlB]; linarith
      linarith
  · filter_upwards [hpos] with N ⟨hBpos, hlB, hc⟩
    rw [rpow_def_of_pos hBpos, show (1 : ℝ) / 2 - (1 / 2 - log ((A N).card : ℝ) /
      log ((N : ℝ) / log N)) = log ((A N).card : ℝ) / log ((N : ℝ) / log N) by ring,
      show log ((N : ℝ) / log N) * (log ((A N).card : ℝ) / log ((N : ℝ) / log N)) =
        log ((A N).card : ℝ) by field_simp, exp_log hc]

/-- A prime `a ≤ N` is one of the first `N` primes `nth Nat.Prime 0, …, nth Nat.Prime (N-1)`. -/
lemma mem_first_primes {a N : ℕ} (ha : a.Prime) (haN : a ≤ N) : ∃ k < N, a = Nat.nth Nat.Prime k := by
  refine ⟨Nat.count Nat.Prime a, ?_, (Nat.nth_count ha).symm⟩
  rw [Nat.count_eq_card_filter_range]
  calc _ ≤ ((range a).erase 0).card := card_le_card fun q hq => by
        simp only [mem_filter, mem_range, mem_erase] at hq ⊢; exact ⟨hq.2.ne_zero, hq.1⟩
    _ < N := by rw [card_erase_of_mem (mem_range.2 ha.pos), card_range]; have := ha.two_le; omega

/-- **Reading "among the first `N` primes" (lower bound).** The same sets `A N` are Sidon subsets of
`{nth Nat.Prime k : k < N}` with `|A N| ≥ (N / log N)^(1/2 - ε)` for all large `N`. -/
theorem conjecture_37_firstPrimes :
    ∃ A : ℕ → Finset ℕ, (∀ N, (∀ a ∈ A N, ∃ k < N, a = Nat.nth Nat.Prime k) ∧ IsSidon (A N)) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ((N : ℝ) / log N) ^ (1 / 2 - ε) ≤ (A N).card := by
  obtain ⟨A, hA, hb⟩ := conjecture_37
  exact ⟨A, fun N => ⟨fun a ha => mem_first_primes ((hA N).1 a ha).1 ((hA N).1 a ha).2, (hA N).2⟩,
    fun ε hε => (hb ε hε).mono fun _ h => h.1⟩

end C37
