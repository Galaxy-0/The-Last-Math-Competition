import Mathlib

/-!
# Conjecture 00000000117 holds

Conjecture 00000000117 asserts that for every base `b ∈ [2, 16]` there is a
`b`-ary pandigital prime: a prime whose base-`b` expansion contains each of the
digits `0, …, b - 1` at least once.

We exhibit one for every base: the smallest such prime (OEIS A185122). For each
witness we check that its base-`b` digits contain all `b` digits. We also
certify its primality. Witnesses below `10⁶` are handled by `norm_num`. The
larger ones, up to about `1.85 · 10¹⁹` for base `16`, use Pratt certificates
checked against Mathlib's `lucas_primality`. Such a certificate consists of
the factorization of `p - 1` into primes, which are themselves certified
recursively, together with a witness `a` of order `p - 1` modulo `p`.

| `b` | smallest pandigital prime | in base `b` |
|---|---|---|
| 2 | 2 | 10 |
| 3 | 11 | 102 |
| 4 | 283 | 10123 |
| 5 | 3319 | 101234 |
| 6 | 48761 | 1013425 |
| 7 | 863231 | 10223465 |
| 8 | 17119607 | 101234567 |
| 9 | 393474749 | 1012346785 |
| 10 | 10123457689 | 10123457689 |
| 11 | 290522736467 | 1022345689A7 |
| 12 | 8989787252711 | 101234568A79B |
| 13 | 304978405943587 | 10123456789ABC |
| 14 | 11177758345241723 | 10123456789CDAB |
| 15 | 442074237951168419 | 10223456789ADBCE |
| 16 | 18528729602926047181 | 10123456789ABEFCD |

Modular powers inside the certificates are computed by `powMod`, binary
exponentiation, which the kernel evaluates with its built-in arithmetic on
numerals (`decide +kernel`). `powMod_eq` proves it equal to `a ^ e % m`.
Nothing is delegated to compiled code: every check is a kernel reduction.
-/

namespace Submission00000000117

/-- `p` is `b`-ary pandigital: its base-`b` expansion contains every digit
`0, …, b - 1`. -/
def IsPandigital (b p : ℕ) : Prop := ∀ d < b, d ∈ Nat.digits b p

/-- Conjecture 00000000117: for every base `b ∈ [2, 16]` there is a `b`-ary
pandigital prime. -/
def ConjectureHolds : Prop := ∀ b, 2 ≤ b → b ≤ 16 → ∃ p, p.Prime ∧ IsPandigital b p

/-! ## Primality certificates -/

/-- Modular exponentiation by repeated squaring: `powMod m fuel a e = a ^ e % m`
whenever `e < 2 ^ fuel` (`powMod_eq`). -/
def powMod (m : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 1 % m
  | fuel + 1, a, e =>
    if e = 0 then 1 % m
    else
      let r := powMod m fuel (a * a % m) (e / 2)
      if e % 2 = 0 then r else a * r % m

theorem powMod_eq (m : ℕ) : ∀ (fuel a e : ℕ), e < 2 ^ fuel → powMod m fuel a e = a ^ e % m
  | 0, a, e, he => by
    have : e = 0 := by simpa using he
    subst this
    simp [powMod]
  | fuel + 1, a, e, he => by
    rw [powMod]
    split_ifs with h0 h2
    · subst h0; simp
    · have ih := powMod_eq m fuel (a * a % m) (e / 2) (by rw [pow_succ] at he; omega)
      simp only at ih ⊢
      rw [ih, ← Nat.pow_mod, ← pow_two, ← pow_mul, Nat.two_mul_div_two_of_even
        (Nat.even_iff.2 h2)]
    · have ih := powMod_eq m fuel (a * a % m) (e / 2) (by rw [pow_succ] at he; omega)
      simp only at ih ⊢
      rw [ih, ← Nat.pow_mod, ← pow_two, ← pow_mul, Nat.mul_mod, Nat.mod_mod,
        ← Nat.mul_mod, ← pow_succ']
      congr 2
      omega

/-- A prime dividing a product of prime powers is one of the primes. -/
theorem mem_of_prime_dvd_prod (r : ℕ) (hr : r.Prime) :
    ∀ fs : List (ℕ × ℕ), (∀ x ∈ fs, x.1.Prime) →
      r ∣ (fs.map fun x => x.1 ^ x.2).prod → r ∈ fs.map Prod.fst
  | [], _, h => by
    simp only [List.map_nil, List.prod_nil, Nat.dvd_one] at h
    exact absurd h hr.one_lt.ne'
  | x :: fs, hfs, h => by
    simp only [List.map_cons, List.prod_cons] at h
    rcases (Nat.Prime.dvd_mul hr).1 h with h | h
    · have := (Nat.prime_dvd_prime_iff_eq hr (hfs x (by simp))).1 (hr.dvd_of_dvd_pow h)
      simp [this]
    · have := mem_of_prime_dvd_prod r hr fs (fun y hy => hfs y (by simp [hy])) h
      simp only [List.map_cons, List.mem_cons]
      exact Or.inr this

/-- Lucas' criterion with a Pratt certificate: if `p - 1 = ∏ qᵢ ^ eᵢ` with all `qᵢ`
prime, `a ^ (p - 1) ≡ 1` and `a ^ ((p - 1) / qᵢ) ≢ 1 (mod p)` for every `i`, then `p`
is prime. The powers are evaluated with `powMod`. -/
theorem prime_of_cert (p a : ℕ) (fs : List (ℕ × ℕ)) (hp : 2 ≤ p) (hlt : p < 2 ^ 128)
    (hprod : (fs.map fun x => x.1 ^ x.2).prod = p - 1)
    (hprime : ∀ x ∈ fs, x.1.Prime)
    (hpow : powMod p 128 a (p - 1) = 1)
    (horder : ∀ x ∈ fs, powMod p 128 a ((p - 1) / x.1) ≠ 1) : p.Prime := by
  have hcast : ∀ k, k < 2 ^ 128 → (((a : ZMod p) ^ k = 1) ↔ powMod p 128 a k = 1) := by
    intro k hk
    rw [powMod_eq p 128 a k hk, ← Nat.cast_pow, ← Nat.cast_one,
      ZMod.natCast_eq_natCast_iff', Nat.one_mod_eq_one.2 (by omega)]
  refine lucas_primality p (a : ZMod p) ((hcast _ (by omega)).2 hpow) ?_
  intro q hq hdvd
  rw [Ne, hcast _ (lt_of_le_of_lt (Nat.div_le_self _ _) (by omega))]
  have hmem := mem_of_prime_dvd_prod q hq fs hprime (hprod ▸ hdvd)
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hmem
  exact horder x hx

/-! ## Certificates for the witnesses and their factors -/

/-- `1065901 - 1 = 2² · 3 · 5² · 11 · 17 · 19`;
the witness `6` has order `p - 1` modulo `p = 1065901`. -/
theorem prime_1065901 : Nat.Prime 1065901 :=
  prime_of_cert 1065901 6
    [(2, 2), (3, 1), (5, 2), (11, 1), (17, 1), (19, 1)]
    (by norm_num) (by norm_num) (by decide +kernel)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro x (rfl | rfl | rfl | rfl | rfl | rfl)
        · norm_num
        · norm_num
        · norm_num
        · norm_num
        · norm_num
        · norm_num)
    (by decide +kernel) (by decide +kernel)

/-- `1222829 - 1 = 2² · 347 · 881`;
the witness `2` has order `p - 1` modulo `p = 1222829`. -/
theorem prime_1222829 : Nat.Prime 1222829 :=
  prime_of_cert 1222829 2
    [(2, 2), (347, 1), (881, 1)]
    (by norm_num) (by norm_num) (by decide +kernel)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro x (rfl | rfl | rfl)
        · norm_num
        · norm_num
        · norm_num)
    (by decide +kernel) (by decide +kernel)

/-- `6395407 - 1 = 2 · 3 · 1065901`;
the witness `3` has order `p - 1` modulo `p = 6395407`. -/
theorem prime_6395407 : Nat.Prime 6395407 :=
  prime_of_cert 6395407 3
    [(2, 1), (3, 1), (1065901, 1)]
    (by norm_num) (by norm_num) (by decide +kernel)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro x (rfl | rfl | rfl)
        · norm_num
        · norm_num
        · exact prime_1065901)
    (by decide +kernel) (by decide +kernel)

/-- `17119607 - 1 = 2 · 7 · 1222829`;
the witness `5` has order `p - 1` modulo `p = 17119607`. -/
theorem prime_17119607 : Nat.Prime 17119607 :=
  prime_of_cert 17119607 5
    [(2, 1), (7, 1), (1222829, 1)]
    (by norm_num) (by norm_num) (by decide +kernel)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro x (rfl | rfl | rfl)
        · norm_num
        · norm_num
        · exact prime_1222829)
    (by decide +kernel) (by decide +kernel)

/-- `67222271 - 1 = 2 · 5 · 2087 · 3221`;
the witness `7` has order `p - 1` modulo `p = 67222271`. -/
theorem prime_67222271 : Nat.Prime 67222271 :=
  prime_of_cert 67222271 7
    [(2, 1), (5, 1), (2087, 1), (3221, 1)]
    (by norm_num) (by norm_num) (by decide +kernel)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro x (rfl | rfl | rfl | rfl)
        · norm_num
        · norm_num
        · norm_num
        · norm_num)
    (by decide +kernel) (by decide +kernel)

/-- `335476601 - 1 = 2³ · 5² · 47 · 89 · 401`;
the witness `6` has order `p - 1` modulo `p = 335476601`. -/
theorem prime_335476601 : Nat.Prime 335476601 :=
  prime_of_cert 335476601 6
    [(2, 3), (5, 2), (47, 1), (89, 1), (401, 1)]
    (by norm_num) (by norm_num) (by decide +kernel)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro x (rfl | rfl | rfl | rfl | rfl)
        · norm_num
        · norm_num
        · norm_num
        · norm_num
        · norm_num)
    (by decide +kernel) (by decide +kernel)

/-- `393474749 - 1 = 2² · 691 · 142357`;
the witness `2` has order `p - 1` modulo `p = 393474749`. -/
theorem prime_393474749 : Nat.Prime 393474749 :=
  prime_of_cert 393474749 2
    [(2, 2), (691, 1), (142357, 1)]
    (by norm_num) (by norm_num) (by decide +kernel)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro x (rfl | rfl | rfl)
        · norm_num
        · norm_num
        · norm_num)
    (by decide +kernel) (by decide +kernel)

/-- `10123457689 - 1 = 2³ · 3² · 4091 · 34369`;
the witness `13` has order `p - 1` modulo `p = 10123457689`. -/
theorem prime_10123457689 : Nat.Prime 10123457689 :=
  prime_of_cert 10123457689 13
    [(2, 3), (3, 2), (4091, 1), (34369, 1)]
    (by norm_num) (by norm_num) (by decide +kernel)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro x (rfl | rfl | rfl | rfl)
        · norm_num
        · norm_num
        · norm_num
        · norm_num)
    (by decide +kernel) (by decide +kernel)

/-- `290522736467 - 1 = 2 · 433 · 335476601`;
the witness `2` has order `p - 1` modulo `p = 290522736467`. -/
theorem prime_290522736467 : Nat.Prime 290522736467 :=
  prime_of_cert 290522736467 2
    [(2, 1), (433, 1), (335476601, 1)]
    (by norm_num) (by norm_num) (by decide +kernel)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro x (rfl | rfl | rfl)
        · norm_num
        · norm_num
        · exact prime_335476601)
    (by decide +kernel) (by decide +kernel)

/-- `8989787252711 - 1 = 2 · 5 · 11 · 131617 · 620933`;
the witness `11` has order `p - 1` modulo `p = 8989787252711`. -/
theorem prime_8989787252711 : Nat.Prime 8989787252711 :=
  prime_of_cert 8989787252711 11
    [(2, 1), (5, 1), (11, 1), (131617, 1), (620933, 1)]
    (by norm_num) (by norm_num) (by decide +kernel)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro x (rfl | rfl | rfl | rfl | rfl)
        · norm_num
        · norm_num
        · norm_num
        · norm_num
        · norm_num)
    (by decide +kernel) (by decide +kernel)

/-- `35485169204621 - 1 = 2² · 5 · 41 · 197 · 317 · 347 · 1997`;
the witness `2` has order `p - 1` modulo `p = 35485169204621`. -/
theorem prime_35485169204621 : Nat.Prime 35485169204621 :=
  prime_of_cert 35485169204621 2
    [(2, 2), (5, 1), (41, 1), (197, 1), (317, 1), (347, 1), (1997, 1)]
    (by norm_num) (by norm_num) (by decide +kernel)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro x (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
        · norm_num
        · norm_num
        · norm_num
        · norm_num
        · norm_num
        · norm_num
        · norm_num)
    (by decide +kernel) (by decide +kernel)

/-- `50829734323931 - 1 = 2 · 5 · 1129 · 13873 · 324529`;
the witness `2` has order `p - 1` modulo `p = 50829734323931`. -/
theorem prime_50829734323931 : Nat.Prime 50829734323931 :=
  prime_of_cert 50829734323931 2
    [(2, 1), (5, 1), (1129, 1), (13873, 1), (324529, 1)]
    (by norm_num) (by norm_num) (by decide +kernel)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro x (rfl | rfl | rfl | rfl | rfl)
        · norm_num
        · norm_num
        · norm_num
        · norm_num
        · norm_num)
    (by decide +kernel) (by decide +kernel)

/-- `132708276772139 - 1 = 2 · 19 · 47 · 170179 · 436627`;
the witness `2` has order `p - 1` modulo `p = 132708276772139`. -/
theorem prime_132708276772139 : Nat.Prime 132708276772139 :=
  prime_of_cert 132708276772139 2
    [(2, 1), (19, 1), (47, 1), (170179, 1), (436627, 1)]
    (by norm_num) (by norm_num) (by decide +kernel)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro x (rfl | rfl | rfl | rfl | rfl)
        · norm_num
        · norm_num
        · norm_num
        · norm_num
        · norm_num)
    (by decide +kernel) (by decide +kernel)

/-- `304978405943587 - 1 = 2 · 3 · 50829734323931`;
the witness `2` has order `p - 1` modulo `p = 304978405943587`. -/
theorem prime_304978405943587 : Nat.Prime 304978405943587 :=
  prime_of_cert 304978405943587 2
    [(2, 1), (3, 1), (50829734323931, 1)]
    (by norm_num) (by norm_num) (by decide +kernel)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro x (rfl | rfl | rfl)
        · norm_num
        · norm_num
        · exact prime_50829734323931)
    (by decide +kernel) (by decide +kernel)

/-- `11177758345241723 - 1 = 2 · 13 · 6395407 · 67222271`;
the witness `2` has order `p - 1` modulo `p = 11177758345241723`. -/
theorem prime_11177758345241723 : Nat.Prime 11177758345241723 :=
  prime_of_cert 11177758345241723 2
    [(2, 1), (13, 1), (6395407, 1), (67222271, 1)]
    (by norm_num) (by norm_num) (by decide +kernel)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro x (rfl | rfl | rfl | rfl)
        · norm_num
        · norm_num
        · exact prime_6395407
        · exact prime_67222271)
    (by decide +kernel) (by decide +kernel)

/-- `442074237951168419 - 1 = 2 · 6229 · 35485169204621`;
the witness `2` has order `p - 1` modulo `p = 442074237951168419`. -/
theorem prime_442074237951168419 : Nat.Prime 442074237951168419 :=
  prime_of_cert 442074237951168419 2
    [(2, 1), (6229, 1), (35485169204621, 1)]
    (by norm_num) (by norm_num) (by decide +kernel)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro x (rfl | rfl | rfl)
        · norm_num
        · norm_num
        · exact prime_35485169204621)
    (by decide +kernel) (by decide +kernel)

/-- `18528729602926047181 - 1 = 2² · 3 · 5 · 13 · 179 · 132708276772139`;
the witness `6` has order `p - 1` modulo `p = 18528729602926047181`. -/
theorem prime_18528729602926047181 : Nat.Prime 18528729602926047181 :=
  prime_of_cert 18528729602926047181 6
    [(2, 2), (3, 1), (5, 1), (13, 1), (179, 1), (132708276772139, 1)]
    (by norm_num) (by norm_num) (by decide +kernel)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro x (rfl | rfl | rfl | rfl | rfl | rfl)
        · norm_num
        · norm_num
        · norm_num
        · norm_num
        · norm_num
        · exact prime_132708276772139)
    (by decide +kernel) (by decide +kernel)

/-! ## The witnesses -/

/-- `2` in base `2`, least significant digit first. -/
theorem digits_2 :
    Nat.digits 2 2 = [0, 1] := by
  rw [show (2 : ℕ) =
    Nat.ofDigits 2 [0, 1] by decide +kernel]
  exact Nat.digits_ofDigits 2 (by norm_num) _ (by decide +kernel) (by simp)

theorem isPandigital_2 : IsPandigital 2 2 := by
  unfold IsPandigital
  rw [digits_2]
  decide +kernel

/-- `11` in base `3`, least significant digit first. -/
theorem digits_3 :
    Nat.digits 3 11 = [2, 0, 1] := by
  rw [show (11 : ℕ) =
    Nat.ofDigits 3 [2, 0, 1] by decide +kernel]
  exact Nat.digits_ofDigits 3 (by norm_num) _ (by decide +kernel) (by simp)

theorem isPandigital_3 : IsPandigital 3 11 := by
  unfold IsPandigital
  rw [digits_3]
  decide +kernel

/-- `283` in base `4`, least significant digit first. -/
theorem digits_4 :
    Nat.digits 4 283 = [3, 2, 1, 0, 1] := by
  rw [show (283 : ℕ) =
    Nat.ofDigits 4 [3, 2, 1, 0, 1] by decide +kernel]
  exact Nat.digits_ofDigits 4 (by norm_num) _ (by decide +kernel) (by simp)

theorem isPandigital_4 : IsPandigital 4 283 := by
  unfold IsPandigital
  rw [digits_4]
  decide +kernel

/-- `3319` in base `5`, least significant digit first. -/
theorem digits_5 :
    Nat.digits 5 3319 = [4, 3, 2, 1, 0, 1] := by
  rw [show (3319 : ℕ) =
    Nat.ofDigits 5 [4, 3, 2, 1, 0, 1] by decide +kernel]
  exact Nat.digits_ofDigits 5 (by norm_num) _ (by decide +kernel) (by simp)

theorem isPandigital_5 : IsPandigital 5 3319 := by
  unfold IsPandigital
  rw [digits_5]
  decide +kernel

/-- `48761` in base `6`, least significant digit first. -/
theorem digits_6 :
    Nat.digits 6 48761 = [5, 2, 4, 3, 1, 0, 1] := by
  rw [show (48761 : ℕ) =
    Nat.ofDigits 6 [5, 2, 4, 3, 1, 0, 1] by decide +kernel]
  exact Nat.digits_ofDigits 6 (by norm_num) _ (by decide +kernel) (by simp)

theorem isPandigital_6 : IsPandigital 6 48761 := by
  unfold IsPandigital
  rw [digits_6]
  decide +kernel

/-- `863231` in base `7`, least significant digit first. -/
theorem digits_7 :
    Nat.digits 7 863231 = [5, 6, 4, 3, 2, 2, 0, 1] := by
  rw [show (863231 : ℕ) =
    Nat.ofDigits 7 [5, 6, 4, 3, 2, 2, 0, 1] by decide +kernel]
  exact Nat.digits_ofDigits 7 (by norm_num) _ (by decide +kernel) (by simp)

theorem isPandigital_7 : IsPandigital 7 863231 := by
  unfold IsPandigital
  rw [digits_7]
  decide +kernel

/-- `17119607` in base `8`, least significant digit first. -/
theorem digits_8 :
    Nat.digits 8 17119607 = [7, 6, 5, 4, 3, 2, 1, 0, 1] := by
  rw [show (17119607 : ℕ) =
    Nat.ofDigits 8 [7, 6, 5, 4, 3, 2, 1, 0, 1] by decide +kernel]
  exact Nat.digits_ofDigits 8 (by norm_num) _ (by decide +kernel) (by simp)

theorem isPandigital_8 : IsPandigital 8 17119607 := by
  unfold IsPandigital
  rw [digits_8]
  decide +kernel

/-- `393474749` in base `9`, least significant digit first. -/
theorem digits_9 :
    Nat.digits 9 393474749 = [5, 8, 7, 6, 4, 3, 2, 1, 0, 1] := by
  rw [show (393474749 : ℕ) =
    Nat.ofDigits 9 [5, 8, 7, 6, 4, 3, 2, 1, 0, 1] by decide +kernel]
  exact Nat.digits_ofDigits 9 (by norm_num) _ (by decide +kernel) (by simp)

theorem isPandigital_9 : IsPandigital 9 393474749 := by
  unfold IsPandigital
  rw [digits_9]
  decide +kernel

/-- `10123457689` in base `10`, least significant digit first. -/
theorem digits_10 :
    Nat.digits 10 10123457689 = [9, 8, 6, 7, 5, 4, 3, 2, 1, 0, 1] := by
  rw [show (10123457689 : ℕ) =
    Nat.ofDigits 10 [9, 8, 6, 7, 5, 4, 3, 2, 1, 0, 1] by decide +kernel]
  exact Nat.digits_ofDigits 10 (by norm_num) _ (by decide +kernel) (by simp)

theorem isPandigital_10 : IsPandigital 10 10123457689 := by
  unfold IsPandigital
  rw [digits_10]
  decide +kernel

/-- `290522736467` in base `11`, least significant digit first. -/
theorem digits_11 :
    Nat.digits 11 290522736467 = [7, 10, 9, 8, 6, 5, 4, 3, 2, 2, 0, 1] := by
  rw [show (290522736467 : ℕ) =
    Nat.ofDigits 11 [7, 10, 9, 8, 6, 5, 4, 3, 2, 2, 0, 1] by decide +kernel]
  exact Nat.digits_ofDigits 11 (by norm_num) _ (by decide +kernel) (by simp)

theorem isPandigital_11 : IsPandigital 11 290522736467 := by
  unfold IsPandigital
  rw [digits_11]
  decide +kernel

/-- `8989787252711` in base `12`, least significant digit first. -/
theorem digits_12 :
    Nat.digits 12 8989787252711 = [11, 9, 7, 10, 8, 6, 5, 4, 3, 2, 1, 0, 1] := by
  rw [show (8989787252711 : ℕ) =
    Nat.ofDigits 12 [11, 9, 7, 10, 8, 6, 5, 4, 3, 2, 1, 0, 1] by decide +kernel]
  exact Nat.digits_ofDigits 12 (by norm_num) _ (by decide +kernel) (by simp)

theorem isPandigital_12 : IsPandigital 12 8989787252711 := by
  unfold IsPandigital
  rw [digits_12]
  decide +kernel

/-- `304978405943587` in base `13`, least significant digit first. -/
theorem digits_13 :
    Nat.digits 13 304978405943587 = [12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 1] := by
  rw [show (304978405943587 : ℕ) =
    Nat.ofDigits 13 [12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 1] by decide +kernel]
  exact Nat.digits_ofDigits 13 (by norm_num) _ (by decide +kernel) (by simp)

theorem isPandigital_13 : IsPandigital 13 304978405943587 := by
  unfold IsPandigital
  rw [digits_13]
  decide +kernel

/-- `11177758345241723` in base `14`, least significant digit first. -/
theorem digits_14 :
    Nat.digits 14 11177758345241723 = [11, 10, 13, 12, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 1] := by
  rw [show (11177758345241723 : ℕ) =
    Nat.ofDigits 14 [11, 10, 13, 12, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 1] by decide +kernel]
  exact Nat.digits_ofDigits 14 (by norm_num) _ (by decide +kernel) (by simp)

theorem isPandigital_14 : IsPandigital 14 11177758345241723 := by
  unfold IsPandigital
  rw [digits_14]
  decide +kernel

/-- `442074237951168419` in base `15`, least significant digit first. -/
theorem digits_15 :
    Nat.digits 15 442074237951168419 = [14, 12, 11, 13, 10, 9, 8, 7, 6, 5, 4, 3, 2, 2, 0, 1] := by
  rw [show (442074237951168419 : ℕ) =
    Nat.ofDigits 15 [14, 12, 11, 13, 10, 9, 8, 7, 6, 5, 4, 3, 2, 2, 0, 1] by decide +kernel]
  exact Nat.digits_ofDigits 15 (by norm_num) _ (by decide +kernel) (by simp)

theorem isPandigital_15 : IsPandigital 15 442074237951168419 := by
  unfold IsPandigital
  rw [digits_15]
  decide +kernel

/-- `18528729602926047181` in base `16`, least significant digit first. -/
theorem digits_16 :
    Nat.digits 16 18528729602926047181 = [13, 12, 15, 14, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 1] := by
  rw [show (18528729602926047181 : ℕ) =
    Nat.ofDigits 16 [13, 12, 15, 14, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 1] by decide +kernel]
  exact Nat.digits_ofDigits 16 (by norm_num) _ (by decide +kernel) (by simp)

theorem isPandigital_16 : IsPandigital 16 18528729602926047181 := by
  unfold IsPandigital
  rw [digits_16]
  decide +kernel

/-- Conjecture 00000000117 holds: every base `b ∈ [2, 16]` has a pandigital
prime, namely the one listed in the table above. -/
theorem conjecture_00000000117 : ConjectureHolds := by
  intro b hb₂ hb₁₆
  interval_cases b
  · exact ⟨2, (by norm_num), isPandigital_2⟩
  · exact ⟨11, (by norm_num), isPandigital_3⟩
  · exact ⟨283, (by norm_num), isPandigital_4⟩
  · exact ⟨3319, (by norm_num), isPandigital_5⟩
  · exact ⟨48761, (by norm_num), isPandigital_6⟩
  · exact ⟨863231, (by norm_num), isPandigital_7⟩
  · exact ⟨17119607, prime_17119607, isPandigital_8⟩
  · exact ⟨393474749, prime_393474749, isPandigital_9⟩
  · exact ⟨10123457689, prime_10123457689, isPandigital_10⟩
  · exact ⟨290522736467, prime_290522736467, isPandigital_11⟩
  · exact ⟨8989787252711, prime_8989787252711, isPandigital_12⟩
  · exact ⟨304978405943587, prime_304978405943587, isPandigital_13⟩
  · exact ⟨11177758345241723, prime_11177758345241723, isPandigital_14⟩
  · exact ⟨442074237951168419, prime_442074237951168419, isPandigital_15⟩
  · exact ⟨18528729602926047181, prime_18528729602926047181, isPandigital_16⟩

end Submission00000000117

#print axioms Submission00000000117.conjecture_00000000117
