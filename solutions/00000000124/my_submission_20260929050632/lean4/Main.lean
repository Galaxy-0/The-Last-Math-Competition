/-!
# Disproof of TLMC conjecture 00000000124 (concrete, axiom-free certificates)

Conjecture (00000000124).  Let `q` be an odd prime such that 2 is a primitive root
modulo `q`; then the least positive integer `m(q)` missing from the orbit
`{2^n mod q : n >= 0}` satisfies `m(q) = O((log q)^2)`.

Refutation.  If `ord_q(2) = q-1` then `2^0, ..., 2^(q-2)` are `q-1` pairwise distinct
nonzero residues, i.e. exactly `{1, ..., q-1}`; the value `q` itself (residue 0) never
occurs.  Hence `m(q) = q` identically, which dominates `(log q)^2`.

This file machine-checks fully concrete instances of that argument for all 22 odd
primes `q < 200` with `ord_q(2) = q-1` (`q = 3, 5, ..., 197`).  For each such `q`:

* `pr_q`    certifies that 2 is a primitive root mod `q`: Fermat's congruence
            `2^(q-1) = 1` together with `2^((q-1)/f) <> 1` for every prime `f | q-1`;
* `dlog_ok_q`/`dl_len_q`/`cover_q` certify that every `1 <= k < q` occurs in the orbit,
            via explicit discrete-log witnesses (checked by `decide`);
* `lm_q`    : `IsLeastMissing q q`, i.e. the least missing positive integer is `q`;
* `pw_q`    : with `ell = floor(log2 q)`, `2^ell <= q < 2^(ell+1)` and `ell*ell < q`,
            the elementary gap `m(q) = q > (floor(log2 q))^2 >= (log_2 q)^2` at `q`.

The flagship `attack_101` bundles the verification verdict's spot check `q = 101`:
`m(101) = 101` while `(log_2 101)^2 = 36 < 101` (and `(ln 101)^2 = 21.29...`).

Everything is proved by `decide` over `Nat` arithmetic or by the elementary lemmas
below; `Check.lean` audits that no theorem depends on any axiom.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- `k` occurs in the orbit of 2 modulo `q`, witnessed by an exponent `n < q-1`. -/
def InOrbit (q k : Nat) : Prop := ∃ n, n < q - 1 ∧ 2 ^ n % q = k

/-- `m` is the least positive integer missing from the orbit of 2 mod `q`:
every positive `k < m` occurs in the orbit, and `m` itself does not.
For an admissible `q` the instance `IsLeastMissing q q` says exactly `m(q) = q`. -/
def IsLeastMissing (m q : Nat) : Prop :=
  (∀ k, 1 ≤ k → k < m → InOrbit q k) ∧ ¬ InOrbit q q

/-- `dlogOk q ns i` reads `ns` as discrete-log witnesses for the values
`i+1, i+2, ...`: entry number `j` must be some `n < q-1` with `2^n % q = i+j+1`. -/
def dlogOk (q : Nat) : List Nat → Nat → Bool
  | [], _ => true
  | n :: rest, i => decide (n < q - 1) && decide (2 ^ n % q = i + 1) && dlogOk q rest (i + 1)

/-- Left projection of a true Boolean conjunction. -/
theorem and_true_l {b c : Bool} (h : (b && c) = true) : b = true := by
  cases b with
  | true => rfl
  | false => exact Bool.noConfusion h

/-- Right projection of a true Boolean conjunction. -/
theorem and_true_r {b c : Bool} (h : (b && c) = true) : c = true := by
  cases b with
  | true => exact h
  | false => exact Bool.noConfusion h

/-- The Boolean check `dlogOk` really yields orbit membership for every value
in its index range `[i+1, i+ns.length]`. -/
theorem dlogOk_implies {q : Nat} :
    ∀ (ns : List Nat) (i : Nat), dlogOk q ns i = true →
      ∀ k, i + 1 ≤ k → k ≤ i + ns.length → InOrbit q k
  | [], i, _, k, hk1, hk2 => by
    have hki : k ≤ i := hk2
    exact absurd (Nat.le_trans hk1 hki) (Nat.not_succ_le_self i)
  | n :: rest, i, h, k, hk1, hk2 => by
    have hA : decide (n < q - 1) = true := and_true_l (and_true_l h)
    have hB : decide (2 ^ n % q = i + 1) = true := and_true_r (and_true_l h)
    have hC : dlogOk q rest (i + 1) = true := and_true_r h
    have hnlt : n < q - 1 := of_decide_eq_true hA
    have heq : 2 ^ n % q = i + 1 := of_decide_eq_true hB
    cases Nat.eq_or_lt_of_le hk1 with
    | inl he =>
      subst he
      exact ⟨n, hnlt, heq⟩
    | inr hlt =>
      have hk2'' : k ≤ i + (rest.length + 1) := hk2
      have hk2a : k ≤ i + rest.length + 1 := (Nat.add_assoc i rest.length 1).symm ▸ hk2''
      have hk2' : k ≤ i + 1 + rest.length := Nat.add_right_comm i rest.length 1 ▸ hk2a
      exact dlogOk_implies rest (i + 1) hC k hlt hk2'

/-- The residue `0` never occurs in the orbit of 2 modulo an odd `q` (here: any `q > 0`). -/
theorem not_inOrbit_self {q : Nat} (hq0 : 0 < q) : ¬ InOrbit q q := by
  intro h
  cases h with
  | intro n h' =>
    cases h' with
    | intro _ hn =>
      have hlt : 2 ^ n % q < q := Nat.mod_lt _ hq0
      rw [hn] at hlt
      exact Nat.lt_irrefl q hlt
/-- Discrete-log witnesses for q = 3: entry j equals n with 2^n ≡ j+1 (mod 3). -/
def dlogs_3 : List Nat := [0, 1]

theorem dlog_ok_3 : dlogOk 3 dlogs_3 0 = true := by decide

theorem dl_len_3 : dlogs_3.length = 2 := by decide

/-- Every `1 ≤ k < 3` occurs in the orbit `{2^n mod 3}`. -/
theorem cover_3 : ∀ k, 1 ≤ k → k < 3 → InOrbit 3 k := by
  intro k hk1 hk2
  exact dlogOk_implies dlogs_3 0 dlog_ok_3 k hk1 (by rw [dl_len_3]; exact Nat.le_of_lt_succ hk2)

/-- Certificate that 2 is a primitive root mod 3: Fermat plus `2^((q-1)/f) ≠ 1`
for each prime f ∣ q-1 (q-1 = 2). -/
theorem pr_3 : 2 ^ 2 % 3 = 1 ∧ 2 ^ 1 % 3 = 2 := by decide

theorem pw_3 : 2 ^ 1 ≤ 3 ∧ 3 < 2 ^ 2 ∧ 1 * 1 < 3 := by decide

/-- The least missing positive integer from the orbit of 2 mod 3 is 3: `m(3) = 3`. -/
theorem lm_3 : IsLeastMissing 3 3 := ⟨cover_3, not_inOrbit_self (by decide)⟩

/-- Discrete-log witnesses for q = 5: entry j equals n with 2^n ≡ j+1 (mod 5). -/
def dlogs_5 : List Nat := [0, 1, 3, 2]

theorem dlog_ok_5 : dlogOk 5 dlogs_5 0 = true := by decide

theorem dl_len_5 : dlogs_5.length = 4 := by decide

/-- Every `1 ≤ k < 5` occurs in the orbit `{2^n mod 5}`. -/
theorem cover_5 : ∀ k, 1 ≤ k → k < 5 → InOrbit 5 k := by
  intro k hk1 hk2
  exact dlogOk_implies dlogs_5 0 dlog_ok_5 k hk1 (by rw [dl_len_5]; exact Nat.le_of_lt_succ hk2)

/-- Certificate that 2 is a primitive root mod 5: Fermat plus `2^((q-1)/f) ≠ 1`
for each prime f ∣ q-1 (q-1 = 2). -/
theorem pr_5 : 2 ^ 4 % 5 = 1 ∧ 2 ^ 2 % 5 = 4 := by decide

theorem pw_5 : 2 ^ 2 ≤ 5 ∧ 5 < 2 ^ 3 ∧ 2 * 2 < 5 := by decide

/-- The least missing positive integer from the orbit of 2 mod 5 is 5: `m(5) = 5`. -/
theorem lm_5 : IsLeastMissing 5 5 := ⟨cover_5, not_inOrbit_self (by decide)⟩

/-- Discrete-log witnesses for q = 11: entry j equals n with 2^n ≡ j+1 (mod 11). -/
def dlogs_11 : List Nat := [0, 1, 8, 2, 4, 9, 7, 3, 6, 5]

theorem dlog_ok_11 : dlogOk 11 dlogs_11 0 = true := by decide

theorem dl_len_11 : dlogs_11.length = 10 := by decide

/-- Every `1 ≤ k < 11` occurs in the orbit `{2^n mod 11}`. -/
theorem cover_11 : ∀ k, 1 ≤ k → k < 11 → InOrbit 11 k := by
  intro k hk1 hk2
  exact dlogOk_implies dlogs_11 0 dlog_ok_11 k hk1 (by rw [dl_len_11]; exact Nat.le_of_lt_succ hk2)

/-- Certificate that 2 is a primitive root mod 11: Fermat plus `2^((q-1)/f) ≠ 1`
for each prime f ∣ q-1 (q-1 = 2 · 5). -/
theorem pr_11 : 2 ^ 10 % 11 = 1 ∧ 2 ^ 5 % 11 = 10 ∧ 2 ^ 2 % 11 = 4 := by decide

theorem pw_11 : 2 ^ 3 ≤ 11 ∧ 11 < 2 ^ 4 ∧ 3 * 3 < 11 := by decide

/-- The least missing positive integer from the orbit of 2 mod 11 is 11: `m(11) = 11`. -/
theorem lm_11 : IsLeastMissing 11 11 := ⟨cover_11, not_inOrbit_self (by decide)⟩

/-- Discrete-log witnesses for q = 13: entry j equals n with 2^n ≡ j+1 (mod 13). -/
def dlogs_13 : List Nat := [0, 1, 4, 2, 9, 5, 11, 3, 8, 10, 7, 6]

theorem dlog_ok_13 : dlogOk 13 dlogs_13 0 = true := by decide

theorem dl_len_13 : dlogs_13.length = 12 := by decide

/-- Every `1 ≤ k < 13` occurs in the orbit `{2^n mod 13}`. -/
theorem cover_13 : ∀ k, 1 ≤ k → k < 13 → InOrbit 13 k := by
  intro k hk1 hk2
  exact dlogOk_implies dlogs_13 0 dlog_ok_13 k hk1 (by rw [dl_len_13]; exact Nat.le_of_lt_succ hk2)

/-- Certificate that 2 is a primitive root mod 13: Fermat plus `2^((q-1)/f) ≠ 1`
for each prime f ∣ q-1 (q-1 = 2 · 3). -/
theorem pr_13 : 2 ^ 12 % 13 = 1 ∧ 2 ^ 6 % 13 = 12 ∧ 2 ^ 4 % 13 = 3 := by decide

theorem pw_13 : 2 ^ 3 ≤ 13 ∧ 13 < 2 ^ 4 ∧ 3 * 3 < 13 := by decide

/-- The least missing positive integer from the orbit of 2 mod 13 is 13: `m(13) = 13`. -/
theorem lm_13 : IsLeastMissing 13 13 := ⟨cover_13, not_inOrbit_self (by decide)⟩

/-- Discrete-log witnesses for q = 19: entry j equals n with 2^n ≡ j+1 (mod 19). -/
def dlogs_19 : List Nat := [0, 1, 13, 2, 16, 14, 6, 3, 8, 17, 12, 15, 5, 7, 11, 4,
  10, 9]

theorem dlog_ok_19 : dlogOk 19 dlogs_19 0 = true := by decide

theorem dl_len_19 : dlogs_19.length = 18 := by decide

/-- Every `1 ≤ k < 19` occurs in the orbit `{2^n mod 19}`. -/
theorem cover_19 : ∀ k, 1 ≤ k → k < 19 → InOrbit 19 k := by
  intro k hk1 hk2
  exact dlogOk_implies dlogs_19 0 dlog_ok_19 k hk1 (by rw [dl_len_19]; exact Nat.le_of_lt_succ hk2)

/-- Certificate that 2 is a primitive root mod 19: Fermat plus `2^((q-1)/f) ≠ 1`
for each prime f ∣ q-1 (q-1 = 2 · 3). -/
theorem pr_19 : 2 ^ 18 % 19 = 1 ∧ 2 ^ 9 % 19 = 18 ∧ 2 ^ 6 % 19 = 7 := by decide

theorem pw_19 : 2 ^ 4 ≤ 19 ∧ 19 < 2 ^ 5 ∧ 4 * 4 < 19 := by decide

/-- The least missing positive integer from the orbit of 2 mod 19 is 19: `m(19) = 19`. -/
theorem lm_19 : IsLeastMissing 19 19 := ⟨cover_19, not_inOrbit_self (by decide)⟩

/-- Discrete-log witnesses for q = 29: entry j equals n with 2^n ≡ j+1 (mod 29). -/
def dlogs_29 : List Nat := [0, 1, 5, 2, 22, 6, 12, 3, 10, 23, 25, 7, 18, 13, 27, 4,
  21, 11, 9, 24, 17, 26, 20, 8, 16, 19, 15, 14]

theorem dlog_ok_29 : dlogOk 29 dlogs_29 0 = true := by decide

theorem dl_len_29 : dlogs_29.length = 28 := by decide

/-- Every `1 ≤ k < 29` occurs in the orbit `{2^n mod 29}`. -/
theorem cover_29 : ∀ k, 1 ≤ k → k < 29 → InOrbit 29 k := by
  intro k hk1 hk2
  exact dlogOk_implies dlogs_29 0 dlog_ok_29 k hk1 (by rw [dl_len_29]; exact Nat.le_of_lt_succ hk2)

/-- Certificate that 2 is a primitive root mod 29: Fermat plus `2^((q-1)/f) ≠ 1`
for each prime f ∣ q-1 (q-1 = 2 · 7). -/
theorem pr_29 : 2 ^ 28 % 29 = 1 ∧ 2 ^ 14 % 29 = 28 ∧ 2 ^ 4 % 29 = 16 := by decide

theorem pw_29 : 2 ^ 4 ≤ 29 ∧ 29 < 2 ^ 5 ∧ 4 * 4 < 29 := by decide

/-- The least missing positive integer from the orbit of 2 mod 29 is 29: `m(29) = 29`. -/
theorem lm_29 : IsLeastMissing 29 29 := ⟨cover_29, not_inOrbit_self (by decide)⟩

/-- Discrete-log witnesses for q = 37: entry j equals n with 2^n ≡ j+1 (mod 37). -/
def dlogs_37 : List Nat := [0, 1, 26, 2, 23, 27, 32, 3, 16, 24, 30, 28, 11, 33, 13, 4,
  7, 17, 35, 25, 22, 31, 15, 29, 10, 12, 6, 34, 21, 14, 9, 5,
  20, 8, 19, 18]

theorem dlog_ok_37 : dlogOk 37 dlogs_37 0 = true := by decide

theorem dl_len_37 : dlogs_37.length = 36 := by decide

/-- Every `1 ≤ k < 37` occurs in the orbit `{2^n mod 37}`. -/
theorem cover_37 : ∀ k, 1 ≤ k → k < 37 → InOrbit 37 k := by
  intro k hk1 hk2
  exact dlogOk_implies dlogs_37 0 dlog_ok_37 k hk1 (by rw [dl_len_37]; exact Nat.le_of_lt_succ hk2)

/-- Certificate that 2 is a primitive root mod 37: Fermat plus `2^((q-1)/f) ≠ 1`
for each prime f ∣ q-1 (q-1 = 2 · 3). -/
theorem pr_37 : 2 ^ 36 % 37 = 1 ∧ 2 ^ 18 % 37 = 36 ∧ 2 ^ 12 % 37 = 26 := by decide

theorem pw_37 : 2 ^ 5 ≤ 37 ∧ 37 < 2 ^ 6 ∧ 5 * 5 < 37 := by decide

/-- The least missing positive integer from the orbit of 2 mod 37 is 37: `m(37) = 37`. -/
theorem lm_37 : IsLeastMissing 37 37 := ⟨cover_37, not_inOrbit_self (by decide)⟩

/-- Discrete-log witnesses for q = 53: entry j equals n with 2^n ≡ j+1 (mod 53). -/
def dlogs_53 : List Nat := [0, 1, 17, 2, 47, 18, 14, 3, 34, 48, 6, 19, 24, 15, 12, 4,
  10, 35, 37, 49, 31, 7, 39, 20, 42, 25, 51, 16, 46, 13, 33, 5,
  23, 11, 9, 36, 30, 38, 41, 50, 45, 32, 22, 8, 29, 40, 44, 21,
  28, 43, 27, 26]

theorem dlog_ok_53 : dlogOk 53 dlogs_53 0 = true := by decide

theorem dl_len_53 : dlogs_53.length = 52 := by decide

/-- Every `1 ≤ k < 53` occurs in the orbit `{2^n mod 53}`. -/
theorem cover_53 : ∀ k, 1 ≤ k → k < 53 → InOrbit 53 k := by
  intro k hk1 hk2
  exact dlogOk_implies dlogs_53 0 dlog_ok_53 k hk1 (by rw [dl_len_53]; exact Nat.le_of_lt_succ hk2)

/-- Certificate that 2 is a primitive root mod 53: Fermat plus `2^((q-1)/f) ≠ 1`
for each prime f ∣ q-1 (q-1 = 2 · 13). -/
theorem pr_53 : 2 ^ 52 % 53 = 1 ∧ 2 ^ 26 % 53 = 52 ∧ 2 ^ 4 % 53 = 16 := by decide

theorem pw_53 : 2 ^ 5 ≤ 53 ∧ 53 < 2 ^ 6 ∧ 5 * 5 < 53 := by decide

/-- The least missing positive integer from the orbit of 2 mod 53 is 53: `m(53) = 53`. -/
theorem lm_53 : IsLeastMissing 53 53 := ⟨cover_53, not_inOrbit_self (by decide)⟩

/-- Discrete-log witnesses for q = 59: entry j equals n with 2^n ≡ j+1 (mod 59). -/
def dlogs_59 : List Nat := [0, 1, 50, 2, 6, 51, 18, 3, 42, 7, 25, 52, 45, 19, 56, 4,
  40, 43, 38, 8, 10, 26, 15, 53, 12, 46, 34, 20, 28, 57, 49, 5,
  17, 41, 24, 44, 55, 39, 37, 9, 14, 11, 33, 27, 48, 16, 23, 54,
  36, 13, 32, 47, 22, 35, 31, 21, 30, 29]

theorem dlog_ok_59 : dlogOk 59 dlogs_59 0 = true := by decide

theorem dl_len_59 : dlogs_59.length = 58 := by decide

/-- Every `1 ≤ k < 59` occurs in the orbit `{2^n mod 59}`. -/
theorem cover_59 : ∀ k, 1 ≤ k → k < 59 → InOrbit 59 k := by
  intro k hk1 hk2
  exact dlogOk_implies dlogs_59 0 dlog_ok_59 k hk1 (by rw [dl_len_59]; exact Nat.le_of_lt_succ hk2)

/-- Certificate that 2 is a primitive root mod 59: Fermat plus `2^((q-1)/f) ≠ 1`
for each prime f ∣ q-1 (q-1 = 2 · 29). -/
theorem pr_59 : 2 ^ 58 % 59 = 1 ∧ 2 ^ 29 % 59 = 58 ∧ 2 ^ 2 % 59 = 4 := by decide

theorem pw_59 : 2 ^ 5 ≤ 59 ∧ 59 < 2 ^ 6 ∧ 5 * 5 < 59 := by decide

/-- The least missing positive integer from the orbit of 2 mod 59 is 59: `m(59) = 59`. -/
theorem lm_59 : IsLeastMissing 59 59 := ⟨cover_59, not_inOrbit_self (by decide)⟩

/-- Discrete-log witnesses for q = 61: entry j equals n with 2^n ≡ j+1 (mod 61). -/
def dlogs_61 : List Nat := [0, 1, 6, 2, 22, 7, 49, 3, 12, 23, 15, 8, 40, 50, 28, 4,
  47, 13, 26, 24, 55, 16, 57, 9, 44, 41, 18, 51, 35, 29, 59, 5,
  21, 48, 11, 14, 39, 27, 46, 25, 54, 56, 43, 17, 34, 58, 20, 10,
  38, 45, 53, 42, 33, 19, 37, 52, 32, 36, 31, 30]

theorem dlog_ok_61 : dlogOk 61 dlogs_61 0 = true := by decide

theorem dl_len_61 : dlogs_61.length = 60 := by decide

/-- Every `1 ≤ k < 61` occurs in the orbit `{2^n mod 61}`. -/
theorem cover_61 : ∀ k, 1 ≤ k → k < 61 → InOrbit 61 k := by
  intro k hk1 hk2
  exact dlogOk_implies dlogs_61 0 dlog_ok_61 k hk1 (by rw [dl_len_61]; exact Nat.le_of_lt_succ hk2)

/-- Certificate that 2 is a primitive root mod 61: Fermat plus `2^((q-1)/f) ≠ 1`
for each prime f ∣ q-1 (q-1 = 2 · 3 · 5). -/
theorem pr_61 : 2 ^ 60 % 61 = 1 ∧ 2 ^ 30 % 61 = 60 ∧ 2 ^ 20 % 61 = 47 ∧ 2 ^ 12 % 61 = 9 := by decide

theorem pw_61 : 2 ^ 5 ≤ 61 ∧ 61 < 2 ^ 6 ∧ 5 * 5 < 61 := by decide

/-- The least missing positive integer from the orbit of 2 mod 61 is 61: `m(61) = 61`. -/
theorem lm_61 : IsLeastMissing 61 61 := ⟨cover_61, not_inOrbit_self (by decide)⟩

/-- Discrete-log witnesses for q = 67: entry j equals n with 2^n ≡ j+1 (mod 67). -/
def dlogs_67 : List Nat := [0, 1, 39, 2, 15, 40, 23, 3, 12, 16, 59, 41, 19, 24, 54, 4,
  64, 13, 10, 17, 62, 60, 28, 42, 30, 20, 51, 25, 44, 55, 47, 5,
  32, 65, 38, 14, 22, 11, 58, 18, 53, 63, 9, 61, 27, 29, 50, 43,
  46, 31, 37, 21, 57, 52, 8, 26, 49, 45, 36, 56, 7, 48, 35, 6,
  34, 33]

theorem dlog_ok_67 : dlogOk 67 dlogs_67 0 = true := by decide

theorem dl_len_67 : dlogs_67.length = 66 := by decide

/-- Every `1 ≤ k < 67` occurs in the orbit `{2^n mod 67}`. -/
theorem cover_67 : ∀ k, 1 ≤ k → k < 67 → InOrbit 67 k := by
  intro k hk1 hk2
  exact dlogOk_implies dlogs_67 0 dlog_ok_67 k hk1 (by rw [dl_len_67]; exact Nat.le_of_lt_succ hk2)

/-- Certificate that 2 is a primitive root mod 67: Fermat plus `2^((q-1)/f) ≠ 1`
for each prime f ∣ q-1 (q-1 = 2 · 3 · 11). -/
theorem pr_67 : 2 ^ 66 % 67 = 1 ∧ 2 ^ 33 % 67 = 66 ∧ 2 ^ 22 % 67 = 37 ∧ 2 ^ 6 % 67 = 64 := by decide

theorem pw_67 : 2 ^ 6 ≤ 67 ∧ 67 < 2 ^ 7 ∧ 6 * 6 < 67 := by decide

/-- The least missing positive integer from the orbit of 2 mod 67 is 67: `m(67) = 67`. -/
theorem lm_67 : IsLeastMissing 67 67 := ⟨cover_67, not_inOrbit_self (by decide)⟩

/-- Discrete-log witnesses for q = 83: entry j equals n with 2^n ≡ j+1 (mod 83). -/
def dlogs_83 : List Nat := [0, 1, 72, 2, 27, 73, 8, 3, 62, 28, 24, 74, 77, 9, 17, 4,
  56, 63, 47, 29, 80, 25, 60, 75, 54, 78, 52, 10, 12, 18, 38, 5,
  14, 57, 35, 64, 20, 48, 67, 30, 40, 81, 71, 26, 7, 61, 23, 76,
  16, 55, 46, 79, 59, 53, 51, 11, 37, 13, 34, 19, 66, 39, 70, 6,
  22, 15, 45, 58, 50, 36, 33, 65, 69, 21, 44, 49, 32, 68, 43, 31,
  42, 41]

theorem dlog_ok_83 : dlogOk 83 dlogs_83 0 = true := by decide

theorem dl_len_83 : dlogs_83.length = 82 := by decide

/-- Every `1 ≤ k < 83` occurs in the orbit `{2^n mod 83}`. -/
theorem cover_83 : ∀ k, 1 ≤ k → k < 83 → InOrbit 83 k := by
  intro k hk1 hk2
  exact dlogOk_implies dlogs_83 0 dlog_ok_83 k hk1 (by rw [dl_len_83]; exact Nat.le_of_lt_succ hk2)

/-- Certificate that 2 is a primitive root mod 83: Fermat plus `2^((q-1)/f) ≠ 1`
for each prime f ∣ q-1 (q-1 = 2 · 41). -/
theorem pr_83 : 2 ^ 82 % 83 = 1 ∧ 2 ^ 41 % 83 = 82 ∧ 2 ^ 2 % 83 = 4 := by decide

theorem pw_83 : 2 ^ 6 ≤ 83 ∧ 83 < 2 ^ 7 ∧ 6 * 6 < 83 := by decide

/-- The least missing positive integer from the orbit of 2 mod 83 is 83: `m(83) = 83`. -/
theorem lm_83 : IsLeastMissing 83 83 := ⟨cover_83, not_inOrbit_self (by decide)⟩

/-- Discrete-log witnesses for q = 101: entry j equals n with 2^n ≡ j+1 (mod 101). -/
def dlogs_101 : List Nat := [0, 1, 69, 2, 24, 70, 9, 3, 38, 25, 13, 71, 66, 10, 93, 4,
  30, 39, 96, 26, 78, 14, 86, 72, 48, 67, 7, 11, 91, 94, 84, 5,
  82, 31, 33, 40, 56, 97, 35, 27, 45, 79, 42, 15, 62, 87, 58, 73,
  18, 49, 99, 68, 23, 8, 37, 12, 65, 92, 29, 95, 77, 85, 47, 6,
  90, 83, 81, 32, 55, 34, 44, 41, 61, 57, 17, 98, 22, 36, 64, 28,
  76, 46, 89, 80, 54, 43, 60, 16, 21, 63, 75, 88, 53, 59, 20, 74,
  52, 19, 51, 50]

theorem dlog_ok_101 : dlogOk 101 dlogs_101 0 = true := by decide

theorem dl_len_101 : dlogs_101.length = 100 := by decide

/-- Every `1 ≤ k < 101` occurs in the orbit `{2^n mod 101}`. -/
theorem cover_101 : ∀ k, 1 ≤ k → k < 101 → InOrbit 101 k := by
  intro k hk1 hk2
  exact dlogOk_implies dlogs_101 0 dlog_ok_101 k hk1 (by rw [dl_len_101]; exact Nat.le_of_lt_succ hk2)

/-- Certificate that 2 is a primitive root mod 101: Fermat plus `2^((q-1)/f) ≠ 1`
for each prime f ∣ q-1 (q-1 = 2 · 5). -/
theorem pr_101 : 2 ^ 100 % 101 = 1 ∧ 2 ^ 50 % 101 = 100 ∧ 2 ^ 20 % 101 = 95 := by decide

theorem pw_101 : 2 ^ 6 ≤ 101 ∧ 101 < 2 ^ 7 ∧ 6 * 6 < 101 := by decide

/-- The least missing positive integer from the orbit of 2 mod 101 is 101: `m(101) = 101`. -/
theorem lm_101 : IsLeastMissing 101 101 := ⟨cover_101, not_inOrbit_self (by decide)⟩

/-- Discrete-log witnesses for q = 107: entry j equals n with 2^n ≡ j+1 (mod 107). -/
def dlogs_107 : List Nat := [0, 1, 70, 2, 47, 71, 43, 3, 34, 48, 22, 72, 14, 44, 11, 4,
  29, 35, 78, 49, 7, 23, 62, 73, 94, 15, 104, 45, 32, 12, 27, 5,
  92, 30, 90, 36, 38, 79, 84, 50, 40, 8, 59, 24, 81, 63, 66, 74,
  86, 95, 99, 16, 52, 105, 69, 46, 42, 33, 21, 13, 10, 28, 77, 6,
  61, 93, 103, 31, 26, 91, 89, 37, 83, 39, 58, 80, 65, 85, 98, 51,
  68, 41, 20, 9, 76, 60, 102, 25, 88, 82, 57, 64, 97, 67, 19, 75,
  101, 87, 56, 96, 18, 100, 55, 17, 54, 53]

theorem dlog_ok_107 : dlogOk 107 dlogs_107 0 = true := by decide

theorem dl_len_107 : dlogs_107.length = 106 := by decide

/-- Every `1 ≤ k < 107` occurs in the orbit `{2^n mod 107}`. -/
theorem cover_107 : ∀ k, 1 ≤ k → k < 107 → InOrbit 107 k := by
  intro k hk1 hk2
  exact dlogOk_implies dlogs_107 0 dlog_ok_107 k hk1 (by rw [dl_len_107]; exact Nat.le_of_lt_succ hk2)

/-- Certificate that 2 is a primitive root mod 107: Fermat plus `2^((q-1)/f) ≠ 1`
for each prime f ∣ q-1 (q-1 = 2 · 53). -/
theorem pr_107 : 2 ^ 106 % 107 = 1 ∧ 2 ^ 53 % 107 = 106 ∧ 2 ^ 2 % 107 = 4 := by decide

theorem pw_107 : 2 ^ 6 ≤ 107 ∧ 107 < 2 ^ 7 ∧ 6 * 6 < 107 := by decide

/-- The least missing positive integer from the orbit of 2 mod 107 is 107: `m(107) = 107`. -/
theorem lm_107 : IsLeastMissing 107 107 := ⟨cover_107, not_inOrbit_self (by decide)⟩

/-- Discrete-log witnesses for q = 131: entry j equals n with 2^n ≡ j+1 (mod 131). -/
def dlogs_131 : List Nat := [0, 1, 72, 2, 46, 73, 96, 3, 14, 47, 56, 74, 18, 97, 118, 4,
  43, 15, 35, 48, 38, 57, 23, 75, 92, 19, 86, 98, 51, 119, 29, 5,
  128, 44, 12, 16, 41, 36, 90, 49, 126, 39, 124, 58, 60, 24, 105, 76,
  62, 93, 115, 20, 26, 87, 102, 99, 107, 52, 82, 120, 78, 30, 110, 6,
  64, 129, 71, 45, 95, 13, 55, 17, 117, 42, 34, 37, 22, 91, 85, 50,
  28, 127, 11, 40, 89, 125, 123, 59, 104, 61, 114, 25, 101, 106, 81, 77,
  109, 63, 70, 94, 54, 116, 33, 21, 84, 27, 10, 88, 122, 103, 113, 100,
  80, 108, 69, 53, 32, 83, 9, 121, 112, 79, 68, 31, 8, 111, 67, 7,
  66, 65]

theorem dlog_ok_131 : dlogOk 131 dlogs_131 0 = true := by decide

theorem dl_len_131 : dlogs_131.length = 130 := by decide

/-- Every `1 ≤ k < 131` occurs in the orbit `{2^n mod 131}`. -/
theorem cover_131 : ∀ k, 1 ≤ k → k < 131 → InOrbit 131 k := by
  intro k hk1 hk2
  exact dlogOk_implies dlogs_131 0 dlog_ok_131 k hk1 (by rw [dl_len_131]; exact Nat.le_of_lt_succ hk2)

/-- Certificate that 2 is a primitive root mod 131: Fermat plus `2^((q-1)/f) ≠ 1`
for each prime f ∣ q-1 (q-1 = 2 · 5 · 13). -/
theorem pr_131 : 2 ^ 130 % 131 = 1 ∧ 2 ^ 65 % 131 = 130 ∧ 2 ^ 26 % 131 = 53 ∧ 2 ^ 10 % 131 = 107 := by decide

theorem pw_131 : 2 ^ 7 ≤ 131 ∧ 131 < 2 ^ 8 ∧ 7 * 7 < 131 := by decide

/-- The least missing positive integer from the orbit of 2 mod 131 is 131: `m(131) = 131`. -/
theorem lm_131 : IsLeastMissing 131 131 := ⟨cover_131, not_inOrbit_self (by decide)⟩

/-- Discrete-log witnesses for q = 139: entry j equals n with 2^n ≡ j+1 (mod 139). -/
def dlogs_139 : List Nat := [0, 1, 41, 2, 86, 42, 50, 3, 82, 87, 76, 43, 64, 51, 127, 4,
  107, 83, 61, 88, 91, 77, 27, 44, 34, 65, 123, 52, 94, 128, 56, 5,
  117, 108, 136, 84, 80, 62, 105, 89, 32, 92, 115, 78, 30, 28, 98, 45,
  100, 35, 10, 66, 47, 124, 24, 53, 102, 95, 21, 129, 37, 57, 132, 6,
  12, 118, 16, 109, 68, 137, 40, 85, 49, 81, 75, 63, 126, 106, 60, 90,
  26, 33, 122, 93, 55, 116, 135, 79, 104, 31, 114, 29, 97, 99, 9, 46,
  23, 101, 20, 36, 131, 11, 15, 67, 39, 48, 74, 125, 59, 25, 121, 54,
  134, 103, 113, 96, 8, 22, 19, 130, 14, 38, 73, 58, 120, 133, 112, 7,
  18, 13, 72, 119, 111, 17, 71, 110, 70, 69]

theorem dlog_ok_139 : dlogOk 139 dlogs_139 0 = true := by decide

theorem dl_len_139 : dlogs_139.length = 138 := by decide

/-- Every `1 ≤ k < 139` occurs in the orbit `{2^n mod 139}`. -/
theorem cover_139 : ∀ k, 1 ≤ k → k < 139 → InOrbit 139 k := by
  intro k hk1 hk2
  exact dlogOk_implies dlogs_139 0 dlog_ok_139 k hk1 (by rw [dl_len_139]; exact Nat.le_of_lt_succ hk2)

/-- Certificate that 2 is a primitive root mod 139: Fermat plus `2^((q-1)/f) ≠ 1`
for each prime f ∣ q-1 (q-1 = 2 · 3 · 23). -/
theorem pr_139 : 2 ^ 138 % 139 = 1 ∧ 2 ^ 69 % 139 = 138 ∧ 2 ^ 46 % 139 = 96 ∧ 2 ^ 6 % 139 = 64 := by decide

theorem pw_139 : 2 ^ 7 ≤ 139 ∧ 139 < 2 ^ 8 ∧ 7 * 7 < 139 := by decide

/-- The least missing positive integer from the orbit of 2 mod 139 is 139: `m(139) = 139`. -/
theorem lm_139 : IsLeastMissing 139 139 := ⟨cover_139, not_inOrbit_self (by decide)⟩

/-- Discrete-log witnesses for q = 149: entry j equals n with 2^n ≡ j+1 (mod 149). -/
def dlogs_149 : List Nat := [0, 1, 87, 2, 104, 88, 142, 3, 26, 105, 109, 89, 53, 143, 43, 4,
  124, 27, 84, 106, 81, 110, 95, 90, 60, 54, 113, 144, 120, 44, 132, 5,
  48, 125, 98, 28, 72, 85, 140, 107, 41, 82, 93, 111, 130, 96, 138, 91,
  136, 61, 63, 55, 18, 114, 65, 145, 23, 121, 57, 45, 38, 133, 20, 6,
  9, 49, 116, 126, 34, 99, 67, 29, 12, 73, 147, 86, 103, 141, 25, 108,
  52, 42, 123, 83, 80, 94, 59, 112, 119, 131, 47, 97, 71, 139, 40, 92,
  129, 137, 135, 62, 17, 64, 22, 56, 37, 19, 8, 115, 33, 66, 11, 146,
  102, 24, 51, 122, 79, 58, 118, 46, 70, 39, 128, 134, 16, 21, 36, 7,
  32, 10, 101, 50, 78, 117, 69, 127, 15, 35, 31, 100, 77, 68, 14, 30,
  76, 13, 75, 74]

theorem dlog_ok_149 : dlogOk 149 dlogs_149 0 = true := by decide

theorem dl_len_149 : dlogs_149.length = 148 := by decide

/-- Every `1 ≤ k < 149` occurs in the orbit `{2^n mod 149}`. -/
theorem cover_149 : ∀ k, 1 ≤ k → k < 149 → InOrbit 149 k := by
  intro k hk1 hk2
  exact dlogOk_implies dlogs_149 0 dlog_ok_149 k hk1 (by rw [dl_len_149]; exact Nat.le_of_lt_succ hk2)

/-- Certificate that 2 is a primitive root mod 149: Fermat plus `2^((q-1)/f) ≠ 1`
for each prime f ∣ q-1 (q-1 = 2 · 37). -/
theorem pr_149 : 2 ^ 148 % 149 = 1 ∧ 2 ^ 74 % 149 = 148 ∧ 2 ^ 4 % 149 = 16 := by decide

theorem pw_149 : 2 ^ 7 ≤ 149 ∧ 149 < 2 ^ 8 ∧ 7 * 7 < 149 := by decide

/-- The least missing positive integer from the orbit of 2 mod 149 is 149: `m(149) = 149`. -/
theorem lm_149 : IsLeastMissing 149 149 := ⟨cover_149, not_inOrbit_self (by decide)⟩

/-- Discrete-log witnesses for q = 163: entry j equals n with 2^n ≡ j+1 (mod 163). -/
def dlogs_163 : List Nat := [0, 1, 101, 2, 15, 102, 73, 3, 40, 16, 47, 103, 51, 74, 116, 4,
  57, 41, 125, 17, 12, 48, 9, 104, 30, 52, 141, 75, 107, 117, 69, 5,
  148, 58, 88, 42, 33, 126, 152, 18, 160, 13, 38, 49, 55, 10, 28, 105,
  146, 31, 158, 53, 144, 142, 62, 76, 64, 108, 135, 118, 78, 70, 113, 6,
  66, 149, 25, 59, 110, 89, 92, 43, 137, 34, 131, 127, 120, 153, 95, 19,
  80, 161, 100, 14, 72, 39, 46, 50, 115, 56, 124, 11, 8, 29, 140, 106,
  68, 147, 87, 32, 151, 159, 37, 54, 27, 145, 157, 143, 61, 63, 134, 77,
  112, 65, 24, 109, 91, 136, 130, 119, 94, 79, 99, 71, 45, 114, 123, 7,
  139, 67, 86, 150, 36, 26, 156, 60, 133, 111, 23, 90, 129, 93, 98, 44,
  122, 138, 85, 35, 155, 132, 22, 128, 97, 121, 84, 154, 21, 96, 83, 20,
  82, 81]

theorem dlog_ok_163 : dlogOk 163 dlogs_163 0 = true := by decide

theorem dl_len_163 : dlogs_163.length = 162 := by decide

/-- Every `1 ≤ k < 163` occurs in the orbit `{2^n mod 163}`. -/
theorem cover_163 : ∀ k, 1 ≤ k → k < 163 → InOrbit 163 k := by
  intro k hk1 hk2
  exact dlogOk_implies dlogs_163 0 dlog_ok_163 k hk1 (by rw [dl_len_163]; exact Nat.le_of_lt_succ hk2)

/-- Certificate that 2 is a primitive root mod 163: Fermat plus `2^((q-1)/f) ≠ 1`
for each prime f ∣ q-1 (q-1 = 2 · 3). -/
theorem pr_163 : 2 ^ 162 % 163 = 1 ∧ 2 ^ 81 % 163 = 162 ∧ 2 ^ 54 % 163 = 104 := by decide

theorem pw_163 : 2 ^ 7 ≤ 163 ∧ 163 < 2 ^ 8 ∧ 7 * 7 < 163 := by decide

/-- The least missing positive integer from the orbit of 2 mod 163 is 163: `m(163) = 163`. -/
theorem lm_163 : IsLeastMissing 163 163 := ⟨cover_163, not_inOrbit_self (by decide)⟩

/-- Discrete-log witnesses for q = 173: entry j equals n with 2^n ≡ j+1 (mod 173). -/
def dlogs_173 : List Nat := [0, 1, 27, 2, 39, 28, 95, 3, 54, 40, 23, 29, 130, 96, 66, 4,
  73, 55, 33, 41, 122, 24, 20, 30, 78, 131, 81, 97, 144, 67, 102, 5,
  50, 74, 134, 56, 162, 34, 157, 42, 138, 123, 84, 25, 93, 21, 64, 31,
  18, 79, 100, 132, 155, 82, 62, 98, 60, 145, 147, 68, 13, 103, 149, 6,
  169, 51, 70, 75, 47, 135, 15, 57, 166, 163, 105, 35, 118, 158, 151, 43,
  108, 139, 8, 124, 112, 85, 171, 26, 38, 94, 53, 22, 129, 65, 72, 32,
  121, 19, 77, 80, 143, 101, 49, 133, 161, 156, 137, 83, 92, 63, 17, 99,
  154, 61, 59, 146, 12, 148, 168, 69, 46, 14, 165, 104, 117, 150, 107, 7,
  111, 170, 37, 52, 128, 71, 120, 76, 142, 48, 160, 136, 91, 16, 153, 58,
  11, 167, 45, 164, 116, 106, 110, 36, 127, 119, 141, 159, 90, 152, 10, 44,
  115, 109, 126, 140, 89, 9, 114, 125, 88, 113, 87, 86]

theorem dlog_ok_173 : dlogOk 173 dlogs_173 0 = true := by decide

theorem dl_len_173 : dlogs_173.length = 172 := by decide

/-- Every `1 ≤ k < 173` occurs in the orbit `{2^n mod 173}`. -/
theorem cover_173 : ∀ k, 1 ≤ k → k < 173 → InOrbit 173 k := by
  intro k hk1 hk2
  exact dlogOk_implies dlogs_173 0 dlog_ok_173 k hk1 (by rw [dl_len_173]; exact Nat.le_of_lt_succ hk2)

/-- Certificate that 2 is a primitive root mod 173: Fermat plus `2^((q-1)/f) ≠ 1`
for each prime f ∣ q-1 (q-1 = 2 · 43). -/
theorem pr_173 : 2 ^ 172 % 173 = 1 ∧ 2 ^ 86 % 173 = 172 ∧ 2 ^ 4 % 173 = 16 := by decide

theorem pw_173 : 2 ^ 7 ≤ 173 ∧ 173 < 2 ^ 8 ∧ 7 * 7 < 173 := by decide

/-- The least missing positive integer from the orbit of 2 mod 173 is 173: `m(173) = 173`. -/
theorem lm_173 : IsLeastMissing 173 173 := ⟨cover_173, not_inOrbit_self (by decide)⟩

/-- Discrete-log witnesses for q = 179: entry j equals n with 2^n ≡ j+1 (mod 179). -/
def dlogs_179 : List Nat := [0, 1, 108, 2, 138, 109, 171, 3, 38, 139, 15, 110, 114, 172, 68, 4,
  166, 39, 54, 140, 101, 16, 135, 111, 98, 115, 146, 173, 118, 69, 62, 5,
  123, 167, 131, 40, 149, 55, 44, 141, 155, 102, 80, 17, 176, 136, 36, 112,
  164, 99, 96, 116, 121, 147, 153, 174, 162, 119, 160, 70, 72, 63, 31, 6,
  74, 124, 86, 168, 65, 132, 59, 41, 33, 150, 28, 56, 8, 45, 11, 142,
  76, 156, 24, 103, 126, 81, 48, 18, 88, 177, 107, 137, 170, 37, 14, 113,
  67, 165, 53, 100, 134, 97, 145, 117, 61, 122, 130, 148, 43, 154, 79, 175,
  35, 163, 95, 120, 152, 161, 159, 71, 30, 73, 85, 64, 58, 32, 27, 7,
  10, 75, 23, 125, 47, 87, 106, 169, 13, 66, 52, 133, 144, 60, 129, 42,
  78, 34, 94, 151, 158, 29, 84, 57, 26, 9, 22, 46, 105, 12, 51, 143,
  128, 77, 93, 157, 83, 25, 21, 104, 50, 127, 92, 82, 20, 49, 91, 19,
  90, 89]

theorem dlog_ok_179 : dlogOk 179 dlogs_179 0 = true := by decide

theorem dl_len_179 : dlogs_179.length = 178 := by decide

/-- Every `1 ≤ k < 179` occurs in the orbit `{2^n mod 179}`. -/
theorem cover_179 : ∀ k, 1 ≤ k → k < 179 → InOrbit 179 k := by
  intro k hk1 hk2
  exact dlogOk_implies dlogs_179 0 dlog_ok_179 k hk1 (by rw [dl_len_179]; exact Nat.le_of_lt_succ hk2)

/-- Certificate that 2 is a primitive root mod 179: Fermat plus `2^((q-1)/f) ≠ 1`
for each prime f ∣ q-1 (q-1 = 2 · 89). -/
theorem pr_179 : 2 ^ 178 % 179 = 1 ∧ 2 ^ 89 % 179 = 178 ∧ 2 ^ 2 % 179 = 4 := by decide

theorem pw_179 : 2 ^ 7 ≤ 179 ∧ 179 < 2 ^ 8 ∧ 7 * 7 < 179 := by decide

/-- The least missing positive integer from the orbit of 2 mod 179 is 179: `m(179) = 179`. -/
theorem lm_179 : IsLeastMissing 179 179 := ⟨cover_179, not_inOrbit_self (by decide)⟩

/-- Discrete-log witnesses for q = 181: entry j equals n with 2^n ≡ j+1 (mod 181). -/
def dlogs_181 : List Nat := [0, 1, 56, 2, 156, 57, 15, 3, 112, 157, 62, 58, 164, 16, 32, 4,
  175, 113, 135, 158, 71, 63, 53, 59, 132, 165, 168, 17, 48, 33, 99, 5,
  118, 176, 171, 114, 26, 136, 40, 159, 83, 72, 20, 64, 88, 54, 13, 60,
  30, 133, 51, 166, 97, 169, 38, 18, 11, 49, 36, 34, 125, 100, 127, 6,
  140, 119, 102, 177, 109, 172, 129, 115, 80, 27, 8, 137, 77, 41, 142, 160,
  44, 84, 121, 73, 151, 21, 104, 65, 145, 89, 179, 55, 155, 14, 111, 61,
  163, 31, 174, 134, 70, 52, 131, 167, 47, 98, 117, 170, 25, 39, 82, 19,
  87, 12, 29, 50, 96, 37, 10, 35, 124, 126, 139, 101, 108, 128, 79, 7,
  76, 141, 43, 120, 150, 103, 144, 178, 154, 110, 162, 173, 69, 130, 46, 116,
  24, 81, 86, 28, 95, 9, 123, 138, 107, 78, 75, 42, 149, 143, 153, 161,
  68, 45, 23, 85, 94, 122, 106, 74, 148, 152, 67, 22, 93, 105, 147, 66,
  92, 146, 91, 90]

theorem dlog_ok_181 : dlogOk 181 dlogs_181 0 = true := by decide

theorem dl_len_181 : dlogs_181.length = 180 := by decide

/-- Every `1 ≤ k < 181` occurs in the orbit `{2^n mod 181}`. -/
theorem cover_181 : ∀ k, 1 ≤ k → k < 181 → InOrbit 181 k := by
  intro k hk1 hk2
  exact dlogOk_implies dlogs_181 0 dlog_ok_181 k hk1 (by rw [dl_len_181]; exact Nat.le_of_lt_succ hk2)

/-- Certificate that 2 is a primitive root mod 181: Fermat plus `2^((q-1)/f) ≠ 1`
for each prime f ∣ q-1 (q-1 = 2 · 3 · 5). -/
theorem pr_181 : 2 ^ 180 % 181 = 1 ∧ 2 ^ 90 % 181 = 180 ∧ 2 ^ 60 % 181 = 48 ∧ 2 ^ 36 % 181 = 59 := by decide

theorem pw_181 : 2 ^ 7 ≤ 181 ∧ 181 < 2 ^ 8 ∧ 7 * 7 < 181 := by decide

/-- The least missing positive integer from the orbit of 2 mod 181 is 181: `m(181) = 181`. -/
theorem lm_181 : IsLeastMissing 181 181 := ⟨cover_181, not_inOrbit_self (by decide)⟩

/-- Discrete-log witnesses for q = 197: entry j equals n with 2^n ≡ j+1 (mod 197). -/
def dlogs_197 : List Nat := [0, 1, 181, 2, 89, 182, 146, 3, 166, 90, 29, 183, 25, 147, 74, 4,
  159, 167, 154, 91, 131, 30, 120, 184, 178, 26, 151, 148, 36, 75, 141, 5,
  14, 160, 39, 168, 192, 155, 10, 92, 110, 132, 78, 31, 59, 121, 66, 185,
  96, 179, 144, 27, 72, 152, 118, 149, 139, 37, 8, 76, 64, 142, 116, 6,
  114, 15, 17, 161, 105, 40, 19, 169, 45, 193, 163, 156, 175, 11, 107, 93,
  136, 111, 42, 133, 52, 79, 21, 32, 55, 60, 171, 122, 126, 67, 47, 186,
  82, 97, 195, 180, 88, 145, 165, 28, 24, 73, 158, 153, 130, 119, 177, 150,
  35, 140, 13, 38, 191, 9, 109, 77, 58, 65, 95, 143, 71, 117, 138, 7,
  63, 115, 113, 16, 104, 18, 44, 162, 174, 106, 135, 41, 51, 20, 54, 170,
  125, 46, 81, 194, 87, 164, 23, 157, 129, 176, 34, 12, 190, 108, 57, 94,
  70, 137, 62, 112, 103, 43, 173, 134, 50, 53, 124, 80, 86, 22, 128, 33,
  189, 56, 69, 61, 102, 172, 49, 123, 85, 127, 188, 68, 101, 48, 84, 187,
  100, 83, 99, 98]

theorem dlog_ok_197 : dlogOk 197 dlogs_197 0 = true := by decide

theorem dl_len_197 : dlogs_197.length = 196 := by decide

/-- Every `1 ≤ k < 197` occurs in the orbit `{2^n mod 197}`. -/
theorem cover_197 : ∀ k, 1 ≤ k → k < 197 → InOrbit 197 k := by
  intro k hk1 hk2
  exact dlogOk_implies dlogs_197 0 dlog_ok_197 k hk1 (by rw [dl_len_197]; exact Nat.le_of_lt_succ hk2)

/-- Certificate that 2 is a primitive root mod 197: Fermat plus `2^((q-1)/f) ≠ 1`
for each prime f ∣ q-1 (q-1 = 2 · 7). -/
theorem pr_197 : 2 ^ 196 % 197 = 1 ∧ 2 ^ 98 % 197 = 196 ∧ 2 ^ 28 % 197 = 104 := by decide

theorem pw_197 : 2 ^ 7 ≤ 197 ∧ 197 < 2 ^ 8 ∧ 7 * 7 < 197 := by decide

/-- The least missing positive integer from the orbit of 2 mod 197 is 197: `m(197) = 197`. -/
theorem lm_197 : IsLeastMissing 197 197 := ⟨cover_197, not_inOrbit_self (by decide)⟩

/-- Flagship spot check from the verification verdict: for q = 101, 2 is a primitive
root, the least missing positive integer is m(101) = 101, and already
`(floor(log2 101))^2 = 36 < 101 = m(101)` (indeed `(ln 101)^2 = 21.29... < 101`). -/
theorem attack_101 :
    IsLeastMissing 101 101
      ∧ 2 ^ 100 % 101 = 1 ∧ 2 ^ 50 % 101 = 100 ∧ 2 ^ 20 % 101 = 95
      ∧ 2 ^ 6 ≤ 101 ∧ 101 < 2 ^ 7 ∧ 6 * 6 < 101 :=
  ⟨lm_101, pr_101.1, pr_101.2.1, pr_101.2.2, pw_101.1, pw_101.2.1, pw_101.2.2⟩

/-- Smallest instance: m(3) = 3 > (ln 3)^2 = 1.20... (verdict spot check q = 3). -/
theorem attack_3 :
    IsLeastMissing 3 3
      ∧ 2 ^ 2 % 3 = 1 ∧ 2 ^ 1 % 3 = 2
      ∧ 2 ^ 1 ≤ 3 ∧ 3 < 2 ^ 2 ∧ 1 * 1 < 3 :=
  ⟨lm_3, pr_3.1, pr_3.2, pw_3.1, pw_3.2.1, pw_3.2.2⟩
