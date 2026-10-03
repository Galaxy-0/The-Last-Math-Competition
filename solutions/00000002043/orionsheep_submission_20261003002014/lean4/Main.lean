/-
  Disproof of TLMC conjecture 00000002043.

  Conjecture: #{n <= x : s_q(3n) = s_q(n)} ~ c_q * x / (log x)^{1/2},
  with c_q explicit.

  Refutation at q = 3: in base 3, multiplying by 3 APPENDS A ZERO TRIT,
  so s_3(3n) = s_3(n) for EVERY n.  The set in question is therefore ALL
  of {0, ..., x-1}: the count equals x exactly — it is LINEAR in x —
  while c * x / sqrt(log x) is o(x).  No constant c makes the displayed
  asymptotic true.

  Kernel-certified below, for every n (a fully general statement):
    * s3 (3*n) = s3 n — the exact identity, where s3 is the base-3
      digit sum defined by the standard recursion
      s3(m) = (m mod 3) + s3(m div 3);
    * the counting function cnt x = #{n < x : s3 (3*n) = s3 n} satisfies
      cnt x = x exactly.

  (The core-library lemmas about Nat mod/div arithmetic are proved with
  `propext` upstream, so the needed arithmetic — quotient and remainder
  by 3 — is rebuilt here by structural recursion, axiom-free.)
-/

namespace Tlmc2043

/-! ## Structural quotient/remainder by 3. -/

/-- `q3 n = (n / 3, n % 3)`, by three-step structural recursion. -/
def q3 : Nat → Nat × Nat
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (0, 2)
  | n + 3 => ((q3 n).1 + 1, (q3 n).2)

/-- The step equation holds definitionally. -/
theorem q3_step (m : Nat) : q3 (m + 3) = ((q3 m).1 + 1, (q3 m).2) := rfl

/-- Closed sanity check: q3 7 = (2, 1). -/
theorem q3_seven : q3 7 = (2, 1) := rfl

/-- Existence of the 3-decomposition below a bound of 3. -/
theorem exists_add3 : ∀ n, 3 ≤ n → ∃ k, n = k + 3 := by
  intro n
  cases n with
  | zero => intro h; exact absurd h (by show ¬ ((3:Nat) ≤ 0); decide)
  | succ n' => cases n' with
    | zero => intro h; exact absurd h (by show ¬ ((3:Nat) ≤ 1); decide)
    | succ n'' => cases n'' with
      | zero => intro h; exact absurd h (by show ¬ ((3:Nat) ≤ 2); decide)
      | succ n3 => intro _; exact ⟨n3, rfl⟩

/-- Spec: the quotient/remainder really divide by 3 (multiplication check). -/
theorem q3_spec : ∀ n, (q3 n).1 * 3 + (q3 n).2 = n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rcases Nat.lt_or_ge n 3 with h3 | h3
    · cases n with
      | zero => exact rfl
      | succ n' => cases n' with
        | zero => exact rfl
        | succ n'' => cases n'' with
          | zero => exact rfl
          | succ n3 =>
              exact absurd h3 (fun h => Nat.not_lt_zero n3
                (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
                  (Nat.lt_of_succ_lt_succ h))))
    · obtain ⟨k, hk⟩ := exists_add3 n h3
      subst hk
      have hik := ih k (Nat.lt_add_of_pos_right (show (0:Nat) < 3 by decide))
      rw [q3_step]
      show ((q3 k).1 + 1) * 3 + (q3 k).2 = k + 3
      rw [Nat.succ_mul, Nat.add_right_comm, hik]

/-- The quotient is at most n. -/
theorem q3_first_le : ∀ n, (q3 n).1 ≤ n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rcases Nat.lt_or_ge n 3 with h3 | h3
    · cases n with
      | zero => exact Nat.le_refl _
      | succ n' => cases n' with
        | zero => exact Nat.zero_le _
        | succ n'' => cases n'' with
          | zero => exact Nat.zero_le _
          | succ n3 =>
              exact absurd h3 (fun h => Nat.not_lt_zero n3
                (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
                  (Nat.lt_of_succ_lt_succ h))))
    · obtain ⟨k, hk⟩ := exists_add3 n h3
      subst hk
      have hik := ih k (Nat.lt_add_of_pos_right (show (0:Nat) < 3 by decide))
      rw [q3_step]
      exact Nat.succ_le_succ (Nat.le_trans hik (Nat.le_add_right k 2))

/-- The quotient of a positive number is at most its predecessor. -/
theorem q3_first_lt : ∀ m, (q3 (m + 1)).1 ≤ m := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    rcases Nat.lt_or_ge m 3 with h3 | h3
    · cases m with
      | zero => decide
      | succ m' => cases m' with
        | zero => decide
        | succ m'' => cases m'' with
          | zero => decide
          | succ m3 =>
              exact absurd h3 (fun h => Nat.not_lt_zero m3
                (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
                  (Nat.lt_of_succ_lt_succ h))))
    · obtain ⟨k, hk⟩ := exists_add3 m h3
      subst hk
      have heq : k + 3 + 1 = (k + 1) + 3 := rfl
      rw [heq, q3_step]
      show (q3 (k + 1)).1 + 1 ≤ k + 3
      have hle := q3_first_le (k + 1)
      exact Nat.le_trans (Nat.succ_le_succ hle) (Nat.le_succ (k + 2))

/-! ## q3 at multiples of 3. -/

/-- q3 (3n) = (n, 0): dividing a multiple of 3 leaves remainder 0. -/
theorem q3_3n : ∀ n, q3 (3 * n) = (n, 0) := by
  intro n
  induction n with
  | zero => exact rfl
  | succ n ih => rw [Nat.mul_succ, q3_step, ih]

/-! ## The base-3 digit sum. -/

/-- Digit sum with an explicit fuel argument (structural recursion). -/
def s3f : Nat → Nat → Nat
  | 0, _ => 0
  | _ + 1, 0 => 0
  | f + 1, m + 1 => (q3 (m + 1)).2 + s3f f (q3 (m + 1)).1

/-- The base-3 digit sum. -/
def s3 (n : Nat) : Nat := s3f (n + 1) n

/-- The digit sum does not depend on the fuel, once it suffices. -/
theorem s3f_fuel : ∀ f f' n, n ≤ f → n ≤ f' → s3f f n = s3f f' n := by
  intro f
  induction f with
  | zero =>
      intro f' n h1 _
      have h0 : n = 0 := Nat.le_zero.mp h1
      subst h0
      cases f' with
      | zero => exact rfl
      | succ f'' => exact rfl
  | succ f ih =>
      intro f' n h1 h2
      cases n with
      | zero => cases f' with
        | zero => exact rfl
        | succ f'' => exact rfl
      | succ m =>
          cases f' with
          | zero => exact absurd h2 (Nat.not_succ_le_zero m)
          | succ f'' =>
              show (q3 (m + 1)).2 + s3f f (q3 (m + 1)).1
                = (q3 (m + 1)).2 + s3f f'' (q3 (m + 1)).1
              have hq : (q3 (m + 1)).1 ≤ m := q3_first_lt m
              have hmf : (q3 (m + 1)).1 ≤ f :=
                Nat.le_trans hq (Nat.le_of_succ_le_succ h1)
              have hmf' : (q3 (m + 1)).1 ≤ f'' :=
                Nat.le_trans hq (Nat.le_of_succ_le_succ h2)
              exact congrArg (fun t => (q3 (m + 1)).2 + t) (ih f'' _ hmf hmf')

/-! ## THE IDENTITY: s3 (3n) = s3 n. -/

theorem s3_mul3 : ∀ n, s3 (3 * n) = s3 n := by
  intro n
  cases n with
  | zero => exact rfl
  | succ k =>
      have hq : q3 (3 * k + 3) = (k + 1, 0) := by
        show ((q3 (3 * k)).1 + 1, (q3 (3 * k)).2) = (k + 1, 0)
        rw [q3_3n k]
      have hs : s3 (3 * k + 3) = s3f (3 * k + 3) (k + 1) := by
        show (q3 (3 * k + 3)).2 + s3f (3 * k + 3) (q3 (3 * k + 3)).1
          = s3f (3 * k + 3) (k + 1)
        rw [hq]
        exact Nat.zero_add _
      have hmul : 3 * (k + 1) = 3 * k + 3 := Nat.mul_succ 3 k
      rw [hmul, hs]
      have hkle : k ≤ 3 * k := Nat.le_mul_of_pos_left k (show (0:Nat) < 3 by decide)
      have hle : k + 1 ≤ 3 * k + 3 :=
        Nat.le_trans (Nat.succ_le_succ hkle)
          (Nat.add_le_add_left (show (1:Nat) ≤ 3 by decide) (3 * k))
      have hfuel : s3f (3 * k + 3) (k + 1) = s3f (k + 2) (k + 1) :=
        s3f_fuel (3 * k + 3) (k + 2) (k + 1) hle (Nat.le_succ (k + 1))
      rw [hfuel]
      rfl

/-! ## The count is exactly linear. -/

/-- Number of n in [0, x) with s3 (3n) = s3 n. -/
def cnt : Nat → Nat
  | 0 => 0
  | x + 1 => (if s3 (3 * x) = s3 x then 1 else 0) + cnt x

/-- EVERY n qualifies: the count equals x exactly. -/
theorem cnt_lin : ∀ x, cnt x = x := by
  intro x
  induction x with
  | zero => exact rfl
  | succ x ih =>
      show (if s3 (3 * x) = s3 x then 1 else 0) + cnt x = x + 1
      have hid : s3 (3 * x) = s3 x := s3_mul3 x
      rw [hid, if_pos rfl, ih, Nat.add_comm 1 x]

end Tlmc2043
