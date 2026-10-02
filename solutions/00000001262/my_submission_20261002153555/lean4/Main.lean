/-!
# Disproof of TLMC conjecture 00000001262

The conjecture asserts that *the abelian complexity of balanced periodic words is
eventually constant, equal to the alphabet size*.

We disprove it with the balanced periodic word `w = (aab)^∞` over the alphabet
`{a, b}` (so the alphabet size is `2`).  Writing `omega n` for the abelian
complexity (the number of distinct Parikh vectors of length-`n` windows), we prove

* `omega_triple`      : `∀ k, omega (3 * k) = 1`     (the universal statement),
* `omega_triple_succ` : `∀ k, omega (3 * k + 1) = 2`,
* `omega_triple_succ2`: `∀ k, omega (3 * k + 2) = 2`,

so `omega` cycles through the values `2, 2, 1` forever.  Since
`omega (3 * k) = 1 ≠ 2` holds at `n = 3k` for arbitrarily large `k`, the
complexity is *not* eventually equal to the alphabet size:

* `not_eventually_two : ¬ (∃ N, ∀ n ≥ N, omega n = 2)`.

The word is genuinely balanced and periodic (argued in `main.tex`, verified in
`reproduce.py`), so it lies squarely inside the scope of the conjecture.

Everything is bare Lean 4 core (toolchain `v4.33.1`, no Mathlib).  The core
library lemmas about `%` (e.g. `Nat.add_mod_left`) depend on `propext`, so the
3-periodicity of the word is developed from scratch by structural recursion
(`cycle`, `ph` below).  `Check.lean` audits that every theorem depends on
**zero axioms** (no `propext`, no `Classical.choice`, no `Quot.sound`) and uses
no `sorry`.
-/

namespace Tlmc1262

/-! ## The 3-phase clock: positions of `w` mod 3, by structural recursion -/

/-- Cyclic successor on the phases `0 → 1 → 2 → 0`. -/
def cycle (p : Nat) : Nat := match p with
  | 0 => 1
  | 1 => 2
  | _ => 0

/-- `ph i` is the phase of position `i`, i.e. `i mod 3`, defined by plain
structural recursion on `i` (no core `%` involved). -/
def ph : Nat → Nat
  | 0 => 0
  | n + 1 => cycle (ph n)

theorem ph_succ (n : Nat) : ph (n + 1) = cycle (ph n) := rfl

/-- The phase clock is 3-periodic. -/
theorem ph_shift3 (n : Nat) : ph (n + 1 + 1 + 1) = ph n := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [ph_succ, ih, ph_succ]

/-! ## The word `w = (aab)^∞` and letter counting in windows -/

/-- `ch i = 1` if the `i`-th letter of `w = (aab)^∞` is `a`, and `0` if it is
`b`: the letter is `b` exactly in phase `2` (positions `2, 5, 8, ...`). -/
def ch (i : Nat) : Nat := if ph i == 2 then 0 else 1

/-- `ch` is 3-periodic: `(aab)` is a cyclic permutation of itself. -/
theorem ch_shift (s : Nat) : ch (s + 1 + 1 + 1) = ch s := by
  unfold ch
  rw [ph_shift3]

/-- `A s n` = number of letters `a` in the length-`n` window of `w` starting at
position `s`.  The Parikh vector of the window is `(A s n, n - A s n)`, so two
windows of the same length have equal Parikh vectors exactly when they have
equal `A`-values.  This reduces abelian complexity to counting distinct
`A`-values. -/
def A : Nat → Nat → Nat
  | _, 0 => 0
  | s, n + 1 => ch s + A (s + 1) n

theorem A_succ (s n : Nat) : A s (n + 1) = ch s + A (s + 1) n := rfl

/-! ## Shifting the window start by three positions changes nothing -/

theorem sum3 (t : Nat) : t + 1 + 1 + 1 = t + 3 := rfl

/-- A length-`n` window starting 3 positions later is a cyclic permutation of
the window starting at `s`, hence has the same letter counts. -/
theorem A_shift3 : ∀ (n s : Nat), A (s + 1 + 1 + 1) n = A s n := by
  intro n
  induction n with
  | zero => intro s; rfl
  | succ m ih =>
    intro s
    rw [A_succ (s + 1 + 1 + 1) m, A_succ s m, ch_shift, ih (s + 1)]

/-- One-step windows specialised to the three residue starts.  For `s = 2` the
window continues at position `3`, so the 3-shift lemma brings it back to `0`. -/
theorem A_step0 (n : Nat) : A 0 (n + 1) = 1 + A 1 n := rfl
theorem A_step1 (n : Nat) : A 1 (n + 1) = 1 + A 2 n := rfl

theorem A_step2 (n : Nat) : A 2 (n + 1) = 0 + A 0 n := by
  rw [A_succ 2 n, A_shift3 n 0]
  rfl

/-- Unfolding a window by three letters: consume `w` at `s`, `s + 1`, `s + 2`,
then recurse at `s + 3`. -/
theorem A3add (s n : Nat) :
    A s (n + 1 + 1 + 1)
      = ch s + (ch (s + 1) + (ch (s + 1 + 1) + A (s + 1 + 1 + 1) n)) := by
  rw [A_succ s (n + 1 + 1), A_succ (s + 1) (n + 1), A_succ (s + 1 + 1) n]

/-- Faithfulness of the definition below, in Euclidean form: from the start
`3 * q + r` (every position is of this form for a unique `r < 3`), a window
sees exactly what the residue-`r` window sees. -/
theorem A_shiftQ : ∀ (q r n : Nat), A (3 * q + r) n = A r n := by
  intro q
  induction q with
  | zero =>
    intro r n
    rw [Nat.mul_zero, Nat.zero_add]
  | succ p ih =>
    intro r n
    show A (3 * p + 3 + r) n = A r n
    rw [Nat.add_assoc (3 * p) 3 r, Nat.add_comm 3 r, ← Nat.add_assoc (3 * p) r 3,
        ← sum3 (3 * p + r), A_shift3 n (3 * p + r), ih r n]

/-! ## Windows of length `3 * k` contain exactly `2 * k` letters `a` -/

theorem A0_triple : ∀ k : Nat, A 0 (3 * k) = 2 * k := by
  intro k
  induction k with
  | zero => rfl
  | succ j ih =>
    show A 0 (3 * j + 3) = 2 * (j + 1)
    rw [← sum3 (3 * j), A3add 0 (3 * j), A_shift3 (3 * j) 0, ih]
    show 1 + (1 + (0 + 2 * j)) = 2 * (j + 1)
    rw [Nat.zero_add, Nat.add_comm 1 (2 * j), ← Nat.add_assoc 1 (2 * j) 1,
        Nat.add_comm 1 (2 * j)]
    rfl

theorem A1_triple : ∀ k : Nat, A 1 (3 * k) = 2 * k := by
  intro k
  induction k with
  | zero => rfl
  | succ j ih =>
    show A 1 (3 * j + 3) = 2 * (j + 1)
    rw [← sum3 (3 * j), A3add 1 (3 * j), A_shift3 (3 * j) 1, ih]
    show 1 + (0 + (1 + 2 * j)) = 2 * (j + 1)
    rw [Nat.zero_add, Nat.add_comm 1 (2 * j), ← Nat.add_assoc 1 (2 * j) 1,
        Nat.add_comm 1 (2 * j)]
    rfl

theorem A2_triple : ∀ k : Nat, A 2 (3 * k) = 2 * k := by
  intro k
  induction k with
  | zero => rfl
  | succ j ih =>
    show A 2 (3 * j + 3) = 2 * (j + 1)
    rw [← sum3 (3 * j), A3add 2 (3 * j), A_shift3 (3 * j) 2, ih]
    show 0 + (1 + (1 + 2 * j)) = 2 * (j + 1)
    rw [Nat.zero_add, Nat.add_comm 1 (2 * j), ← Nat.add_assoc 1 (2 * j) 1,
        Nat.add_comm 1 (2 * j)]
    rfl

/-! ## The abelian complexity of `w` -/

/-- Number of distinct values among `x, y, z`. -/
def distinct3 (x y z : Nat) : Nat :=
  if x = y then (if y = z then 1 else 2)
  else (if x = z then 2 else (if y = z then 2 else 3))

/-- Abelian complexity of `w`: the number of distinct Parikh vectors of
length-`n` windows.  By `A_shiftQ` (with Euclidean division of the start by 3)
the `a`-count of every window occurs at one of the residue starts `0, 1, 2`,
and the `b`-count is determined by the `a`-count, so this is the genuine
abelian complexity. -/
def omega (n : Nat) : Nat := distinct3 (A 0 n) (A 1 n) (A 2 n)

theorem distinct3_refl (x : Nat) : distinct3 x x x = 1 := by
  unfold distinct3
  rw [if_pos (show x = x from rfl), if_pos (show x = x from rfl)]

theorem distinct3_aab (x y : Nat) (h : x ≠ y) : distinct3 x x y = 2 := by
  unfold distinct3
  rw [if_pos (show x = x from rfl), if_neg h]

theorem distinct3_abb (x y : Nat) (h : x ≠ y) : distinct3 x y y = 2 := by
  unfold distinct3
  rw [if_neg h, if_neg h, if_pos (show y = y from rfl)]

theorem one_add_ne (x : Nat) : 1 + x ≠ x := by
  rw [Nat.add_comm 1 x]
  exact Nat.succ_ne_self x

theorem one_add_left_ne (x : Nat) : 1 + (1 + x) ≠ 1 + x := by
  intro he
  rw [Nat.add_comm 1 (1 + x)] at he
  rw [Nat.add_one] at he
  rw [Nat.add_comm 1 x] at he
  rw [Nat.add_one] at he
  exact absurd (Nat.succ.inj he) (Nat.succ_ne_self x)

/-! ## The three residue classes -/

/-- **Main universal statement.**  Every length-`3k` window of `w` is a cyclic
permutation of `(aab)^k`, so all Parikh vectors coincide and `omega (3*k) = 1`,
which is *not* the alphabet size `2`. -/
theorem omega_triple (k : Nat) : omega (3 * k) = 1 := by
  unfold omega
  rw [A0_triple k, A1_triple k, A2_triple k]
  exact distinct3_refl (2 * k)

theorem omega_triple_succ (k : Nat) : omega (3 * k + 1) = 2 := by
  unfold omega
  rw [A_step0 (3 * k), A_step1 (3 * k), A_step2 (3 * k)]
  rw [A1_triple k, A2_triple k, A0_triple k]
  show distinct3 (1 + 2 * k) (1 + 2 * k) (0 + 2 * k) = 2
  rw [Nat.zero_add]
  exact distinct3_aab (1 + 2 * k) (2 * k) (one_add_ne (2 * k))

theorem omega_triple_succ2 (k : Nat) : omega (3 * k + 2) = 2 := by
  unfold omega
  show distinct3 (A 0 (3 * k + 1 + 1)) (A 1 (3 * k + 1 + 1))
      (A 2 (3 * k + 1 + 1)) = 2
  rw [A_step0 (3 * k + 1), A_step1 (3 * k + 1), A_step2 (3 * k + 1)]
  rw [A_step1 (3 * k), A_step2 (3 * k), A_step0 (3 * k)]
  rw [A2_triple k, A0_triple k, A1_triple k]
  rw [Nat.zero_add, Nat.zero_add]
  exact distinct3_abb (1 + (1 + 2 * k)) (1 + 2 * k) (one_add_left_ne (2 * k))

/-- Complete closed form: `omega` cycles through `2, 2, 1` forever. -/
theorem omega_values (k : Nat) :
    omega (3 * k) = 1 ∧ omega (3 * k + 1) = 2 ∧ omega (3 * k + 2) = 2 :=
  ⟨omega_triple k, omega_triple_succ k, omega_triple_succ2 k⟩

/-! ## Sanity anchors on the first values -/

theorem omega_one : omega 1 = 2 := by decide
theorem omega_two : omega 2 = 2 := by decide
theorem omega_three : omega 3 = 1 := by decide

/-! ## The conjecture fails -/

/-- **The conjecture is false.**  There is no point `N` from which the abelian
complexity of the balanced periodic word `(aab)^∞` is constantly `2` (the
alphabet size): taking `n = 3 * (N + 1) ≥ N` forces `omega n = 1`. -/
theorem not_eventually_two : ¬ ∃ N : Nat, ∀ n : Nat, n ≥ N → omega n = 2 := by
  intro h
  apply Exists.elim h
  intro N hN
  have hle : N ≤ 3 * (N + 1) :=
    Nat.le_trans (Nat.le_succ N) (Nat.le_mul_of_pos_left (N + 1) (by decide))
  have h3 := hN (3 * (N + 1)) hle
  rw [omega_triple (N + 1)] at h3
  exact absurd h3 (by decide)

end Tlmc1262
