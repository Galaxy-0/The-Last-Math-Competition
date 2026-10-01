/-!
# Disproof of TLMC conjecture 00000000589

Conjecture: for every 3-generated numerical semigroup `S = <a,b,c>`,

    g(S) <= sqrt(3) * (abc)^(1/3) * (1 + o(1)),

with the constant `sqrt(3)` optimal (Erdos-Graham type), where `g(S)` is the
Frobenius number.

Attack family: `S_n = <n, n+1, n^2 - n - 1>` for `n >= 3`.

Main result (`frob_family`): the Frobenius number of `S_n` is *exactly*
`n^2 - 2n - 1` for every `n >= 3`. Consequently

    g(S_n) / (sqrt(3) * (abc)^(1/3))  ~  n^(2/3) / sqrt(3)  ->  infinity,

so the claimed `sqrt(3)` bound fails (first violated at `n = 6`, ratio 1.2434)
and fails by an unbounded multiplicative factor; no constant can rescue it, so
"`sqrt(3)` is optimal" is false a fortiori.

Since core Lean has no real-number `sqrt` machinery here, violations of the
bound are certified by root-free comparisons: because `3 * sqrt(3) < 5`, the
inequality `5 * abc < g^3` certifies `g > sqrt(3) * (abc)^(1/3)` (all sides
positive). See `cert6`, `cert20`, `cert100`.

Everything below is pure Lean core: no Mathlib, no `sorry`, no `omega`, no
`simp` — and, as `Check.lean` verifies, **no axioms at all**. (The core-Nat
subtraction/division lemmas carry `propext` in this Lean version, so the
truncated-subtraction toolkit is re-derived here from scratch by structural
induction as the `my_*` section.)
-/

/-! ## A small axiom-free `Nat` toolkit -/

/-- Cancellation of a common right summand. -/
theorem my_add_cancel_r {a b k : Nat} (h : a + k = b + k) : a = b := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rw [Nat.add_succ, Nat.add_succ] at h
    exact ih (congrArg Nat.pred h)

/-- Right-associativity swap: `a + b + c = a + c + b`. -/
theorem my_add_right_comm (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_comm b c, ← Nat.add_assoc]

/-- A `≤`-hypothesis unfolds to an additive witness. -/
theorem my_le_exists {m n : Nat} (h : m <= n) : ∃ k : Nat, n = m + k := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | step _ ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨Nat.succ k, ?_⟩
    rw [hk, Nat.add_succ]

/-- Cancellation of a common right summand in `≤`. -/
theorem my_le_of_add_le_add_right {a b c : Nat} (h : a + b <= c + b) : a <= c := by
  rcases Nat.lt_or_ge c a with hlt | hge
  · -- c < a is impossible: it would force succ (c + b) <= c + b
    have hsucc : Nat.succ c <= a := Nat.succ_le_of_lt hlt
    obtain ⟨w, hw⟩ := my_le_exists hsucc    -- a = succ c + w
    have h2 : Nat.succ (c + b) <= a + b := by
      have hrec : forall b : Nat, Nat.succ (c + b) <= Nat.succ ((c + w) + b) := by
        intro b
        induction b with
        | zero => exact Nat.succ_le_succ (Nat.le_add_right c w)
        | succ b ih => exact Nat.succ_le_succ ih
      rw [hw, Nat.succ_add c w, Nat.succ_add (c + w) b]
      exact hrec b
    exact absurd (Nat.le_trans h2 h) (Nat.not_succ_le_self (c + b))
  · exact hge

/-- Cancellation of a common left summand in `≤`. -/
theorem my_le_of_add_le_add_left {a k l : Nat} (h : k + a <= l + a) : k <= l :=
  my_le_of_add_le_add_right h

/-- `(k + m) - m = k`, by induction on `m` (with `k` generalized). -/
theorem my_sub_cancel : forall (m k : Nat), (k + m) - m = k := by
  intro m
  induction m with
  | zero => intro k; rfl
  | succ m ih =>
    intro k
    rw [Nat.add_succ, Nat.sub_succ, ← Nat.succ_add, ih (Nat.succ k), Nat.pred_succ]

/-- `m ≤ n` gives `m + (n - m) = n`. -/
theorem my_add_sub_cancel' {m n : Nat} (h : m <= n) : m + (n - m) = n := by
  obtain ⟨k, hk⟩ := my_le_exists h
  have h2 := my_sub_cancel m k
  rw [Nat.add_comm k m] at h2
  rw [hk, h2]

/-- `(n - m) + m = n`. -/
theorem my_sub_add_cancel {m n : Nat} (h : m <= n) : (n - m) + m = n := by
  rw [Nat.add_comm (n - m) m, my_add_sub_cancel' h]

/-- `n - m - k = n - (m + k)`. -/
theorem my_sub_sub (n m k : Nat) : n - m - k = n - (m + k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    calc n - m - Nat.succ k = Nat.pred (n - m - k) := Nat.sub_succ (n - m) k
      _ = Nat.pred (n - (m + k)) := by rw [ih]
      _ = n - Nat.succ (m + k) := (Nat.sub_succ n (m + k)).symm
      _ = n - (m + Nat.succ k) := by rw [Nat.add_succ]

/-- Subtracting the larger leaves at most the smaller. -/
theorem my_sub_le_sub_left {n m : Nat} (h : n <= m) (k : Nat) : k - m <= k - n := by
  obtain ⟨j, hj⟩ := my_le_exists h
  rw [hj, ← my_sub_sub k n j]
  exact Nat.sub_le (k - n) j

/-- From `a + b ≤ c` we get `a ≤ c - b`. -/
theorem my_le_sub_right_of_add {a b c : Nat} (h : a + b <= c) : a <= c - b := by
  have hbc : b <= c := Nat.le_trans (Nat.le_add_left b a) h
  have h4 : b + (c - b) = c := my_add_sub_cancel' hbc
  have h5 : a + b <= b + (c - b) := by rw [h4]; exact h
  rw [Nat.add_comm b (c - b)] at h5
  exact my_le_of_add_le_add_right h5

/-- Distributivity from the clean `Nat.mul_add`. -/
theorem my_add_mul (a b c : Nat) : (a + b) * c = a * c + b * c := by
  rw [Nat.mul_comm (a + b) c, Nat.mul_add, Nat.mul_comm c a, Nat.mul_comm c b]

/-- `k ≤ m` gives `n + (m - k) = (n + m) - k`. -/
theorem my_add_sub_assoc {k m : Nat} (h : k <= m) (n : Nat) :
    n + (m - k) = (n + m) - k := by
  obtain ⟨j, hj⟩ := my_le_exists h
  rw [hj, Nat.add_comm k j, my_sub_cancel k j, ← Nat.add_assoc,
    my_sub_cancel k (n + j)]

/-- Multiplication by a positive natural is injective. -/
theorem my_mul_cancel {u v n : Nat} (hn : 0 < n) (h : u * n = v * n) : u = v := by
  have h1 : n * u <= n * v := by
    rw [Nat.mul_comm n u, Nat.mul_comm n v]
    exact Nat.le_of_eq h
  have h2 : n * v <= n * u := by
    rw [Nat.mul_comm n v, Nat.mul_comm n u]
    exact Nat.le_of_eq h.symm
  exact Nat.le_antisymm (Nat.le_of_mul_le_mul_left h1 hn)
    (Nat.le_of_mul_le_mul_left h2 hn)

/-- `1 + X = X + 1`. -/
theorem my_one_add (X : Nat) : 1 + X = X + 1 := by
  induction X with
  | zero => rfl
  | succ X ih => exact congrArg Nat.succ ih

/-! ## The attack family -/

/-- `m` is representable as a nonnegative integer combination of `a, b, c`. -/
def Rep (a b c m : Nat) : Prop := exists x y z : Nat, x * a + y * b + z * c = m

/-- `g` is the Frobenius number of `<a,b,c>`: `g` itself is not representable,
and every larger integer is. -/
def IsFrobenius (a b c g : Nat) : Prop := Not (Rep a b c g) /\ forall m, g < m -> Rep a b c m

/-- The "window" identity: for `i + 2 <= n`, the value `n^2 - 2n + i` is
representable by `n` and `n+1` alone (stated additively). -/
theorem window (n i : Nat) (hi : i + 2 <= n) :
    (n - 2 - i) * n + i * (n + 1) + (2 * n - i) = n * n := by
  have h2n : 2 <= n := Nat.le_trans (Nat.le_add_left 2 i) hi
  have hi2n : i <= 2 * n :=
    Nat.le_trans (Nat.le_add_right i 2) (Nat.le_trans hi (by
      have t : n <= n * 2 := Nat.le_mul_of_pos_right n (show (0:Nat) < 2 by decide)
      rwa [Nat.mul_comm] at t))
  have h8 : n * n = (n - 2) * n + 2 * n := by
    calc n * n = (n - 2 + 2) * n := by rw [my_sub_add_cancel h2n]
      _ = (n - 2) * n + 2 * n := my_add_mul _ _ _
  calc (n - 2 - i) * n + i * (n + 1) + (2 * n - i)
      = (n - 2 - i) * n + (i * n + i + (2 * n - i)) := by rw [Nat.mul_succ, Nat.add_assoc]
    _ = (n - 2 - i) * n + (i * n + (i + (2 * n - i))) := by rw [Nat.add_assoc]
    _ = (n - 2 - i) * n + (i * n + 2 * n) := by rw [my_add_sub_cancel' hi2n]
    _ = (n - 2 - i) * n + (i + 2) * n := by rw [← my_add_mul]
    _ = ((n - 2 - i) + (i + 2)) * n := by rw [← my_add_mul]
    _ = (((n - 2 - i) + i) + 2) * n := by rw [Nat.add_assoc]
    _ = ((n - 2) + 2) * n := by rw [my_sub_add_cancel (my_le_sub_right_of_add hi)]
    _ = n * n := by rw [my_sub_add_cancel h2n]

/-- One representation step: from `m` representable, `m + a` is representable
(add one more copy of generator `a`). -/
theorem repr_step (a b c m : Nat) (h : Rep a b c m) : Rep a b c (m + a) := by
  obtain ⟨x, y, z, hx⟩ := h
  refine ⟨x + 1, y, z, ?_⟩
  have hxa : (x + 1) * a = x * a + a := by rw [my_add_mul, Nat.one_mul]
  rw [hxa, ← hx]
  calc (x * a + a) + y * b + z * c
      = x * a + (a + (y * b + z * c)) := by rw [Nat.add_assoc, Nat.add_assoc]
    _ = x * a + ((y * b + z * c) + a) := by rw [Nat.add_comm a (y * b + z * c)]
    _ = x * a + (y * b + (z * c + a)) := by rw [Nat.add_assoc]
    _ = ((x * a + y * b) + z * c) + a :=
      ((Nat.add_assoc (x * a) (y * b) (z * c + a)).symm.trans
        (Nat.add_assoc (x * a + y * b) (z * c) a).symm)

/-- Every point of the form `n^2 - 2n + t` is representable by
`<n, n+1, n^2-n-1>` for `n >= 3`, i.e. everything `>= n^2 - 2n` is
representable. Strong induction on `t`:
window `[n^2-2n, n^2-n-2]` by `window`; the point `n^2-n-1` (i.e. `t = n-1`)
equals the third generator; for `t >= n` peel off one `n` and use the
induction hypothesis. -/
theorem repr_shifted (n : Nat) (hn : 3 <= n) :
    forall t : Nat, Rep n (n + 1) (n * n - n - 1) (n * n - 2 * n + t) := by
  intro t
  induction t using Nat.strongRecOn with
  | _ t ih =>
    have hn1 : 1 <= n := Nat.le_trans (show (1:Nat) <= 3 by decide) hn
    have h2n : 2 <= n := Nat.le_trans (show (2:Nat) <= 3 by decide) hn
    have npos : 0 < n := Nat.lt_of_lt_of_le (show (0:Nat) < 3 by decide) hn
    have hAn : n * n - 2 * n + 2 * n = n * n := by
      rw [Nat.add_comm]
      exact my_add_sub_cancel' (Nat.mul_le_mul h2n (Nat.le_refl n))
    rcases Nat.lt_or_ge n (t + 2) with hgt | hle
    · -- n < t + 2: either t = n - 1 (the third generator itself) or t >= n (peel)
      rcases Nat.lt_or_ge t n with hlt | hgen
      · -- t = n - 1, so the point is n^2 - n - 1, exactly the third generator
        have h4 : n + 1 <= t + 2 := Nat.succ_le_of_lt hgt
        have h5 : n <= t + 1 := Nat.le_of_succ_le_succ h4
        have h6 : n - 1 <= t := Nat.pred_le_pred h5
        have h7t : t <= n - 1 := Nat.pred_le_pred (Nat.succ_le_of_lt hlt)
        have hteq : t = n - 1 := Nat.le_antisymm h7t h6
        have hnd : n <= n * n := Nat.le_mul_of_pos_right n npos
        have hAn2 : (n * n - 2 * n) + n = n * n - n :=
          my_add_cancel_r (k := n) (by
            rw [Nat.add_assoc, ← Nat.two_mul, hAn, Nat.add_comm (n * n - n) n,
              my_add_sub_cancel' hnd])
        have hAn1 : (n * n - 2 * n) + (n - 1) = n * n - n - 1 := by
          rw [my_add_sub_assoc hn1 (n * n - 2 * n), hAn2]
        rw [hteq, hAn1]
        exact ⟨0, 0, 1, by rw [Nat.zero_mul, Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add]⟩
      · -- t >= n: peel off one copy of n
        have htpos : 0 < t := Nat.lt_of_lt_of_le npos hgen
        have ih' := ih (t - n) (Nat.sub_lt htpos npos)
        have ht : (n * n - 2 * n) + t = ((n * n - 2 * n) + (t - n)) + n := by
          conv => lhs; rw [← my_add_sub_cancel' hgen]
          rw [Nat.add_comm n (t - n), ← Nat.add_assoc]
        rw [ht]
        exact repr_step n (n + 1) (n * n - n - 1) ((n * n - 2 * n) + (t - n)) ih'
    · -- t + 2 <= n: window case
      have hin : t <= n := Nat.le_trans (my_le_sub_right_of_add hle) (Nat.sub_le n 2)
      have hn2 : n <= 2 * n := by
        have tt : n <= n * 2 := Nat.le_mul_of_pos_right n (show (0:Nat) < 2 by decide)
        rwa [Nat.mul_comm] at tt
      have hle2n : t <= 2 * n := Nat.le_trans hin hn2
      refine ⟨n - 2 - t, t, 0, ?_⟩
      have hw := window n t hle
      have hp : ((n * n - 2 * n) + t) + (2 * n - t) = n * n := by
        rw [Nat.add_assoc, my_add_sub_cancel' hle2n]
        exact hAn
      have hW : (n - 2 - t) * n + t * (n + 1) = (n * n - 2 * n) + t :=
        my_add_cancel_r (k := 2 * n - t) (by rw [hw, hp])
      rw [Nat.zero_mul, Nat.add_zero]
      exact hW

/-- Every `m >= n^2 - 2n` is representable by `<n, n+1, n^2-n-1>` (n >= 3). -/
theorem repr_ge (n : Nat) (hn : 3 <= n) :
    forall m, n * n - 2 * n <= m -> Rep n (n + 1) (n * n - n - 1) m := by
  intro m hm
  have hmA : (n * n - 2 * n) + (m - (n * n - 2 * n)) = m := my_add_sub_cancel' hm
  rw [← hmA]
  exact repr_shifted n hn (m - (n * n - 2 * n))

/-- The Frobenius candidate `n^2 - 2n - 1` is NOT representable by
`<n, n+1, n^2-n-1>` (n >= 3).

If `z >= 1` the combination already reaches `n^2 - n - 1 > n^2 - 2n - 1`.
If `z = 0`, write `x*n + y*(n+1) = (x+y)*n + y`. If `y < n-1`, cancelling `y`
against `(x+y)*n = (n-3)*n + succ j` with `succ j <= n-1` forces `n <= succ j`
— absurd; hence `y >= n-1`, while `y <= x+y <= n-3` follows from
`(x+y)*n = n^2 - 2n - 1 - y <= (n-3)*n` — a contradiction. -/
theorem notrepr (n : Nat) (hn : 3 <= n) :
    Not (Rep n (n + 1) (n * n - n - 1) (n * n - 2 * n - 1)) := by
  rintro ⟨x, y, z, h⟩
  have hn1 : 1 <= n := Nat.le_trans (show (1:Nat) <= 3 by decide) hn
  have npos : 0 < n := Nat.lt_of_lt_of_le (show (0:Nat) < 3 by decide) hn
  have h2n : 2 <= n := Nat.le_trans (show (2:Nat) <= 3 by decide) hn
  have h3n : 3 * n <= n * n := Nat.mul_le_mul hn (Nat.le_refl n)
  have hAn : n * n - 2 * n + 2 * n = n * n := by
    rw [Nat.add_comm]
    exact my_add_sub_cancel' (Nat.mul_le_mul h2n (Nat.le_refl n))
  have e3 : 3 * n = 2 * n + n := Nat.succ_mul 2 n
  have q : 2 * n + 1 <= 3 * n := by
    calc 2 * n + 1 <= 2 * n + n := Nat.add_le_add_left hn1 (2 * n)
      _ = 3 * n := e3.symm
  have h7 : n * n = (n - 3) * n + 3 * n := by
    calc n * n = (n - 3 + 3) * n := by rw [my_sub_add_cancel hn]
      _ = (n - 3) * n + 3 * n := my_add_mul _ _ _
  have hsplit : n * n - 2 * n - 1 = (n - 3) * n + (n - 1) := by
    have c1 : (n - 1) + (2 * n + 1) = 3 * n := by
      calc (n - 1) + (2 * n + 1) = ((n - 1) + 1) + 2 * n := by
            rw [Nat.add_comm (2 * n) 1, ← Nat.add_assoc]
        _ = n + 2 * n := by rw [my_sub_add_cancel hn1]
        _ = 3 * n := by rw [Nat.add_comm n (2 * n), e3]
    have k1 : (n * n - 2 * n - 1) + (2 * n + 1) = n * n := by
      rw [Nat.add_comm]
      exact my_add_sub_cancel' (Nat.le_trans q h3n)
    have k2 : ((n - 3) * n + (n - 1)) + (2 * n + 1) = n * n := by
      rw [Nat.add_assoc, c1, h7]
    exact my_add_cancel_r (k := 2 * n + 1) (by rw [k1, k2])
  by_cases hz : z = 0
  · subst hz
    rw [Nat.zero_mul, Nat.mul_succ, Nat.add_zero] at h
    -- h : x * n + (y * n + y) = n * n - 2 * n - 1
    have huB : (x + y) * n + y = (n - 3) * n + (n - 1) := by
      rw [my_add_mul, Nat.add_assoc, ← hsplit]
      exact h
    by_cases hyn : n - 1 <= y
    · -- y >= n - 1: force (x+y)*n <= (n-3)*n, then y <= n-3 < n-1 <= y
      obtain ⟨j, hjy⟩ := my_le_exists hyn    -- y = (n - 1) + j
      have hcomb : ((x + y) * n + (n - 1)) + j = (n - 3) * n + (n - 1) := by
        rw [Nat.add_assoc, ← hjy, huB]
      have hle : (x + y) * n + (n - 1) <= (n - 3) * n + (n - 1) := by
        have h3 : (x + y) * n + (n - 1) <= ((x + y) * n + (n - 1)) + j :=
          Nat.le_add_right _ _
        rw [hcomb] at h3
        exact Nat.le_trans h3 (Nat.le_refl _)
      have hNle : (x + y) * n <= (n - 3) * n := my_le_of_add_le_add_right hle
      have hcomm : n * (x + y) <= n * (n - 3) := by
        rw [Nat.mul_comm n (x + y), Nat.mul_comm n (n - 3)]
        exact hNle
      have hule : x + y <= n - 3 := Nat.le_of_mul_le_mul_left hcomm npos
      have huy : y <= x + y := Nat.le_add_left y x
      have hle1 : n - 1 <= n - 3 := Nat.le_trans (Nat.le_trans hyn huy) hule
      have hrw : n - 3 + 2 = n - 1 := by
        have hss : n - 1 - 2 = n - 3 := my_sub_sub n 1 2
        rw [← hss, Nat.add_comm (n - 1 - 2) 2]
        exact my_add_sub_cancel' (Nat.sub_le_sub_right hn 1)
      have hfin : (n - 1) + 2 <= n - 1 := by
        calc (n - 1) + 2 <= n - 3 + 2 := Nat.add_le_add_right hle1 2
          _ = n - 1 := hrw
      have hbad : Nat.succ (n - 1) <= n - 1 := by
        calc Nat.succ (n - 1) = (n - 1) + 1 := rfl
          _ <= (n - 1) + 2 := Nat.add_le_add_left (show (1:Nat) <= 2 by decide) (n - 1)
          _ <= n - 1 := hfin
      exact absurd hbad (Nat.not_succ_le_self (n - 1))
    · -- y < n - 1: impossible
      have hynlt : y < n - 1 := Nat.not_le.mp hyn
      have hlt : Nat.succ y <= n - 1 := Nat.succ_le_of_lt hynlt
      obtain ⟨j, hj⟩ := my_le_exists hlt    -- n - 1 = succ y + j
      rw [hj, Nat.succ_add y j, ← Nat.add_succ y j, ← Nat.add_assoc,
        my_add_right_comm ((n - 3) * n) y (Nat.succ j)] at huB
      -- huB : (x+y)*n = ((n-3)*n + succ j) + y
      have huC : (x + y) * n = (n - 3) * n + Nat.succ j := my_add_cancel_r huB
      rcases Nat.lt_or_ge (x + y) (n - 2) with hltU | hgeU
      · -- x + y <= n - 3: then (x+y)*n <= (n-3)*n, forcing succ j <= 0
        have hs : Nat.succ (x + y) <= n - 2 := Nat.succ_le_of_lt hltU
        have hshift := Nat.add_le_add_right hs 2   -- succ (x+y) + 2 <= (n-2) + 2
        have hstep : (n - 2) + 2 = n :=
          my_sub_add_cancel (Nat.le_trans (show (2:Nat) <= 3 by decide) hn)
        have h4 : (x + y) + 3 <= n := by
          have hle := Nat.le_trans (show (x + y) + 3 <= Nat.succ (x + y) + 2 from
            Nat.le_refl _) hshift
          rwa [hstep] at hle
        have hUlt : (x + y) <= n - 3 := my_le_sub_right_of_add h4
        have hUB : (n - 3) * n + Nat.succ j <= (n - 3) * n + 0 := by
          rw [Nat.add_zero, ← huC]
          exact Nat.mul_le_mul hUlt (Nat.le_refl n)
        have hUB' : Nat.succ j + ((n - 3) * n) <= 0 + ((n - 3) * n) := by
          rw [Nat.add_comm (Nat.succ j) ((n - 3) * n), Nat.add_comm 0 ((n - 3) * n)]
          exact hUB
        exact absurd (my_le_of_add_le_add_right hUB') (Nat.not_succ_le_zero j)
      · -- x + y >= n - 2: then (x+y)*n >= (n-2)*n = (n-3)*n + n, so n <= succ j,
        -- but also succ j <= n - 1
        have hge2 : (n - 2) * n <= (x + y) * n := Nat.mul_le_mul hgeU (Nat.le_refl n)
        have hBn : (n - 2) * n = (n - 3) * n + n := by
          have h1n2 : 1 <= n - 2 := Nat.sub_le_sub_right hn 2
          have hstep : (n - 2) - 1 + 1 = n - 2 := my_sub_add_cancel h1n2
          have hss : (n - 2) - 1 = n - 3 := my_sub_sub n 2 1
          calc (n - 2) * n = ((n - 2) - 1 + 1) * n := by rw [hstep]
            _ = ((n - 2) - 1) * n + n := Nat.succ_mul ((n - 2) - 1) n
            _ = (n - 3) * n + n := by rw [hss]
        have hs1 : (n - 3) * n + n <= (n - 3) * n + Nat.succ j := by
          rw [← hBn, ← huC]
          exact hge2
        have hs1c : n + (n - 3) * n <= Nat.succ j + (n - 3) * n := by
          rw [Nat.add_comm n ((n - 3) * n), Nat.add_comm (Nat.succ j) ((n - 3) * n)]
          exact hs1
        have hs2 : n <= Nat.succ j := my_le_of_add_le_add_right hs1c
        have hsj : Nat.succ j <= n - 1 := by
          rw [hj, ← ((Nat.add_succ y j).symm.trans (Nat.succ_add y j).symm)]
          exact Nat.le_add_left _ _
        have hle2 : n <= n - 1 := Nat.le_trans hs2 hsj
        have hbad2 : Nat.succ n <= n := by
          calc Nat.succ n = n + 1 := rfl
            _ <= (n - 1) + 1 := Nat.add_le_add_right hle2 1
            _ = n := my_sub_add_cancel hn1
        exact absurd hbad2 (Nat.not_succ_le_self n)
  · -- z >= 1: the combination is already too big
    have hz1 : 0 < z := Nat.pos_of_ne_zero hz
    have hc1 : n * n - n - 1 <= z * (n * n - n - 1) := by
      rw [Nat.mul_comm z (n * n - n - 1)]
      exact Nat.le_mul_of_pos_right _ hz1
    have hc2 : z * (n * n - n - 1) <= n * n - 2 * n - 1 := by
      rw [← h]
      exact Nat.le_add_left _ _
    have e5 : 1 <= n * n - 2 * n :=
      my_le_sub_right_of_add (by
        have h22 : 2 * n + 2 <= 3 * n := by
          calc 2 * n + 2 <= 2 * n + n :=
              Nat.add_le_add_left (Nat.le_trans (show (2:Nat) <= 3 by decide) hn) (2 * n)
            _ = 3 * n := e3.symm
        have hconv : 1 + 2 * n = 2 * n + 1 := Nat.add_comm 1 (2 * n)
        rw [hconv]
        calc 2 * n + 1 <= 2 * n + 2 :=
            Nat.add_le_add_left (show (1:Nat) <= 2 by decide) (2 * n)
          _ <= 3 * n := h22
          _ <= n * n := h3n)
    have hc3 : n * n - 2 * n - 1 < n * n - n - 1 :=
      Nat.lt_of_succ_le (by
        show n * n - 2 * n - 1 + 1 <= n * n - n - 1
        rw [Nat.add_comm (n * n - 2 * n - 1) 1, my_add_sub_cancel' e5, my_sub_sub]
        exact my_sub_le_sub_left (show n + 1 <= 2 * n from
          Nat.le_trans (Nat.add_le_add_left hn1 n) (Nat.le_of_eq (Nat.two_mul n).symm))
          (n * n))
    exact absurd (Nat.lt_of_le_of_lt (Nat.le_trans hc1 hc2) hc3) (Nat.lt_irrefl (n * n - n - 1))

/-- `n^2 - 2n - 1 + 1 = n^2 - 2n` (used to unpack strict inequality). -/
theorem frobN_succ (n : Nat) (hn : 3 <= n) :
    n * n - 2 * n - 1 + 1 = n * n - 2 * n := by
  have h3n : 3 * n <= n * n := Nat.mul_le_mul hn (Nat.le_refl n)
  have h22 : 2 * n + 2 <= 3 * n := by
    calc 2 * n + 2 <= 2 * n + n :=
        Nat.add_le_add_left (Nat.le_trans (show (2:Nat) <= 3 by decide) hn) (2 * n)
      _ = 3 * n := (Nat.succ_mul 2 n).symm
  have h1led : 1 + 2 * n <= n * n := by
    calc 1 + 2 * n = 2 * n + 1 := by rw [Nat.add_comm]
      _ <= 2 * n + 2 := Nat.add_le_add_left (show (1:Nat) <= 2 by decide) (2 * n)
      _ <= 3 * n := h22
      _ <= n * n := h3n
  rw [Nat.add_comm (n * n - 2 * n - 1) 1]
  exact my_add_sub_cancel' (my_le_sub_right_of_add h1led)

/-- **Main theorem.** For every `n >= 3`, the Frobenius number of the
3-generated semigroup `<n, n+1, n^2-n-1>` is exactly `n^2 - 2n - 1`.

Since `n^2 - 2n - 1 ~ n^2` while `(abc)^(1/3) ~ n^(4/3)`, the ratio
`g / (sqrt(3) * (abc)^(1/3))` grows like `n^(2/3) / sqrt(3)` and is
unbounded: conjecture 00000000589 is FALSE. -/
theorem frob_family (n : Nat) (hn : 3 <= n) :
    IsFrobenius n (n + 1) (n * n - n - 1) (n * n - 2 * n - 1) :=
  ⟨notrepr n hn, fun m hm => repr_ge n hn m (by
    rw [← frobN_succ n hn]
    exact Nat.succ_le_of_lt hm)⟩

/-! ### Concrete attack instances

The conjectured bound `g <= sqrt(3) * (abc)^(1/3)` is violated from `n = 6`
onwards. Root-free certificates: since `3 * sqrt(3) < 5`, `5 * abc < g^3`
implies `g^3 > 3 * sqrt(3) * abc`, i.e. `g > sqrt(3) * (abc)^(1/3)` for
positive `g, abc`. -/

theorem frob6 : IsFrobenius 6 7 29 23 := frob_family 6 (by decide)
theorem frob20 : IsFrobenius 20 21 379 359 := frob_family 20 (by decide)
theorem frob100 : IsFrobenius 100 101 9899 9799 := frob_family 100 (by decide)

theorem cert6 : 5 * (6 * 7 * 29) < 23 * 23 * 23 := by decide
theorem cert20 : 5 * (20 * 21 * 379) < 359 * 359 * 359 := by decide
theorem cert100 : 5 * (100 * 101 * 9899) < 9799 * 9799 * 9799 := by decide

/-- `n = 6`: `g(<6,7,29>) = 23 > sqrt(3) * (6*7*29)^(1/3) = 18.497...`
(ratio 1.2434). First violation of the conjectured bound. -/
theorem violation6 :
    IsFrobenius 6 7 29 23 /\ 5 * (6 * 7 * 29) < 23 * 23 * 23 := ⟨frob6, cert6⟩

/-- `n = 20`: `g(<20,21,379>) = 359 > sqrt(3) * (20*21*379)^(1/3) = 93.869...`
(ratio 3.8245). -/
theorem violation20 :
    IsFrobenius 20 21 379 359 /\ 5 * (20 * 21 * 379) < 359 * 359 * 359 := ⟨frob20, cert20⟩

/-- `n = 100`: `g(<100,101,9899>) = 9799 > sqrt(3) * (100*101*9899)^(1/3)`
(ratio 12.19). The ratio diverges with `n` by `frob_family`. -/
theorem violation100 :
    IsFrobenius 100 101 9899 9799 /\ 5 * (100 * 101 * 9899) < 9799 * 9799 * 9799 :=
  ⟨frob100, cert100⟩
