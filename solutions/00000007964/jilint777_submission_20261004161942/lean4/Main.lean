/-!
# Conjecture 00000007964 — binary linear quasi-perfect codes exist for (almost) every length

The conjecture contains the clause

  "binary linear quasi-perfect codes of length `n` exist if and only if `n` is of type `2^k - 1`
   or in a finite exceptional list (the Levenshtein set)".

The conjecture's preamble defines quasi-perfect codes as codes with covering radius `e + 1`
("r+1") having a *tight uniform shell distribution*.  We treat two readings:
* standard: covering radius = packing radius + 1, `ρ = e + 1` with `e = ⌊(d-1)/2⌋` (`IsQP`);
* the conjecture's own: `IsQP` plus `ShellUniform` (any two words at the same distance from the
  code have equinumerous shells of every radius, via explicit bijections) (`UQPLen`).
Everything below is built from scratch in Lean 4 core:
words are `List Bool`, codes are predicates, `IsLinear` is "F₂-subspace of F₂ⁿ", `MinDist`
and `CovRad` are the usual minimum distance and covering radius (attained values).

Results:
* `SH_quasiPerfect`  — shortened Hamming codes: for every `n ≥ 3` with `n + 1 ≠ 2^k`,
  a `[n, ·, 3]` linear code with covering radius 2 (quasi-perfect, `e = 1`).
* `EH_quasiPerfect`  — extended Hamming codes of length `2^m` (`m ≥ 2`): `d = 4`, covering radius 2.
* `EW_quasiPerfect`  — even-weight codes of every length `n ≥ 2`: `d = 2`, covering radius 1.
* `hamming_not_QP`   — sanity check: the Hamming codes (length `2^m - 1`) are perfect, not QP.
* `QP_spectrum`      — binary linear QP codes of length `n` exist **iff `n ≥ 2`**.
* `conjecture_00000007964_false : ¬ LevenshteinClause` — the clause is false; and
  `onlyIf3_false`, `onlyIf4_false`, `onlyIfWeak_false`, `onlyIf_any_false`,
  `levenshteinAtLeast_false` refute even the one-directional / `d ≥ 3` / `d ≥ 4` / non-strict variants.
* `EW_shellUniform`, `UQP_spectrum : UQPLen n ↔ 2 ≤ n`,
  `conjecture_00000007964_false_uniform : ¬ LevenshteinClauseUniform` and `onlyIfUniform_false` —
  the same refutation for the conjecture's uniform-shell notion; `SH5_not_shellUniform` shows that
  `ShellUniform` is a genuine restriction.
-/

/-! ## Binary words -/

/-- Hamming weight. -/
def wt : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + wt bs

/-- Coordinatewise sum over `F₂`. -/
def xorW : List Bool → List Bool → List Bool
  | a :: as, b :: bs => (a != b) :: xorW as bs
  | _, _ => []

/-- Hamming distance. -/
def dist (x y : List Bool) : Nat := wt (xorW x y)

def zeroW (n : Nat) : List Bool := List.replicate n false

/-- Syndrome: XOR of the labels `i, i+1, …` of the positions carrying a `1`. -/
def synd : Nat → List Bool → Nat
  | _, [] => 0
  | i, b :: bs => (if b then i else 0) ^^^ synd (i+1) bs

/-- Unit word of length `n` with its `1` at index `j`. -/
def unitW : Nat → Nat → List Bool
  | 0, _ => []
  | n+1, 0 => true :: zeroW n
  | n+1, j+1 => false :: unitW n j

/-! ## Algebra of `xor` on `Nat` -/

theorem xor_swap4 (a b c d : Nat) : (a ^^^ b) ^^^ (c ^^^ d) = (a ^^^ c) ^^^ (b ^^^ d) := by
  apply Nat.eq_of_testBit_eq; intro j
  simp only [Nat.testBit_xor]
  cases a.testBit j <;> cases b.testBit j <;> cases c.testBit j <;> cases d.testBit j <;> rfl

theorem xor_cancel_left (a b : Nat) : a ^^^ (a ^^^ b) = b := by
  rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

theorem eq_of_xor_eq_zero {a b : Nat} (h : a ^^^ b = 0) : a = b := by
  apply Nat.eq_of_testBit_eq; intro j
  have := congrArg (fun t => Nat.testBit t j) h
  simp only [Nat.testBit_xor, Nat.zero_testBit] at this
  revert this; cases a.testBit j <;> cases b.testBit j <;> simp

/-- If `2^k ≤ s < 2^(k+1)` then `s ⊕ 2^k < 2^k`. -/
theorem xor_top_lt {k s : Nat} (h1 : 2^k ≤ s) (h2 : s < 2^(k+1)) : s ^^^ 2^k < 2^k := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  rw [Nat.testBit_xor]
  rcases Nat.eq_or_lt_of_le hj with h | h
  · subst h
    have hdiv : s / 2^k = 1 :=
      Nat.div_eq_of_lt_le (by omega) (by rw [Nat.pow_succ] at h2; omega)
    have hb : s.testBit k = true := by
      have := Nat.testBit_div_two_pow (n := k) s 0
      rw [hdiv, Nat.zero_add] at this
      rw [← this]; decide
    rw [hb, Nat.testBit_two_pow_self]; rfl
  · have hs : s.testBit j = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by decide) h))
    have ht : (2^k).testBit j = false := by
      rw [Nat.testBit_two_pow]; simp; omega
    rw [hs, ht]; rfl

/-! ## Basic word lemmas -/

theorem length_zeroW (n : Nat) : (zeroW n).length = n := by simp [zeroW]

theorem wt_zeroW (n : Nat) : wt (zeroW n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [zeroW, List.replicate, wt] at *; exact ih

theorem synd_zeroW (i n : Nat) : synd i (zeroW n) = 0 := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => simp [zeroW, List.replicate, synd] at *; exact ih (i+1)

theorem length_xorW : ∀ (x y : List Bool), x.length = y.length → (xorW x y).length = x.length
  | [], [], _ => rfl
  | _ :: xs, _ :: ys, h => by
      simp [xorW] at *; exact length_xorW xs ys h

theorem xorW_comm : ∀ (x y : List Bool), xorW x y = xorW y x
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | a :: xs, b :: ys => by
      simp only [xorW, xorW_comm xs ys]; cases a <;> cases b <;> rfl

theorem xorW_cancel : ∀ (x y : List Bool), x.length = y.length → xorW x (xorW x y) = y
  | [], [], _ => rfl
  | a :: xs, b :: ys, h => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [xorW, xorW_cancel xs ys h]; cases a <;> cases b <;> rfl

theorem xorW_zeroW : ∀ (x : List Bool), xorW x (zeroW x.length) = x
  | [] => rfl
  | a :: xs => by
      have := xorW_zeroW xs
      simp only [zeroW, List.length_cons, List.replicate] at *
      simp only [xorW, this]; cases a <;> rfl

theorem zeroW_xorW : ∀ (x : List Bool), xorW (zeroW x.length) x = x := by
  intro x; rw [xorW_comm]; exact xorW_zeroW x

theorem eq_of_wt_xorW_zero : ∀ (x y : List Bool), x.length = y.length → wt (xorW x y) = 0 → x = y
  | [], [], _, _ => rfl
  | a :: xs, b :: ys, h, h0 => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [xorW, wt] at h0
      have h1 : wt (xorW xs ys) = 0 := by omega
      have h2 : (a != b) = false := by revert h0; cases (a != b) <;> simp
      rw [eq_of_wt_xorW_zero xs ys h h1]
      cases a <;> cases b <;> simp_all

theorem dist_self (x : List Bool) : dist x x = 0 := by
  induction x with
  | nil => rfl
  | cons a xs ih => simp [dist, xorW, wt] at *; exact ih

theorem synd_xorW : ∀ (i : Nat) (x y : List Bool), x.length = y.length →
    synd i (xorW x y) = synd i x ^^^ synd i y
  | _, [], [], _ => by simp [xorW, synd]
  | i, a :: xs, b :: ys, h => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [xorW, synd, synd_xorW (i+1) xs ys h]
      rw [xor_swap4]
      cases a <;> cases b <;> simp

/-- Parity of a sum. -/
theorem wt_xorW_parity : ∀ (x y : List Bool), x.length = y.length →
    (wt (xorW x y) + wt x + wt y) % 2 = 0
  | [], [], _ => rfl
  | a :: xs, b :: ys, h => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      have := wt_xorW_parity xs ys h
      simp only [xorW, wt]
      cases a <;> cases b <;> simp <;> omega

theorem synd_wt0 : ∀ (i : Nat) (x : List Bool), wt x = 0 → synd i x = 0
  | _, [], _ => rfl
  | i, b :: bs, h => by
      cases b <;> simp [wt, synd] at * <;> exact synd_wt0 (i+1) bs h

theorem synd_wt1 : ∀ (i : Nat) (x : List Bool), wt x = 1 → i ≤ synd i x ∧ synd i x < i + x.length
  | _, [], h => by simp [wt] at h
  | i, b :: bs, h => by
      cases b
      · simp [wt] at h
        have := synd_wt1 (i+1) bs h
        simp [synd]; omega
      · simp [wt] at h
        simp [synd, synd_wt0 (i+1) bs h]

theorem synd_wt2 : ∀ (i : Nat) (x : List Bool), wt x = 2 → synd i x ≠ 0
  | _, [], h => by simp [wt] at h
  | i, b :: bs, h => by
      cases b
      · simp [wt] at h
        simp [synd]; exact synd_wt2 (i+1) bs h
      · simp [wt] at h
        have h1 : wt bs = 1 := by omega
        have := synd_wt1 (i+1) bs h1
        simp only [synd, if_true]
        intro h0
        have := eq_of_xor_eq_zero h0
        omega

theorem synd_lt (m : Nat) : ∀ (i : Nat) (x : List Bool), i + x.length ≤ 2^m → synd i x < 2^m
  | _, [], _ => Nat.two_pow_pos m
  | i, b :: bs, h => by
      simp only [List.length_cons] at h
      have ih := synd_lt m (i+1) bs (by omega)
      simp only [synd]
      apply Nat.xor_lt_two_pow _ ih
      cases b
      · simp; exact Nat.two_pow_pos m
      · simp; omega

theorem length_unitW : ∀ (n j : Nat), (unitW n j).length = n
  | 0, _ => rfl
  | n+1, 0 => by simp [unitW, length_zeroW]
  | n+1, j+1 => by simp [unitW, length_unitW n j]

theorem wt_unitW : ∀ (n j : Nat), j < n → wt (unitW n j) = 1
  | 0, _, h => by omega
  | n+1, 0, _ => by simp [unitW, wt, wt_zeroW]
  | n+1, j+1, h => by simp [unitW, wt]; exact wt_unitW n j (by omega)

theorem synd_unitW : ∀ (i n j : Nat), j < n → synd i (unitW n j) = i + j
  | _, 0, _, h => by omega
  | i, n+1, 0, _ => by simp [unitW, synd, synd_zeroW]
  | i, n+1, j+1, h => by
      simp [unitW, synd]; rw [synd_unitW (i+1) n j (by omega)]; omega

theorem wt_unit_pair : ∀ (n a b : Nat), a < n → b < n → a ≠ b →
    wt (xorW (unitW n a) (unitW n b)) = 2
  | 0, _, _, h, _, _ => by omega
  | n+1, 0, 0, _, _, h => by omega
  | n+1, 0, b+1, _, hb, _ => by
      have := zeroW_xorW (unitW n b)
      rw [length_unitW] at this
      simp [unitW, xorW, wt, this, wt_unitW n b (by omega)]
  | n+1, a+1, 0, ha, _, _ => by
      have := xorW_zeroW (unitW n a)
      rw [length_unitW] at this
      simp [unitW, xorW, wt, this, wt_unitW n a (by omega)]
  | n+1, a+1, b+1, ha, hb, hab => by
      simp [unitW, xorW, wt]; exact wt_unit_pair n a b (by omega) (by omega) (by omega)

/-! ## Codes, minimum distance, covering radius, quasi-perfect codes -/

/-- `C` is a binary linear code of length `n`: a set of words of length `n`
containing `0` and closed under coordinatewise addition (= an `F₂`-subspace of `F₂ⁿ`). -/
def IsLinear (n : Nat) (C : List Bool → Prop) : Prop :=
  (∀ x, C x → x.length = n) ∧ C (zeroW n) ∧ ∀ x y, C x → C y → C (xorW x y)

/-- `d` is the minimum distance of `C` (so `C` has at least two codewords). -/
def MinDist (C : List Bool → Prop) (d : Nat) : Prop :=
  (∀ x y, C x → C y → x ≠ y → d ≤ dist x y) ∧ ∃ x y, C x ∧ C y ∧ x ≠ y ∧ dist x y = d

/-- `r` is the covering radius of `C ⊆ F₂ⁿ`. -/
def CovRad (n : Nat) (C : List Bool → Prop) (r : Nat) : Prop :=
  (∀ x : List Bool, x.length = n → ∃ c, C c ∧ dist x c ≤ r) ∧
  ∃ x : List Bool, x.length = n ∧ ∀ c, C c → r ≤ dist x c

/-- Quasi-perfect binary linear code of length `n`: covering radius = packing radius
`e = ⌊(d-1)/2⌋` plus one. -/
def IsQP (n : Nat) (C : List Bool → Prop) : Prop :=
  IsLinear n C ∧ ∃ d, MinDist C d ∧ CovRad n C ((d - 1) / 2 + 1)

/-- A binary linear quasi-perfect code of length `n` exists. -/
def QPLen (n : Nat) : Prop := ∃ C, IsQP n C

/-- A binary linear quasi-perfect code of length `n` with minimum distance `d ≥ D` exists. -/
def QPLenAtLeast (D n : Nat) : Prop :=
  ∃ C, IsLinear n C ∧ ∃ d, D ≤ d ∧ MinDist C d ∧ CovRad n C ((d - 1) / 2 + 1)

theorem minDist_unique {C : List Bool → Prop} {d d' : Nat} (h : MinDist C d) (h' : MinDist C d') :
    d = d' := by
  obtain ⟨x, y, hx, hy, hxy, hd⟩ := h.2
  obtain ⟨x', y', hx', hy', hxy', hd'⟩ := h'.2
  have := h.1 x' y' hx' hy' hxy'
  have := h'.1 x y hx hy hxy
  omega

theorem covRad_unique {n : Nat} {C : List Bool → Prop} {r r' : Nat} (h : CovRad n C r)
    (h' : CovRad n C r') : r = r' := by
  obtain ⟨x, hx, hfar⟩ := h.2
  obtain ⟨x', hx', hfar'⟩ := h'.2
  obtain ⟨c, hc, hcd⟩ := h'.1 x hx
  obtain ⟨c', hc', hcd'⟩ := h.1 x' hx'
  have := hfar c hc
  have := hfar' c' hc'
  omega

/-- If a code is linear, its distance from `x` to `xorW x y` is `wt y`. -/
theorem dist_xorW_cancel (x y : List Bool) (h : x.length = y.length) : dist x (xorW x y) = wt y := by
  simp only [dist]; rw [xorW_cancel x y h]

/-! ## Family 1: shortened Hamming codes (d = 3), every length n ≥ 3 with n+1 not a power of 2 -/

/-- Shortened Hamming code of length `n`: parity-check columns are the binary expansions
of `1, 2, …, n`. For `n = 2^m - 1` it is the Hamming code. -/
def SH (n : Nat) (x : List Bool) : Prop := x.length = n ∧ synd 1 x = 0

theorem SH_linear (n : Nat) : IsLinear n (SH n) := by
  refine ⟨fun x hx => hx.1, ⟨length_zeroW n, synd_zeroW 1 n⟩, ?_⟩
  intro x y hx hy
  refine ⟨?_, ?_⟩
  · rw [length_xorW x y (by rw [hx.1, hy.1]), hx.1]
  · rw [synd_xorW 1 x y (by rw [hx.1, hy.1]), hx.2, hy.2]; rfl

theorem SH_minDist (n : Nat) (hn : 3 ≤ n) : MinDist (SH n) 3 := by
  refine ⟨?_, ?_⟩
  · intro x y hx hy hxy
    have hl : x.length = y.length := by rw [hx.1, hy.1]
    have hs : synd 1 (xorW x y) = 0 := by rw [synd_xorW 1 x y hl, hx.2, hy.2]; rfl
    simp only [dist]
    have h0 : wt (xorW x y) ≠ 0 := fun h => hxy (eq_of_wt_xorW_zero x y hl h)
    have h1 : wt (xorW x y) ≠ 1 := fun h => by have := synd_wt1 1 _ h; omega
    have h2 : wt (xorW x y) ≠ 2 := fun h => synd_wt2 1 _ h hs
    omega
  · refine ⟨true :: true :: true :: zeroW (n-3), zeroW n, ⟨?_, ?_⟩, SH_linear n |>.2.1, ?_, ?_⟩
    · simp [length_zeroW]; omega
    · simp [synd, synd_zeroW]
    · intro h; have := congrArg (fun l => true ∈ l) h; simp [zeroW] at this
    · have hl : (true :: true :: true :: zeroW (n-3)).length = n := by simp [length_zeroW]; omega
      have := xorW_zeroW (true :: true :: true :: zeroW (n-3))
      rw [hl] at this
      simp only [dist]; rw [this]; simp [wt, wt_zeroW]

/-- Every syndrome `s < 2^(k+1)` is the syndrome of a word of weight `≤ 2`, if `2^k ≤ n`. -/
theorem SH_realize (n k s : Nat) (hk : 2^k ≤ n) (hs : s < 2^(k+1)) :
    ∃ y : List Bool, y.length = n ∧ synd 1 y = s ∧ wt y ≤ 2 := by
  by_cases h0 : s = 0
  · exact ⟨zeroW n, length_zeroW n, by rw [synd_zeroW, h0], by rw [wt_zeroW]; omega⟩
  by_cases h1 : s ≤ n
  · refine ⟨unitW n (s-1), length_unitW n _, ?_, ?_⟩
    · rw [synd_unitW 1 n (s-1) (by omega)]; omega
    · rw [wt_unitW n (s-1) (by omega)]; omega
  · have hb := xor_top_lt (k := k) (s := s) (by omega) hs
    have hb0 : s ^^^ 2^k ≠ 0 := fun h => by have := eq_of_xor_eq_zero h; omega
    have ht : 1 ≤ 2^k := Nat.two_pow_pos k
    refine ⟨xorW (unitW n (2^k - 1)) (unitW n ((s ^^^ 2^k) - 1)), ?_, ?_, ?_⟩
    · rw [length_xorW _ _ (by rw [length_unitW, length_unitW]), length_unitW]
    · rw [synd_xorW 1 _ _ (by rw [length_unitW, length_unitW]),
        synd_unitW 1 n _ (by omega), synd_unitW 1 n _ (by omega)]
      have e1 : 1 + (2^k - 1) = 2^k := by omega
      have e2 : 1 + ((s ^^^ 2^k) - 1) = s ^^^ 2^k := by omega
      rw [e1, e2, Nat.xor_comm s, xor_cancel_left]
    · rw [wt_unit_pair n _ _ (by omega) (by omega) (by omega)]; omega

theorem SH_covRad (n : Nat) (hn : 3 ≤ n) (hpow : ∀ k, n + 1 ≠ 2^k) : CovRad n (SH n) 2 := by
  have hn0 : n ≠ 0 := by omega
  have hk := Nat.log2_self_le hn0
  have hk' : n < 2^(n.log2 + 1) := Nat.lt_log2_self
  refine ⟨?_, ?_⟩
  · intro x hx
    have hs : synd 1 x < 2^(n.log2+1) := synd_lt _ 1 x (by rw [hx]; have := hpow (n.log2+1); omega)
    obtain ⟨y, hyl, hys, hyw⟩ := SH_realize n n.log2 (synd 1 x) hk hs
    have hl : x.length = y.length := by rw [hx, hyl]
    refine ⟨xorW x y, ⟨?_, ?_⟩, ?_⟩
    · rw [length_xorW x y hl, hx]
    · rw [synd_xorW 1 x y hl, hys, Nat.xor_self]
    · rw [dist_xorW_cancel x y hl]; exact hyw
  · have hne := hpow (n.log2 + 1)
    have hpos := Nat.two_pow_pos (n.log2 + 1)
    obtain ⟨x, hxl, hxs, -⟩ := SH_realize n n.log2 (2^(n.log2+1) - 1) hk (by omega)
    refine ⟨x, hxl, ?_⟩
    intro c hc
    have hl : x.length = c.length := by rw [hxl, hc.1]
    have hs : synd 1 (xorW x c) = 2^(n.log2+1) - 1 := by
      rw [synd_xorW 1 x c hl, hxs, hc.2, Nat.xor_zero]
    simp only [dist]
    have h0 : wt (xorW x c) ≠ 0 := fun h => by rw [synd_wt0 1 _ h] at hs; omega
    have h1 : wt (xorW x c) ≠ 1 := fun h => by
      have := synd_wt1 1 _ h; rw [length_xorW x c hl, hxl] at this; omega
    omega

/-- **Main family.** For every `n ≥ 3` such that `n+1` is not a power of two, the shortened
Hamming code `SH n` is a binary linear quasi-perfect code with `d = 3`, `e = 1`, covering radius 2. -/
theorem SH_quasiPerfect (n : Nat) (hn : 3 ≤ n) (hpow : ∀ k, n + 1 ≠ 2^k) :
    IsLinear n (SH n) ∧ MinDist (SH n) 3 ∧ CovRad n (SH n) 2 ∧ IsQP n (SH n) :=
  ⟨SH_linear n, SH_minDist n hn, SH_covRad n hn hpow,
   SH_linear n, 3, SH_minDist n hn, SH_covRad n hn hpow⟩

/-! ## Family 2: extended Hamming codes (d = 4), lengths 2^m, m ≥ 2 -/

/-- Extended Hamming code of length `2^m`: positions labelled `0, 1, …, 2^m - 1`;
a word is a codeword iff the XOR of its labels is `0` and its weight is even. -/
def EH (m : Nat) (x : List Bool) : Prop := x.length = 2^m ∧ synd 0 x = 0 ∧ wt x % 2 = 0

theorem EH_linear (m : Nat) : IsLinear (2^m) (EH m) := by
  refine ⟨fun x hx => hx.1, ⟨length_zeroW _, synd_zeroW 0 _, by rw [wt_zeroW]⟩, ?_⟩
  intro x y hx hy
  have hl : x.length = y.length := by rw [hx.1, hy.1]
  refine ⟨?_, ?_, ?_⟩
  · rw [length_xorW x y hl, hx.1]
  · rw [synd_xorW 0 x y hl, hx.2.1, hy.2.1]; rfl
  · have := wt_xorW_parity x y hl; have := hx.2.2; have := hy.2.2; omega

theorem four_le_two_pow (m : Nat) (hm : 2 ≤ m) : 4 ≤ 2^m := by
  have := Nat.pow_le_pow_right (n := 2) (by decide) hm; simpa using this

theorem EH_minDist (m : Nat) (hm : 2 ≤ m) : MinDist (EH m) 4 := by
  have h4 := four_le_two_pow m hm
  refine ⟨?_, ?_⟩
  · intro x y hx hy hxy
    have hl : x.length = y.length := by rw [hx.1, hy.1]
    have hs : synd 0 (xorW x y) = 0 := by rw [synd_xorW 0 x y hl, hx.2.1, hy.2.1]; rfl
    have hp := wt_xorW_parity x y hl
    have := hx.2.2; have := hy.2.2
    simp only [dist]
    have h0 : wt (xorW x y) ≠ 0 := fun h => hxy (eq_of_wt_xorW_zero x y hl h)
    have h2 : wt (xorW x y) ≠ 2 := fun h => synd_wt2 0 _ h hs
    omega
  · refine ⟨true :: true :: true :: true :: zeroW (2^m-4), zeroW (2^m),
      ⟨?_, ?_, ?_⟩, EH_linear m |>.2.1, ?_, ?_⟩
    · simp [length_zeroW]; omega
    · simp [synd, synd_zeroW]
    · simp [wt, wt_zeroW]
    · intro h; have := congrArg (fun l => true ∈ l) h; simp [zeroW] at this
    · have hl : (true :: true :: true :: true :: zeroW (2^m-4)).length = 2^m := by
        simp [length_zeroW]; omega
      have := xorW_zeroW (true :: true :: true :: true :: zeroW (2^m-4))
      rw [hl] at this
      simp only [dist]; rw [this]; simp [wt, wt_zeroW]

theorem EH_covRad (m : Nat) (hm : 2 ≤ m) : CovRad (2^m) (EH m) 2 := by
  have h4 := four_le_two_pow m hm
  refine ⟨?_, ?_⟩
  · intro x hx
    have hs : synd 0 x < 2^m := synd_lt m 0 x (by omega)
    -- a word `y` of weight ≤ 2 with the same syndrome and the same parity as `x`
    have hy : ∃ y : List Bool, y.length = 2^m ∧ synd 0 y = synd 0 x ∧ wt y % 2 = wt x % 2 ∧ wt y ≤ 2 := by
      by_cases hp : wt x % 2 = 1
      · refine ⟨unitW (2^m) (synd 0 x), length_unitW _ _, ?_, ?_, ?_⟩
        · rw [synd_unitW 0 _ _ hs]; omega
        · rw [wt_unitW _ _ hs]; omega
        · rw [wt_unitW _ _ hs]; omega
      · by_cases h0 : synd 0 x = 0
        · exact ⟨zeroW (2^m), length_zeroW _, by rw [synd_zeroW, h0], by rw [wt_zeroW]; omega,
            by rw [wt_zeroW]; omega⟩
        · refine ⟨xorW (unitW (2^m) 0) (unitW (2^m) (synd 0 x)), ?_, ?_, ?_, ?_⟩
          · rw [length_xorW _ _ (by rw [length_unitW, length_unitW]), length_unitW]
          · rw [synd_xorW 0 _ _ (by rw [length_unitW, length_unitW]),
              synd_unitW 0 _ _ (by omega), synd_unitW 0 _ _ hs]; simp
          · rw [wt_unit_pair _ _ _ (by omega) hs (by omega)]; omega
          · rw [wt_unit_pair _ _ _ (by omega) hs (by omega)]; omega
    obtain ⟨y, hyl, hys, hyp, hyw⟩ := hy
    have hl : x.length = y.length := by rw [hx, hyl]
    refine ⟨xorW x y, ⟨?_, ?_, ?_⟩, ?_⟩
    · rw [length_xorW x y hl, hx]
    · rw [synd_xorW 0 x y hl, hys, Nat.xor_self]
    · have := wt_xorW_parity x y hl; omega
    · rw [dist_xorW_cancel x y hl]; exact hyw
  · refine ⟨xorW (unitW (2^m) 0) (unitW (2^m) 1), ?_, ?_⟩
    · rw [length_xorW _ _ (by rw [length_unitW, length_unitW]), length_unitW]
    · intro c hc
      have hxl : (xorW (unitW (2^m) 0) (unitW (2^m) 1)).length = 2^m := by
        rw [length_xorW _ _ (by rw [length_unitW, length_unitW]), length_unitW]
      have hxs : synd 0 (xorW (unitW (2^m) 0) (unitW (2^m) 1)) = 1 := by
        rw [synd_xorW 0 _ _ (by rw [length_unitW, length_unitW]),
          synd_unitW 0 _ _ (by omega), synd_unitW 0 _ _ (by omega)]; rfl
      have hxw : wt (xorW (unitW (2^m) 0) (unitW (2^m) 1)) = 2 :=
        wt_unit_pair _ _ _ (by omega) (by omega) (by omega)
      generalize xorW (unitW (2^m) 0) (unitW (2^m) 1) = x at hxl hxs hxw
      have hl : x.length = c.length := by rw [hxl, hc.1]
      have hs : synd 0 (xorW x c) = 1 := by rw [synd_xorW 0 x c hl, hxs, hc.2.1]; rfl
      have hp := wt_xorW_parity x c hl
      have := hc.2.2
      simp only [dist]
      have h0 : wt (xorW x c) ≠ 0 := fun h => by rw [synd_wt0 0 _ h] at hs; omega
      omega

/-- **Second family.** For every `m ≥ 2` the extended Hamming code of length `2^m` is a
binary linear quasi-perfect code with `d = 4`, `e = 1`, covering radius 2. -/
theorem EH_quasiPerfect (m : Nat) (hm : 2 ≤ m) :
    IsLinear (2^m) (EH m) ∧ MinDist (EH m) 4 ∧ CovRad (2^m) (EH m) 2 ∧ IsQP (2^m) (EH m) :=
  ⟨EH_linear m, EH_minDist m hm, EH_covRad m hm, EH_linear m, 4, EH_minDist m hm, EH_covRad m hm⟩

/-! ## Family 3: even-weight codes (d = 2), every length n ≥ 2 -/

def EW (n : Nat) (x : List Bool) : Prop := x.length = n ∧ wt x % 2 = 0

theorem EW_linear (n : Nat) : IsLinear n (EW n) := by
  refine ⟨fun x hx => hx.1, ⟨length_zeroW _, by rw [wt_zeroW]⟩, ?_⟩
  intro x y hx hy
  have hl : x.length = y.length := by rw [hx.1, hy.1]
  refine ⟨?_, ?_⟩
  · rw [length_xorW x y hl, hx.1]
  · have := wt_xorW_parity x y hl; have := hx.2; have := hy.2; omega

theorem EW_minDist (n : Nat) (hn : 2 ≤ n) : MinDist (EW n) 2 := by
  refine ⟨?_, ?_⟩
  · intro x y hx hy hxy
    have hl : x.length = y.length := by rw [hx.1, hy.1]
    have hp := wt_xorW_parity x y hl
    have := hx.2; have := hy.2
    simp only [dist]
    have h0 : wt (xorW x y) ≠ 0 := fun h => hxy (eq_of_wt_xorW_zero x y hl h)
    omega
  · refine ⟨true :: true :: zeroW (n-2), zeroW n, ⟨?_, ?_⟩, EW_linear n |>.2.1, ?_, ?_⟩
    · simp [length_zeroW]; omega
    · simp [wt, wt_zeroW]
    · intro h; have := congrArg (fun l => true ∈ l) h; simp [zeroW] at this
    · have hl : (true :: true :: zeroW (n-2)).length = n := by simp [length_zeroW]; omega
      have := xorW_zeroW (true :: true :: zeroW (n-2))
      rw [hl] at this
      simp only [dist]; rw [this]; simp [wt, wt_zeroW]

theorem EW_covRad (n : Nat) (hn : 2 ≤ n) : CovRad n (EW n) 1 := by
  refine ⟨?_, ?_⟩
  · intro x hx
    by_cases hp : wt x % 2 = 0
    · exact ⟨x, ⟨hx, hp⟩, by rw [dist_self]; omega⟩
    · have hl : x.length = (unitW n 0).length := by rw [hx, length_unitW]
      refine ⟨xorW x (unitW n 0), ⟨?_, ?_⟩, ?_⟩
      · rw [length_xorW _ _ hl, hx]
      · have := wt_xorW_parity x _ hl; rw [wt_unitW n 0 (by omega)] at this; omega
      · rw [dist_xorW_cancel x _ hl, wt_unitW n 0 (by omega)]; omega
  · refine ⟨unitW n 0, length_unitW n 0, ?_⟩
    intro c hc
    have hl : (unitW n 0).length = c.length := by rw [length_unitW, hc.1]
    have hp := wt_xorW_parity _ _ hl
    rw [wt_unitW n 0 (by omega)] at hp
    have := hc.2
    simp only [dist]; omega

/-- **Third family.** For every `n ≥ 2` the even-weight code is quasi-perfect (`d = 2`, `e = 0`,
covering radius 1). -/
theorem EW_quasiPerfect (n : Nat) (hn : 2 ≤ n) :
    IsLinear n (EW n) ∧ MinDist (EW n) 2 ∧ CovRad n (EW n) 1 ∧ IsQP n (EW n) :=
  ⟨EW_linear n, EW_minDist n hn, EW_covRad n hn, EW_linear n, 2, EW_minDist n hn, EW_covRad n hn⟩

/-! ## The complete length spectrum: QP codes exist exactly for n ≥ 2 -/

/-- In length `n ≤ 1`, any word of length `n` coincides with one of two distinct words. -/
theorem short_word_cases (n : Nat) (hn : n ≤ 1) (u v w : List Bool) (hu : u.length = n)
    (hv : v.length = n) (hw : w.length = n) (huv : u ≠ v) : w = u ∨ w = v := by
  rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl
  · match u, v, hu, hv with
    | [], [], _, _ => exact absurd rfl huv
  · match u, v, w, hu, hv, hw with
    | [a], [b], [c], _, _, _ =>
        cases a <;> cases b <;> cases c <;> simp_all

theorem no_QP_short (n : Nat) (hn : n ≤ 1) : ¬ QPLen n := by
  rintro ⟨C, hlin, d, hmd, hcov⟩
  obtain ⟨x, y, hx, hy, hxy, -⟩ := hmd.2
  obtain ⟨z, hzl, hz⟩ := hcov.2
  rcases short_word_cases n hn x y z (hlin.1 x hx) (hlin.1 y hy) hzl hxy with h | h
  · have := hz x hx; rw [← h, dist_self] at this; omega
  · have := hz y hy; rw [← h, dist_self] at this; omega

theorem QP_spectrum (n : Nat) : QPLen n ↔ 2 ≤ n := by
  constructor
  · intro h; false_or_by_contra
    exact no_QP_short n (by omega) h
  · intro h; exact ⟨EW n, (EW_quasiPerfect n h).2.2.2⟩

/-! ## The conjecture's length clause and its refutation -/

/-- The conjecture's clause: there is a finite exceptional list `L` (the "Levenshtein set") such that
binary linear quasi-perfect codes of length `n` exist iff `n = 2^k - 1` or `n ∈ L`. -/
def LevenshteinClause : Prop :=
  ∃ L : List Nat, ∀ n, QPLen n ↔ ((∃ k, n + 1 = 2^k) ∨ n ∈ L)

/-- Weakest ("only if") form, restricted to codes with minimum distance `d ≥ D`. -/
def OnlyIfClause (D : Nat) : Prop :=
  ∃ L : List Nat, ∀ n, QPLenAtLeast D n → ((∃ k, n + 1 = 2^k) ∨ n ∈ L)

def listMax : List Nat → Nat
  | [] => 0
  | a :: as => max a (listMax as)

theorem le_listMax : ∀ (L : List Nat) (a : Nat), a ∈ L → a ≤ listMax L
  | [], _, h => by simp at h
  | b :: bs, a, h => by
      simp only [List.mem_cons] at h
      simp only [listMax]
      rcases h with h | h
      · subst h; exact Nat.le_max_left _ _
      · exact Nat.le_trans (le_listMax bs a h) (Nat.le_max_right _ _)

theorem odd_ne_two_pow (n : Nat) (h : n % 2 = 1) (h1 : 1 < n) : ∀ k, n ≠ 2^k := by
  intro k hk
  cases k with
  | zero => simp at hk; omega
  | succ k => rw [Nat.pow_succ] at hk; omega

theorem QPLenAtLeast_SH (n : Nat) (hn : 3 ≤ n) (hpow : ∀ k, n + 1 ≠ 2^k) : QPLenAtLeast 3 n :=
  ⟨SH n, SH_linear n, 3, Nat.le_refl 3, SH_minDist n hn, SH_covRad n hn hpow⟩

theorem QPLenAtLeast_EH (m : Nat) (hm : 2 ≤ m) : QPLenAtLeast 4 (2^m) :=
  ⟨EH m, EH_linear m, 4, Nat.le_refl 4, EH_minDist m hm, EH_covRad m hm⟩

/-- Even with `d ≥ 3` required, the "only if" direction fails for every finite list. -/
theorem onlyIf3_false : ¬ OnlyIfClause 3 := by
  rintro ⟨L, hL⟩
  let n := 2 * (listMax L + 2)
  have hodd : (n + 1) % 2 = 1 := by omega
  have hpow : ∀ k, n + 1 ≠ 2^k := odd_ne_two_pow (n+1) hodd (by omega)
  rcases hL n (QPLenAtLeast_SH n (by omega) hpow) with ⟨k, hk⟩ | hmem
  · exact hpow k hk
  · have := le_listMax L n hmem; omega

/-- Even with `d ≥ 4` (uniformly packed extended Hamming codes) the "only if" direction fails. -/
theorem onlyIf4_false : ¬ OnlyIfClause 4 := by
  rintro ⟨L, hL⟩
  let m := listMax L + 2
  have hm : m < 2^m := Nat.lt_two_pow_self
  have h4 := four_le_two_pow m (by omega)
  have hpow : ∀ k, 2^m + 1 ≠ 2^k := odd_ne_two_pow (2^m+1)
    (by rw [show m = (m - 1) + 1 by omega, Nat.pow_succ]; omega) (by omega)
  rcases hL (2^m) (QPLenAtLeast_EH m (by omega)) with ⟨k, hk⟩ | hmem
  · exact hpow k hk
  · have := le_listMax L _ hmem; omega

/-- With no restriction on `d` the "only if" direction fails as well. -/
theorem onlyIf_any_false : ¬ OnlyIfClause 0 := by
  rintro ⟨L, hL⟩
  exact onlyIf3_false ⟨L, fun n ⟨C, hlin, d, _, hmd, hcov⟩ =>
    hL n ⟨C, hlin, d, Nat.zero_le d, hmd, hcov⟩⟩ |>.elim

/-! ## Sanity check: the Hamming codes are perfect, hence NOT quasi-perfect -/

theorem hamming_covRad (m : Nat) (hm : 2 ≤ m) : CovRad (2^m - 1) (SH (2^m - 1)) 1 := by
  have h4 := four_le_two_pow m hm
  refine ⟨?_, ?_⟩
  · intro x hx
    have hs : synd 1 x < 2^m := synd_lt m 1 x (by omega)
    by_cases h0 : synd 1 x = 0
    · exact ⟨x, ⟨hx, h0⟩, by rw [dist_self]; omega⟩
    · have hl : x.length = (unitW (2^m - 1) (synd 1 x - 1)).length := by rw [hx, length_unitW]
      refine ⟨xorW x (unitW (2^m - 1) (synd 1 x - 1)), ⟨?_, ?_⟩, ?_⟩
      · rw [length_xorW _ _ hl, hx]
      · rw [synd_xorW 1 _ _ hl, synd_unitW 1 _ _ (by omega),
          show 1 + (synd 1 x - 1) = synd 1 x by omega, Nat.xor_self]
      · rw [dist_xorW_cancel _ _ hl, wt_unitW _ _ (by omega)]; omega
  · refine ⟨unitW (2^m - 1) 0, length_unitW _ _, ?_⟩
    intro c hc
    have hl : (unitW (2^m - 1) 0).length = c.length := by rw [length_unitW, hc.1]
    have hs : synd 1 (xorW (unitW (2^m - 1) 0) c) = 1 := by
      rw [synd_xorW 1 _ _ hl, synd_unitW 1 _ _ (by omega), hc.2]; rfl
    simp only [dist]
    have h0 : wt (xorW (unitW (2^m - 1) 0) c) ≠ 0 := fun h => by rw [synd_wt0 1 _ h] at hs; omega
    omega

/-- The Hamming code of length `2^m - 1` (`m ≥ 3`) has `d = 3`, covering radius `1 = e`: it is perfect,
so it is not quasi-perfect. This shows `IsQP` genuinely separates perfect from quasi-perfect codes. -/
theorem hamming_not_QP (m : Nat) (hm : 3 ≤ m) : ¬ IsQP (2^m - 1) (SH (2^m - 1)) := by
  rintro ⟨-, d, hmd, hcov⟩
  have h8 := four_le_two_pow m (by omega)
  have h8' : 8 ≤ 2^m := by
    have := Nat.pow_le_pow_right (n := 2) (by decide) hm; simpa using this
  have hd : d = 3 := minDist_unique hmd (SH_minDist _ (by omega))
  subst hd
  have := covRad_unique hcov (hamming_covRad m (by omega))
  simp at this

/-! ## The conjecture's own notion: quasi-perfect codes with uniform shell distribution -/

/-- `r` is the distance from the word `x` to the code `C`. -/
def DistTo (C : List Bool → Prop) (x : List Bool) (r : Nat) : Prop :=
  (∃ c, C c ∧ dist x c = r) ∧ ∀ c, C c → r ≤ dist x c

/-- Uniform shell distribution (strongest form). Take any two words `x`, `y` of length `n` that are
at the same distance `r` from `C`, and any radius `j`. Then the shells
`{c ∈ C | dist x c = j}` and `{c ∈ C | dist y c = j}` are in explicit bijection: maps `f`, `g`
between them with `g ∘ f = id` and `f ∘ g = id` on the shells. -/
def ShellUniform (n : Nat) (C : List Bool → Prop) : Prop :=
  ∀ x y : List Bool, ∀ r j : Nat, x.length = n → y.length = n → DistTo C x r → DistTo C y r →
    ∃ f g : List Bool → List Bool,
      (∀ c, C c → dist x c = j → C (f c) ∧ dist y (f c) = j) ∧
      (∀ c, C c → dist y c = j → C (g c) ∧ dist x (g c) = j) ∧
      (∀ c, C c → dist x c = j → g (f c) = c) ∧
      (∀ c, C c → dist y c = j → f (g c) = c)

/-- Uniformly-shelled quasi-perfect binary linear code of length `n` exists. -/
def UQPLen (n : Nat) : Prop := ∃ C, IsQP n C ∧ ShellUniform n C

theorem xorW_shift : ∀ (x y c : List Bool), x.length = y.length → c.length = x.length →
    xorW y (xorW c (xorW x y)) = xorW x c
  | [], [], [], _, _ => rfl
  | a :: xs, b :: ys, d :: cs, h1, h2 => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h1 h2
      simp only [xorW, xorW_shift xs ys cs h1 h2]
      cases a <;> cases b <;> cases d <;> rfl

theorem xorW_back : ∀ (x y c : List Bool), x.length = y.length → c.length = x.length →
    xorW (xorW c (xorW x y)) (xorW y x) = c
  | [], [], [], _, _ => rfl
  | a :: xs, b :: ys, d :: cs, h1, h2 => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h1 h2
      simp only [xorW, xorW_back xs ys cs h1 h2]
      cases a <;> cases b <;> cases d <;> rfl

theorem EW_parity_iff (n : Nat) (x : List Bool) (r : Nat) (hx : x.length = n)
    (h : DistTo (EW n) x r) : (wt x % 2 = 0 ↔ r = 0) := by
  constructor
  · intro hp
    have := h.2 x ⟨hx, hp⟩
    rw [dist_self] at this; omega
  · intro hr
    obtain ⟨c, hc, hd⟩ := h.1
    rw [hr] at hd
    have := eq_of_wt_xorW_zero x c (by rw [hx, hc.1]) hd
    rw [this]; exact hc.2

theorem EW_shift (n : Nat) (x y c : List Bool) (hx : x.length = n) (hy : y.length = n)
    (hp : wt x % 2 = wt y % 2) (hc : EW n c) :
    EW n (xorW c (xorW x y)) ∧ dist y (xorW c (xorW x y)) = dist x c := by
  have hxy : x.length = y.length := by rw [hx, hy]
  have hlw : (xorW x y).length = n := by rw [length_xorW x y hxy, hx]
  have hcw : c.length = (xorW x y).length := by rw [hc.1, hlw]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [length_xorW _ _ hcw, hc.1]
  · have h1 := wt_xorW_parity c (xorW x y) hcw
    have h2 := wt_xorW_parity x y hxy
    have := hc.2
    omega
  · simp only [dist]; rw [xorW_shift x y c hxy (by rw [hc.1, hx])]

/-- The even-weight code has a uniform shell distribution (all `n`). -/
theorem EW_shellUniform (n : Nat) : ShellUniform n (EW n) := by
  intro x y r j hx hy hdx hdy
  have ix := EW_parity_iff n x r hx hdx
  have iy := EW_parity_iff n y r hy hdy
  have hp : wt x % 2 = wt y % 2 := by
    by_cases h : r = 0
    · have := ix.2 h; have := iy.2 h; omega
    · have a := (mt ix.1) h; have b := (mt iy.1) h; omega
  have hxy : x.length = y.length := by rw [hx, hy]
  refine ⟨fun c => xorW c (xorW x y), fun c => xorW c (xorW y x), ?_, ?_, ?_, ?_⟩
  · intro c hc hd
    obtain ⟨h1, h2⟩ := EW_shift n x y c hx hy hp hc
    exact ⟨h1, by rw [h2, hd]⟩
  · intro c hc hd
    obtain ⟨h1, h2⟩ := EW_shift n y x c hy hx hp.symm hc
    exact ⟨h1, by rw [h2, hd]⟩
  · intro c hc _
    exact xorW_back x y c hxy (by rw [hc.1, hx])
  · intro c hc _
    exact xorW_back y x c hxy.symm (by rw [hc.1, hy])

/-- Non-vacuity of `ShellUniform`: the quasi-perfect code `SH 5` is NOT shell-uniform.
`e₁` and `e₂` are both at distance 1 from it, but `e₁` has a codeword at distance 5 and `e₂` has none. -/
theorem SH5_not_shellUniform : ¬ ShellUniform 5 (SH 5) := by
  intro h
  have hd1 : ∀ x : List Bool, x.length = 5 → synd 1 x ≠ 0 → wt x = 1 → DistTo (SH 5) x 1 := by
    intro x hx hs hw
    refine ⟨⟨zeroW 5, SH_linear 5 |>.2.1, ?_⟩, ?_⟩
    · have := xorW_zeroW x; rw [hx] at this; simp only [dist]; rw [this, hw]
    · intro c hc
      have : dist x c ≠ 0 := fun h0 => by
        have := eq_of_wt_xorW_zero x c (by rw [hx, hc.1]) h0
        rw [this] at hs; exact hs hc.2
      omega
  obtain ⟨f, -, hf, -, -, -⟩ := h [true, false, false, false, false] [false, true, false, false, false]
    1 5 rfl rfl (hd1 _ rfl (by decide) rfl) (hd1 _ rfl (by decide) rfl)
  obtain ⟨hmem, hdist⟩ := hf [false, true, true, true, true] ⟨rfl, by decide⟩ (by decide)
  have key : ∀ a b c d e : Bool, synd 1 [a, b, c, d, e] = 0 →
      dist [false, true, false, false, false] [a, b, c, d, e] ≠ 5 := by decide
  have hl := hmem.1
  match hw : f [false, true, true, true, true], hl with
  | [a, b, c, d, e], _ => rw [hw] at hmem hdist; exact key a b c d e hmem.2 hdist

theorem UQP_spectrum (n : Nat) : UQPLen n ↔ 2 ≤ n := by
  constructor
  · rintro ⟨C, hqp, -⟩
    exact (QP_spectrum n).1 ⟨C, hqp⟩
  · intro h; exact ⟨EW n, (EW_quasiPerfect n h).2.2.2, EW_shellUniform n⟩

/-- The clause with the conjecture's own (uniform-shell) notion of quasi-perfect code. -/
def LevenshteinClauseUniform : Prop :=
  ∃ L : List Nat, ∀ n, UQPLen n ↔ ((∃ k, n + 1 = 2^k) ∨ n ∈ L)

def OnlyIfClauseUniform : Prop :=
  ∃ L : List Nat, ∀ n, UQPLen n → ((∃ k, n + 1 = 2^k) ∨ n ∈ L)

theorem onlyIfUniform_false : ¬ OnlyIfClauseUniform := by
  rintro ⟨L, hL⟩
  let n := 2 * (listMax L + 2)
  have hpow : ∀ k, n + 1 ≠ 2^k := odd_ne_two_pow (n+1) (by omega) (by omega)
  rcases hL n ((UQP_spectrum n).2 (by omega)) with ⟨k, hk⟩ | hmem
  · exact hpow k hk
  · have := le_listMax L n hmem; omega

/-- **Main theorem, uniform-shell reading.** -/
theorem conjecture_00000007964_false_uniform : ¬ LevenshteinClauseUniform := by
  rintro ⟨L, hL⟩
  exact onlyIfUniform_false ⟨L, fun n h => (hL n).1 h⟩

/-- The `iff` clause restricted to codes with minimum distance `d ≥ D`. -/
def LevenshteinClauseAtLeast (D : Nat) : Prop :=
  ∃ L : List Nat, ∀ n, QPLenAtLeast D n ↔ ((∃ k, n + 1 = 2^k) ∨ n ∈ L)

/-- Non-strict reading ("covering radius at most `e + 1`", perfect codes allowed). -/
def QPLenWeak (n : Nat) : Prop :=
  ∃ C, IsLinear n C ∧ ∃ d r, MinDist C d ∧ r ≤ (d - 1) / 2 + 1 ∧ CovRad n C r

def OnlyIfClauseWeak : Prop :=
  ∃ L : List Nat, ∀ n, QPLenWeak n → ((∃ k, n + 1 = 2^k) ∨ n ∈ L)

theorem onlyIfWeak_false : ¬ OnlyIfClauseWeak := by
  rintro ⟨L, hL⟩
  exact onlyIf3_false ⟨L, fun n ⟨C, hlin, d, _, hmd, hcov⟩ =>
    hL n ⟨C, hlin, d, _, hmd, Nat.le_refl _, hcov⟩⟩ |>.elim

theorem levenshteinAtLeast_false (D : Nat) (hD : D ≤ 4) : ¬ LevenshteinClauseAtLeast D := by
  rintro ⟨L, hL⟩
  by_cases h3 : D ≤ 3
  · exact onlyIf3_false ⟨L, fun n ⟨C, hlin, d, hd, hmd, hcov⟩ =>
      (hL n).1 ⟨C, hlin, d, by omega, hmd, hcov⟩⟩
  · exact onlyIf4_false ⟨L, fun n ⟨C, hlin, d, hd, hmd, hcov⟩ =>
      (hL n).1 ⟨C, hlin, d, by omega, hmd, hcov⟩⟩

/-- **Main theorem.** The conjecture's clause "binary linear quasi-perfect codes of length `n`
exist iff `n = 2^k - 1` or `n` lies in a finite exceptional list" is false. In fact
(`QP_spectrum`) such codes exist for exactly the lengths `n ≥ 2`. -/
theorem conjecture_00000007964_false : ¬ LevenshteinClause := by
  rintro ⟨L, hL⟩
  let n := 2 * (listMax L + 2)
  have hpow : ∀ k, n + 1 ≠ 2^k := odd_ne_two_pow (n+1) (by omega) (by omega)
  rcases (hL n).1 ((QP_spectrum n).2 (by omega)) with ⟨k, hk⟩ | hmem
  · exact hpow k hk
  · have := le_listMax L n hmem; omega

/-- Concrete non-vacuity checks: the predicates are satisfied by explicit small codes. -/
example : IsQP 6 (SH 6) := (SH_quasiPerfect 6 (by decide) (odd_ne_two_pow 7 rfl (by decide))).2.2.2
example : IsQP 8 (EH 3) := (EH_quasiPerfect 3 (by decide)).2.2.2
example : ¬ QPLen 1 := no_QP_short 1 (by decide)
example : SH 6 [true, true, true, false, false, false] := ⟨rfl, by decide⟩
example : ¬ SH 6 [true, true, false, false, false, false] := fun h => by
  have := h.2; revert this; decide

#print axioms SH_quasiPerfect
#print axioms hamming_not_QP
#print axioms EH_quasiPerfect
#print axioms EW_quasiPerfect
#print axioms QP_spectrum
#print axioms onlyIf3_false
#print axioms onlyIf4_false
#print axioms onlyIfWeak_false
#print axioms onlyIf_any_false
#print axioms levenshteinAtLeast_false
#print axioms conjecture_00000007964_false
#print axioms EW_shellUniform
#print axioms SH5_not_shellUniform
#print axioms UQP_spectrum
#print axioms onlyIfUniform_false
#print axioms conjecture_00000007964_false_uniform
