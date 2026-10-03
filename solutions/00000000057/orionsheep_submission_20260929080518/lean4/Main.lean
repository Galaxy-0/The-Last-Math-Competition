/-!
# Disproof of TLMC Conjecture 00000000057

Conjecture: every n-vertex graph of minimum degree at least 3 contains
Ω(log n / log log n) cycles of pairwise distinct prime lengths.

Counterexample family: the disjoint union G_k of k copies of K₃,₃, modelled
on vertices that are pairs `(b, p)` with block index `b` and position
`p ∈ {0,1,2,3,4,5}`; positions `0,1,2` form the low side of a block and
positions `3,4,5` the high side. Two vertices are adjacent iff they share the
block and sit on opposite sides. The k-th family member has `n = 6k` vertices
(blocks `0 .. k-1`) and minimum degree 3.

Formalized facts (core Lean only, no Mathlib, zero axioms, zero `sorry`):

* `cycle_par_false` — the length of every cycle in G_k is even: adjacency
  flips the side, and a closed walk returns to its starting side only after
  an even number of steps (`par` is a division-free recursive parity);
* `even_not_prime` — an even length ≥ 3 is at least 4, hence composite, so
  `no_prime_cycles`: no cycle of G_k has prime length, i.e. the number of
  distinct prime cycle lengths is 0 for every k;
* `pair_min_degree` — every vertex has three pairwise distinct neighbors
  inside its block (minimum degree 3), on every block `b < k`, with
  `n = 6k` unbounded;
* concrete growth witness: `log₂ 6 / log₂ (log₂ 6 + 1) = 2 > 0` while the
  distinct-prime-length count is 0, so 0 is not Ω(log n / log log n).

The proof avoids `Nat.div`/`Nat.mod`/`omega`/`decide`-on-open-propositions
entirely (their spec lemmas depend on `propext`/`Quot.sound`); only
axiom-free core lemmas, term-mode `Eq`/`congrArg` composition, case analysis
on variables, and `decide` on closed propositions are used. `Check.lean`
audits `#print axioms` for every declaration.
-/

/-! ## Division-free parity -/

/-- Recursive parity: `par n = false` iff `n` is even. -/
def par : Nat → Bool
  | 0 => false
  | n + 1 => !par n

theorem par_succ (n : Nat) : par (n + 1) = Bool.not (par n) := rfl

theorem bnot_false {b : Bool} (h : Bool.not b = false) : b = true := by
  cases b with
  | true => rfl
  | false => exact absurd h (by decide)

theorem bnot_true {b : Bool} (h : Bool.not b = true) : b = false := by
  cases b with
  | true => exact absurd h (by decide)
  | false => rfl

theorem bne_false (b : Bool) : b = (b != false) := by
  cases b <;> rfl

theorem bne_flip2 (b d : Bool) :
    Bool.not (bne b d) = bne b (Bool.not d) := by
  cases b <;> cases d <;> rfl

theorem bne_cancel (b d : Bool) (h : b = (b != d)) : d = false := by
  cases b with
  | true => cases d with
    | true => exact absurd h (by decide)
    | false => rfl
  | false => cases d with
    | true => exact absurd h (by decide)
    | false => rfl

theorem and_eq {a b : Bool} (h1 : a = true) (h2 : b = true) : (a && b) = true := by
  cases h1
  exact h2

theorem bne_true {a b : Bool} (h1 : a = true) (h2 : b = false) : (a != b) = true := by
  cases a with
  | true => cases b with
    | true => exact absurd h2 (by decide)
    | false => rfl
  | false => cases b with
    | true => exact absurd h1 (by decide)
    | false => exact h1

theorem bne_flip {a b : Bool} (h : (a != b) = true) : b = !a := by
  cases a with
  | true => cases b with
    | true => exact absurd h (by decide)
    | false => rfl
  | false => cases b with
    | true => rfl
    | false => exact absurd h (by decide)

theorem eq_bb_trans {a b c : Bool} (h1 : a = b) (h2 : a = c) : b = c := h1.symm.trans h2

theorem bne_true_of_flip {a b : Bool} (h : b = !a) : (a != b) = true := by
  cases a with
  | true => cases b with
    | true => exact absurd h (by decide)
    | false => rfl
  | false => cases b with
    | true => rfl
    | false => exact absurd h (by decide)

theorem le_of_eq_le {a b c : Nat} (hab : a = b) (h : c ≤ a) : c ≤ b := by
  rw [← hab]; exact h

theorem le_of_eq_left {a b c : Nat} (hab : a = b) (h : a ≤ c) : b ≤ c := by
  rw [← hab]; exact h

theorem le_of_eq_right {a b c : Nat} (hab : b = c) (h : a ≤ b) : a ≤ c := by
  rw [← hab]; exact h

theorem and_true_right {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a with
  | true => exact h
  | false => exact Bool.noConfusion h

/-- Even/odd case analysis: even numbers are `2 * c`, odd ones `2 * c + 1`. -/
theorem par_spec : ∀ n : Nat,
    (par n = false → ∃ c : Nat, n = 2 * c) ∧ (par n = true → ∃ c : Nat, n = 2 * c + 1) := by
  intro n
  induction n with
  | zero =>
    refine ⟨fun _ => ⟨0, rfl⟩, fun h => absurd h (by decide)⟩
  | succ m ih =>
    cases ih with
    | intro hF hT =>
      have hs := par_succ m
      refine ⟨?_, ?_⟩
      · intro h
        have h' : Bool.not (par m) = false :=
          eq_bb_trans (a := par (m + 1)) (b := Bool.not (par m)) (c := false) hs h
        cases hT (bnot_false h') with
        | intro c hc =>
          refine ⟨c + 1, ?_⟩
          exact Eq.trans (Eq.trans (congrArg (· + 1) hc) rfl) (Eq.symm (Nat.mul_succ 2 c))
      · intro h
        have h' : Bool.not (par m) = true :=
          eq_bb_trans (a := par (m + 1)) (b := Bool.not (par m)) (c := true) hs h
        cases hF (bnot_true h') with
        | intro c hc =>
          exact ⟨c, congrArg (· + 1) hc⟩

/-! ## Primality (core Lean has no `Nat.Prime`) -/

/-- Primality: at least 2, and every divisor is trivial. -/
def IsPrime (m : Nat) : Prop := 2 ≤ m ∧ ∀ d, d ∣ m → d = 1 ∨ d = m

/-- An even number of length at least 3 is at least 4, hence composite. -/
theorem even_not_prime {m : Nat} (hpar : par m = false) (h3 : 3 ≤ m) : ¬ IsPrime m := by
  intro hp
  cases hp with
  | intro _ hall =>
    cases par_spec m with
    | intro hF _ =>
      cases hF hpar with
      | intro c hc =>
        have h2c : 2 ≤ c := by
          cases Nat.lt_or_ge c 2 with
          | inl hlt =>
            have hle : 2 * c ≤ 2 * 1 := Nat.mul_le_mul_left 2 (Nat.le_of_lt_succ hlt)
            have hm2 : m ≤ 2 * 1 := le_of_eq_left (Eq.symm hc) hle
            have hm3 : m ≤ 2 := le_of_eq_right (rfl : (2 : Nat) * 1 = 2) hm2
            exact absurd (Nat.lt_of_lt_of_le h3 hm3) (by decide)
          | inr hge => exact hge
        have h4 : 4 ≤ m := le_of_eq_le (Eq.symm hc) (Nat.mul_le_mul_left 2 h2c)
        have hdvd : 2 ∣ m := ⟨c, hc⟩
        have hor := hall 2 hdvd
        cases hor with
        | inl h1 => exact absurd h1 (by decide)
        | inr h2m => exact absurd (le_of_eq_le (Eq.symm h2m) h4) (by decide)

/-! ## Cyclic indexing into a list -/

/-- Cyclic indexing: `cycIdx l i` walks `i` steps around `l`, restarting at 0
after the end. -/
def cycIdx {α : Type} (l : List α) : Nat → Nat
  | 0 => 0
  | i + 1 => if cycIdx l i + 1 < l.length then cycIdx l i + 1 else 0

theorem cycA {α : Type} (l : List α) : ∀ k : Nat, k < l.length → cycIdx l k = k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ m ih =>
    intro hm
    show (if cycIdx l m + 1 < l.length then cycIdx l m + 1 else 0) = m + 1
    rw [ih (Nat.lt_trans (Nat.lt_succ_self m) hm), if_pos hm]

theorem cycB {α : Type} (l : List α) : ∀ L : Nat, l.length = L → cycIdx l L = 0 := by
  intro L
  induction L with
  | zero => intro _; rfl
  | succ m ih =>
    intro hlen
    have hm : cycIdx l m = m := cycA l m (by rw [hlen]; exact Nat.lt_succ_self m)
    show (if cycIdx l m + 1 < l.length then cycIdx l m + 1 else 0) = 0
    rw [hm, hlen, if_neg (Nat.lt_irrefl (m + 1))]

/-! ## The counterexample family: pairs (block, position) -/

/-- Side of a vertex: `true` for positions 0,1,2, `false` for 3,4,5. -/
def side (v : Nat × Nat) : Bool := decide (v.2 < 3)

/-- Adjacency of the family: same block, opposite side. -/
def adjP (x y : Nat × Nat) : Bool := decide (x.1 = y.1) && (side x != side y)

theorem adjP_flip (x y : Nat × Nat) (h : adjP x y = true) : side y = !(side x) :=
  bne_flip (and_true_right h)

theorem side_eq_true {v : Nat × Nat} (h : v.2 < 3) : side v = true := decide_eq_true h

theorem side_eq_false {v : Nat × Nat} (h : ¬ (v.2 < 3)) : side v = false := decide_eq_false h

theorem adjP_intro {x y : Nat × Nat} (h1 : x.1 = y.1) (h2 : side y = !(side x)) :
    adjP x y = true :=
  and_eq (decide_eq_true h1) (bne_true_of_flip h2)

theorem prod_snd_ne {b i j : Nat} (h : i ≠ j) : (b, i) ≠ (b, j) := by
  intro he
  exact h (congrArg Prod.snd he)

theorem adjP_opp {b p q : Nat} (hp3 : p < 3) (hq3 : ¬ (q < 3)) :
    adjP (b, p) (b, q) = true := by
  refine adjP_intro ?_ ?_
  · exact rfl
  · exact Eq.trans (side_eq_false hq3) (Eq.symm (congrArg Bool.not (side_eq_true hp3)))

theorem adjP_oppR {b p q : Nat} (hpge : ¬ (p < 3)) (hqlt : q < 3) :
    adjP (b, p) (b, q) = true := by
  refine adjP_intro ?_ ?_
  · exact rfl
  · exact Eq.trans (side_eq_true hqlt) (Eq.symm (congrArg Bool.not (side_eq_false hpge)))

/-- Minimum degree 3: every vertex of the family member with blocks
`0 .. k-1` has three pairwise distinct neighbors, also with block index
`< k`. -/
theorem pair_min_degree_bounded (k : Nat) (v : Nat × Nat) (hv : v.1 < k) :
    ∃ x y z : Nat × Nat, x.1 < k ∧ y.1 < k ∧ z.1 < k ∧
      x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      adjP v x = true ∧ adjP v y = true ∧ adjP v z = true := by
  cases Nat.lt_or_ge v.2 3 with
  | inl hlt =>
    refine ⟨(v.1, 3), (v.1, 4), (v.1, 5), hv, hv, hv, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact prod_snd_ne (Nat.ne_of_lt (Nat.lt_succ_self 3))
    · exact prod_snd_ne (Nat.ne_of_lt (Nat.lt_trans (Nat.lt_succ_self 3) (Nat.lt_succ_self 4)))
    · exact prod_snd_ne (Nat.ne_of_lt (Nat.lt_succ_self 4))
    · exact adjP_opp hlt (by decide)
    · exact adjP_opp hlt (by decide)
    · exact adjP_opp hlt (by decide)
  | inr hge =>
    have hpge : ¬ (v.2 < 3) := fun hc => Nat.lt_irrefl v.2 (Nat.lt_of_lt_of_le hc hge)
    refine ⟨(v.1, 0), (v.1, 1), (v.1, 2), hv, hv, hv, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact prod_snd_ne (Nat.ne_of_lt Nat.zero_lt_one)
    · exact prod_snd_ne (Nat.ne_of_lt (Nat.lt_trans Nat.zero_lt_one (Nat.lt_succ_self 1)))
    · exact prod_snd_ne (Nat.ne_of_lt (Nat.lt_succ_self 1))
    · exact adjP_oppR hpge (by decide)
    · exact adjP_oppR hpge (by decide)
    · exact adjP_oppR hpge (by decide)

/-! ## Cycles and their lengths -/

/-- A simple cycle: length ≥ 3, pairwise distinct vertices, all satisfying
`P`, consecutive vertices adjacent, and some last-to-first edge. -/
def IsCycle {α : Type} [Inhabited α] (P : α → Prop) (adjr : α → α → Bool) (l : List α) : Prop :=
  3 ≤ l.length ∧ (∀ v ∈ l, P v) ∧ l.Pairwise (· ≠ ·) ∧
    (∀ i : Nat, i + 1 < l.length →
      adjr (l.getD i default) (l.getD (i + 1) default) = true) ∧
    (∃ i : Nat, i + 1 = l.length ∧
      adjr (l.getD i default) (l.getD 0 default) = true)

/-- Side of the vertex at walk position `i` of `l` (cyclic indexing). -/
def partAt (l : List (Nat × Nat)) (i : Nat) : Bool :=
  side (l.getD (cycIdx l i) (0, 0))

theorem congr_part_getD (l : List (Nat × Nat)) {x y : Nat} (h : x = y) :
    side (l.getD x (0, 0)) = side (l.getD y (0, 0)) :=
  congrArg (fun t => side (l.getD t (0, 0))) h

theorem congr_not_part_getD (l : List (Nat × Nat)) {x y : Nat} (h : x = y) :
    Bool.not (side (l.getD x (0, 0))) = Bool.not (side (l.getD y (0, 0))) :=
  congrArg (fun t => Bool.not (side (l.getD t (0, 0)))) h

theorem eq_xx_trans {a b c : Nat} (h1 : a = b) (h2 : a = c) : b = c := h1.symm.trans h2

/-- Walking one step along a cycle flips the side. -/
theorem step_flip {k : Nat} {l : List (Nat × Nat)}
    (hc : IsCycle (fun v : Nat × Nat => v.1 < k) adjP l) :
    ∀ j : Nat, j < l.length → partAt l (j + 1) = !(partAt l j) := by
  intro j hj
  have hAj : cycIdx l j = j := cycA l j hj
  have horn := Nat.lt_or_ge (j + 1) l.length
  cases horn with
  | inl hlt =>
    have hAj1 : cycIdx l (j + 1) = j + 1 := cycA l (j + 1) hlt
    have he := hc.2.2.2.1 j hlt
    exact Eq.trans (congr_part_getD l hAj1)
      (Eq.trans (adjP_flip (x := l.getD j (0, 0)) (y := l.getD (j + 1) (0, 0)) he)
        (congr_not_part_getD (x := j) (y := cycIdx l j) l (Eq.symm hAj)))
  | inr hge =>
    have heq : j + 1 = l.length := Nat.le_antisymm (Nat.succ_le_of_lt hj) hge
    have hAj1 : cycIdx l (j + 1) = 0 :=
      eq_xx_trans (a := cycIdx l l.length) (b := cycIdx l (j + 1)) (c := 0)
        (Eq.symm (congrArg (cycIdx l) heq)) (cycB l l.length rfl)
    cases hc.2.2.2.2 with
    | intro i hi =>
      have hij : i = j := Nat.succ.inj (Eq.trans hi.left (Eq.symm heq))
      have hlk : adjP (l.getD (cycIdx l j) (0, 0)) (l.getD (cycIdx l (j + 1)) (0, 0)) = true := by
        rw [hAj, hAj1, ← hij]
        exact hi.right
      exact adjP_flip (x := l.getD (cycIdx l j) (0, 0))
        (y := l.getD (cycIdx l (j + 1)) (0, 0)) hlk

/-- The number of steps around a cycle is even: sides alternate, and after
`l.length` steps the walk is back at its starting side. -/
theorem cycle_par_false {k : Nat} {l : List (Nat × Nat)}
    (hc : IsCycle (fun v : Nat × Nat => v.1 < k) adjP l) : par l.length = false := by
  have key : ∀ j : Nat, j ≤ l.length → partAt l j = (partAt l 0 != par j) := by
    intro j
    induction j with
    | zero => intro _; exact bne_false (partAt l 0)
    | succ m ih =>
      intro hm1
      have hm0 : m < l.length := Nat.lt_of_lt_of_le (Nat.lt_succ_self m) hm1
      rw [par_succ m, step_flip hc m hm0, congrArg Bool.not (ih (Nat.le_of_lt hm0)),
        bne_flip2 (partAt l 0) (par m)]
  have hwrap : partAt l l.length = partAt l 0 := by
    have hB : cycIdx l l.length = 0 := cycB l l.length rfl
    have h0 : 0 < l.length := Nat.lt_of_lt_of_le (by decide) hc.1
    show side (l.getD (cycIdx l l.length) (0, 0)) = side (l.getD (cycIdx l 0) (0, 0))
    rw [hB, cycA l 0 h0]
  have hm := key l.length (Nat.le_refl l.length)
  have hm2 : partAt l 0 = (partAt l 0 != par l.length) :=
    Eq.trans (Eq.symm hwrap) hm
  exact bne_cancel _ _ hm2

/-- Hence no cycle of the counterexample family has prime length. -/
theorem no_prime_cycles {k : Nat} (l : List (Nat × Nat))
    (hc : IsCycle (fun v : Nat × Nat => v.1 < k) adjP l) : ¬ IsPrime l.length :=
  even_not_prime (cycle_par_false hc) hc.1

/-! ## The disproof -/

/-- Main disproof of conjecture 00000000057.

For every `k`, the family member with blocks `0 .. k-1` (`n = 6k` vertices):
* every vertex has three pairwise distinct neighbors on its block
  (minimum degree 3), available for all `k`;
* no cycle has prime length, so the number of distinct prime cycle lengths
  is 0 for every `k`;
while the discrete growth witness at `n = 6` is already positive
(`log₂ 6 / log₂ (log₂ 6 + 1) = 2`). Hence 0 is not Ω(log n / log log n):
the conjecture is false. -/
theorem disproof_00000000057 :
    (∀ k : Nat, ∀ v : Nat × Nat, v.1 < k →
        ∃ x y z : Nat × Nat, x.1 < k ∧ y.1 < k ∧ z.1 < k ∧
          x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
          adjP v x = true ∧ adjP v y = true ∧ adjP v z = true) ∧
    (∀ k : Nat, ∀ l : List (Nat × Nat),
        IsCycle (fun v : Nat × Nat => v.1 < k) adjP l → ¬ IsPrime l.length) ∧
    (∀ k : Nat, 0 < k → 6 ≤ 6 * k) ∧
    (Nat.log2 6 / Nat.log2 (Nat.log2 6 + 1) = 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact pair_min_degree_bounded
  · exact fun _k l hc => no_prime_cycles l hc
  · exact fun k hk => Nat.le_trans (by decide) (Nat.le_mul_of_pos_right 6 hk)
  · decide

/-- Concrete witness values of the attack, verified by evaluation. -/
example : Nat.log2 6 = 2 := by decide
example : (Nat.log2 6 / Nat.log2 (Nat.log2 6 + 1)) = 2 := by decide
example : (6 : Nat) = 2 * 3 := rfl
example : (4 : Nat) = 2 * 2 := rfl
