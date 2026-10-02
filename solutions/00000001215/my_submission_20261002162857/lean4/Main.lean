/-!
# Disproof of TLMC conjecture 00000001215 (outerplanar cop number, finitude part)

Conjecture 00000001215 claims (verbatim definition sentence): the cop number
of a planar graph is at most three and the bound is tight; the cop number of
an outerplanar graph is at most two, **with only finitely many graphs attaining
the bound up to isomorphism**.

Attack: the cycles `C_n` for `n ≥ 4`.  Each `C_n` is outerplanar (draw it as a
convex polygon) and has cop number **exactly** 2, and the family is pairwise
non-isomorphic (distinct vertex counts).  Hence infinitely many pairwise
non-isomorphic outerplanar graphs attain the bound 2, and the finitude claim
is false.

This file formalizes the game-theoretic core in core Lean 4 (no Mathlib):

* `Cyc` — a cycle structure on `Fin n` (successor `cw`, predecessor `ccw` with
  inverse laws and no short cycles: no loops, 2-cycles or 3-cycles).
* `robber_mirror` (general, all `n`): with ONE cop, the robber answering from
  `cw (cw c)` and mirroring every cop move keeps `win1 = false` for every
  number of rounds `k` — one cop NEVER wins on any cycle, so the cop number of
  every `C_n` is `≥ 2` (the subtle direction).
* `G5`, `win2`, `capT5`, `strat5` — for the concrete 5-cycle: a full
  state-space certificate that TWO cops always capture (within ≤ 2 rounds),
  so the cop number of `C_5` is exactly 2.
* `noCross5` — a straight-line outer-embedding witness for `C_5` (identity
  cyclic order, no pair of non-adjacent edges crosses).
* `cycleGraph`, `cycle_count_inj` — the family `n ↦ C_n` is injective on
  vertex counts (an isomorphism invariant), i.e. pairwise non-isomorphic.

Every proof is axiom-free: pure kernel computation (`decide` over explicit
tables) and structural inductions with hand-rolled Bool/List lemmas; zero
`sorry`.  See `Check.lean` for the `#print axioms` audit.
-/

namespace TLMC1215

/-! ### Small arithmetic helpers (axiom-free) -/

/-- `v + 5 < 5` is impossible. -/
theorem lt5_false {v : Nat} (h : v + 5 < 5) : False :=
  absurd (Nat.le_trans (Nat.le_add_left 5 v) (Nat.le_of_lt_succ (m := v + 5) (n := 4) h)) (by decide)

/-- Five-way case analysis on a natural number below 5. -/
theorem lt5_cases {p : Nat → Prop} (h0 : p 0) (h1 : p 1) (h2 : p 2) (h3 : p 3)
    (h4 : p 4) (v : Nat) (hv : v < 5) : p v := by
  cases v with
  | zero => exact h0
  | succ v1 => cases v1 with
    | zero => exact h1
    | succ v2 => cases v2 with
      | zero => exact h2
      | succ v3 => cases v3 with
        | zero => exact h3
        | succ v4 => cases v4 with
          | zero => exact h4
          | succ v5 => exact absurd hv lt5_false

/-- Five-way case analysis on `Fin 5`: the branches are stated at the five
explicit `Fin.mk k (proof)` values and the goal is transported along
`Fin.mk x.val x.isLt` (definitional eta for `Fin`, no axioms). -/
theorem fin5_cases {p : Fin 5 → Prop}
    (h0 : p (Fin.mk 0 (by decide : (0 : Nat) < 5)))
    (h1 : p (Fin.mk 1 (by decide : (1 : Nat) < 5)))
    (h2 : p (Fin.mk 2 (by decide : (2 : Nat) < 5)))
    (h3 : p (Fin.mk 3 (by decide : (3 : Nat) < 5)))
    (h4 : p (Fin.mk 4 (by decide : (4 : Nat) < 5)))
    (x : Fin 5) : p x :=
  lt5_cases (p := fun w => ∀ hw : w < 5, p (Fin.mk w hw))
    (fun _ => h0) (fun _ => h1) (fun _ => h2) (fun _ => h3) (fun _ => h4) x.val x.isLt x.isLt

/-! ### Bool / List glue (axiom-free, proved from scratch) -/

theorem beq_false_of_ne {α : Type} [DecidableEq α] {x y : α} (h : x ≠ y) :
    (x == y) = false := by
  cases h' : (x == y) with
  | false => rfl
  | true =>
      have h'' : decide (x = y) = true := h'
      exact absurd (of_decide_eq_true h'') h

theorem beq_true_of_eq {α : Type} [DecidableEq α] {x y : α} (h : x = y) : (x == y) = true := by
  have h1 : decide (x = x) = true := decide_eq_true rfl
  have h2 : decide (x = x) = decide (x = y) := congrArg (fun z : α => decide (x = z)) h
  show decide (x = y) = true
  exact h2.symm.trans h1

theorem and_true_l {b c : Bool} (h : (b && c) = true) : b = true := by
  cases b with
  | false => exact h
  | true => rfl

theorem and_true_r {b c : Bool} (h : (b && c) = true) : c = true := by
  cases b <;> cases c <;> first | rfl | exact h

theorem or3l {a b c : Bool} (h : a = true) : (a || b || c) = true := by
  subst h; rfl
theorem or3ml {a b c : Bool} (h : b = true) : (a || b || c) = true := by
  subst h
  exact (congrArg (fun w : Bool => w || c) (Bool.or_true a)).trans (Bool.true_or c)
theorem or3r {a b c : Bool} (h : c = true) : (a || b || c) = true := by
  subst h
  exact Bool.or_true (a || b)

theorem or_true_cases {a b : Bool} (h : (a || b) = true) : a = true ∨ b = true := by
  cases a with
  | true => exact Or.inl rfl
  | false => cases b with
    | true => exact Or.inr rfl
    | false => exact Bool.noConfusion h

theorem any_cons_true {α : Type} {f : α → Bool} {a : α} {l : List α}
    (h : f a = true) : (a :: l).any f = true := by
  show (f a || l.any f) = true
  rw [h]
  exact Bool.true_or (l.any f)

theorem any_cons_tail {α : Type} {f : α → Bool} {a : α} {l : List α}
    (h : l.any f = true) : (a :: l).any f = true := by
  show (f a || l.any f) = true
  rw [h]
  exact Bool.or_true (f a)

theorem all_cons_head_false {α : Type} {f : α → Bool} {a : α} {l : List α}
    (h : f a = false) : (a :: l).all f = false := by
  show (f a && l.all f) = false
  rw [h, Bool.false_and]

theorem all_cons_mid_false {α : Type} {f : α → Bool} {a b : α} {l : List α}
    (h : f b = false) : (a :: b :: l).all f = false := by
  show (f a && (f b && l.all f)) = false
  rw [h, Bool.false_and, Bool.and_false]

theorem all_cons_last_false {α : Type} {f : α → Bool} {a b c : α}
    (h : f c = false) : (a :: b :: c :: []).all f = false := by
  show (f a && (f b && (f c && ([] : List α).all f))) = false
  rw [h, Bool.false_and, Bool.and_false, Bool.and_false]

theorem all_cons_true2 {α : Type} {f : α → Bool} {a : α} {l : List α}
    (h : f a = true) (hl : l.all f = true) : (a :: l).all f = true := by
  show (f a && l.all f) = true
  rw [h, hl]
  exact rfl


/-! ### Part 1 — one cop never wins on ANY cycle (general theorem)

A `Cyc n` equips `Fin n` with a successor `cw` and predecessor `ccw` that are
mutually inverse and rule out loops, 2-cycles and 3-cycles (so `n ≥ 4`).
`win1 G k c r` = "the single cop at `c` can force capture of the robber at `r`
within `k` rounds" (cop moves first, each to a neighbour or stays; capture if
the cop lands on the robber or the robber walks into the cop). -/

structure Cyc (n : Nat) where
  cw : Fin n → Fin n
  ccw : Fin n → Fin n
  ccw_cw : ∀ i, ccw (cw i) = i
  cw_ccw : ∀ i, cw (ccw i) = i
  cw_ne : ∀ i, cw i ≠ i
  cw2_ne : ∀ i, cw (cw i) ≠ i
  cw3_ne : ∀ i, cw (cw (cw i)) ≠ i

def moves1 {n : Nat} (G : Cyc n) (x : Fin n) : List (Fin n) := [x, G.cw x, G.ccw x]

def win1 {n : Nat} (G : Cyc n) : Nat → Fin n → Fin n → Bool
  | 0, _, _ => false
  | k + 1, c, r =>
      (moves1 G c).any fun d =>
        d == r || ((moves1 G r).all fun r' => win1 G k d r')

theorem moves1_any {n : Nat} (G : Cyc n) (x : Fin n) (f : Fin n → Bool) :
    (moves1 G x).any f = (f x || (f (G.cw x) || (f (G.ccw x) || false))) := rfl

theorem cw_inj {n : Nat} (G : Cyc n) {x y : Fin n} (h : G.cw x = G.cw y) : x = y := by
  rw [← G.ccw_cw x, h, G.ccw_cw y]

/-- **The mirror strategy.** Robber starts two clockwise steps ahead of the cop
(`r = cw (cw c)`) and copies every cop move; the position `r = cw (cw c)` is
preserved forever, and it is never a capture. -/
theorem robber_mirror {n : Nat} (G : Cyc n) : ∀ (k : Nat) (c : Fin n),
    win1 G k c (G.cw (G.cw c)) = false := by
  intro k
  induction k with
  | zero => intro c; rfl
  | succ k IH =>
    intro c
    show (moves1 G c).any
      (fun d => d == G.cw (G.cw c) ||
        (moves1 G (G.cw (G.cw c))).all (fun r' => win1 G k d r')) = false
    rw [moves1_any]
    show ((c == G.cw (G.cw c) ||
        (moves1 G (G.cw (G.cw c))).all (fun r' => win1 G k c r')) ||
      ((G.cw c == G.cw (G.cw c) ||
          (moves1 G (G.cw (G.cw c))).all (fun r' => win1 G k (G.cw c) r')) ||
        ((G.ccw c == G.cw (G.cw c) ||
            (moves1 G (G.cw (G.cw c))).all (fun r' => win1 G k (G.ccw c) r')) ||
          false))) =
      false
    have h1 : (c == G.cw (G.cw c) ||
        (moves1 G (G.cw (G.cw c))).all (fun r' => win1 G k c r')) = false := by
      rw [beq_false_of_ne (Ne.symm (G.cw2_ne c))]
      exact all_cons_head_false (IH c)
    have h2 : (G.cw c == G.cw (G.cw c) ||
        (moves1 G (G.cw (G.cw c))).all (fun r' => win1 G k (G.cw c) r')) = false := by
      rw [beq_false_of_ne (fun h => G.cw_ne c (cw_inj G h).symm)]
      exact all_cons_mid_false (IH (G.cw c))
    have h3 : (G.ccw c == G.cw (G.cw c) ||
        (moves1 G (G.cw (G.cw c))).all (fun r' => win1 G k (G.ccw c) r')) = false := by
      have hne3 : G.ccw c ≠ G.cw (G.cw c) := by
        intro h
        refine G.cw3_ne c ?_
        exact (congrArg G.cw h).symm.trans (G.cw_ccw c)
      rw [beq_false_of_ne hne3]
      refine all_cons_last_false ?_
      show win1 G k (G.ccw c) (G.ccw (G.cw (G.cw c))) = false
      rw [G.ccw_cw]
      have h9 := IH (G.ccw c)
      rw [G.cw_ccw] at h9
      exact h9
    rw [h1, Bool.false_or, h2, Bool.false_or, h3, Bool.or_false]

/-- Consequently, for every fixed cop vertex `c` and every round budget `k`,
the robber has an answer, so ONE cop never forces capture on any `Cyc`. -/
theorem one_cop_never_wins {n : Nat} (G : Cyc n) (c : Fin n) :
    ¬ ∃ k : Nat, ∀ r : Fin n, win1 G k c r = true := by
  rintro ⟨k, hk⟩
  exact Bool.noConfusion ((robber_mirror G k c).symm.trans (hk (G.cw (G.cw c))))


/-! ### Part 2 — the concrete 5-cycle: cop number exactly 2 -/

/-- Successor on `C_5`. -/
def cw5 (x : Fin 5) : Fin 5 :=
  match hv : x.val with
  | 0 => ⟨1, by decide⟩
  | 1 => ⟨2, by decide⟩
  | 2 => ⟨3, by decide⟩
  | 3 => ⟨4, by decide⟩
  | 4 => ⟨0, by decide⟩
  | v + 5 => False.elim (by
      have h9 := x.isLt
      rw [hv] at h9
      exact lt5_false h9)

/-- Predecessor on `C_5`. -/
def ccw5 (x : Fin 5) : Fin 5 :=
  match hv : x.val with
  | 0 => ⟨4, by decide⟩
  | 1 => ⟨0, by decide⟩
  | 2 => ⟨1, by decide⟩
  | 3 => ⟨2, by decide⟩
  | 4 => ⟨3, by decide⟩
  | v + 5 => False.elim (by
      have h9 := x.isLt
      rw [hv] at h9
      exact lt5_false h9)

/-- `C_5` as a cycle structure. -/
def G5 : Cyc 5 := {
  cw := cw5
  ccw := ccw5
  ccw_cw := by
    intro i
    exact @fin5_cases (fun w => ccw5 (cw5 w) = w) (by decide) (by decide) (by decide)
      (by decide) (by decide) i
  cw_ccw := by
    intro i
    exact @fin5_cases (fun w => cw5 (ccw5 w) = w) (by decide) (by decide) (by decide)
      (by decide) (by decide) i
  cw_ne := by
    intro i
    exact @fin5_cases (fun w => cw5 w ≠ w) (by decide) (by decide) (by decide)
      (by decide) (by decide) i
  cw2_ne := by
    intro i
    exact @fin5_cases (fun w => cw5 (cw5 w) ≠ w) (by decide) (by decide) (by decide)
      (by decide) (by decide) i
  cw3_ne := by
    intro i
    exact @fin5_cases (fun w => cw5 (cw5 (cw5 w)) ≠ w) (by decide) (by decide) (by decide)
      (by decide) (by decide) i
}

/-- TWO cops (Aigner–Fromme rules): `win2 G k a b c` = "cops at `a`, `b` force
capture of the robber at `c` within `k` rounds" (both cops move simultaneously,
then the robber moves; capture on contact either way). -/
def win2 {n : Nat} (G : Cyc n) : Nat → Fin n → Fin n → Fin n → Bool
  | 0, _, _, _ => false
  | k + 1, a, b, c =>
      (moves1 G a).any fun d1 =>
        (moves1 G b).any fun d2 =>
          d1 == c || d2 == c ||
            ((moves1 G c).all fun r' => win2 G k d1 d2 r')


/-- Capture horizon table for C_5 (2 cops): minimal number of rounds
after which the cops can force capture from the ordered state
(c1, c2, r); already-captured states have value 1. Computed by the
bundled `reproduce.py` (same numbers, independently recomputed). -/
def capT5 (a b c : Fin 5) : Nat :=
  match a.val, b.val, c.val with
  | 0, 0, 0 => 1
  | 0, 0, 1 => 1
  | 0, 0, 2 => 2
  | 0, 0, 3 => 2
  | 0, 0, 4 => 1
  | 0, 1, 0 => 1
  | 0, 1, 1 => 1
  | 0, 1, 2 => 1
  | 0, 1, 3 => 2
  | 0, 1, 4 => 1
  | 0, 2, 0 => 1
  | 0, 2, 1 => 1
  | 0, 2, 2 => 1
  | 0, 2, 3 => 1
  | 0, 2, 4 => 1
  | 0, 3, 0 => 1
  | 0, 3, 1 => 1
  | 0, 3, 2 => 1
  | 0, 3, 3 => 1
  | 0, 3, 4 => 1
  | 0, 4, 0 => 1
  | 0, 4, 1 => 1
  | 0, 4, 2 => 2
  | 0, 4, 3 => 1
  | 0, 4, 4 => 1
  | 1, 0, 0 => 1
  | 1, 0, 1 => 1
  | 1, 0, 2 => 1
  | 1, 0, 3 => 2
  | 1, 0, 4 => 1
  | 1, 1, 0 => 1
  | 1, 1, 1 => 1
  | 1, 1, 2 => 1
  | 1, 1, 3 => 2
  | 1, 1, 4 => 2
  | 1, 2, 0 => 1
  | 1, 2, 1 => 1
  | 1, 2, 2 => 1
  | 1, 2, 3 => 1
  | 1, 2, 4 => 2
  | 1, 3, 0 => 1
  | 1, 3, 1 => 1
  | 1, 3, 2 => 1
  | 1, 3, 3 => 1
  | 1, 3, 4 => 1
  | 1, 4, 0 => 1
  | 1, 4, 1 => 1
  | 1, 4, 2 => 1
  | 1, 4, 3 => 1
  | 1, 4, 4 => 1
  | 2, 0, 0 => 1
  | 2, 0, 1 => 1
  | 2, 0, 2 => 1
  | 2, 0, 3 => 1
  | 2, 0, 4 => 1
  | 2, 1, 0 => 1
  | 2, 1, 1 => 1
  | 2, 1, 2 => 1
  | 2, 1, 3 => 1
  | 2, 1, 4 => 2
  | 2, 2, 0 => 2
  | 2, 2, 1 => 1
  | 2, 2, 2 => 1
  | 2, 2, 3 => 1
  | 2, 2, 4 => 2
  | 2, 3, 0 => 2
  | 2, 3, 1 => 1
  | 2, 3, 2 => 1
  | 2, 3, 3 => 1
  | 2, 3, 4 => 1
  | 2, 4, 0 => 1
  | 2, 4, 1 => 1
  | 2, 4, 2 => 1
  | 2, 4, 3 => 1
  | 2, 4, 4 => 1
  | 3, 0, 0 => 1
  | 3, 0, 1 => 1
  | 3, 0, 2 => 1
  | 3, 0, 3 => 1
  | 3, 0, 4 => 1
  | 3, 1, 0 => 1
  | 3, 1, 1 => 1
  | 3, 1, 2 => 1
  | 3, 1, 3 => 1
  | 3, 1, 4 => 1
  | 3, 2, 0 => 2
  | 3, 2, 1 => 1
  | 3, 2, 2 => 1
  | 3, 2, 3 => 1
  | 3, 2, 4 => 1
  | 3, 3, 0 => 2
  | 3, 3, 1 => 2
  | 3, 3, 2 => 1
  | 3, 3, 3 => 1
  | 3, 3, 4 => 1
  | 3, 4, 0 => 1
  | 3, 4, 1 => 2
  | 3, 4, 2 => 1
  | 3, 4, 3 => 1
  | 3, 4, 4 => 1
  | 4, 0, 0 => 1
  | 4, 0, 1 => 1
  | 4, 0, 2 => 2
  | 4, 0, 3 => 1
  | 4, 0, 4 => 1
  | 4, 1, 0 => 1
  | 4, 1, 1 => 1
  | 4, 1, 2 => 1
  | 4, 1, 3 => 1
  | 4, 1, 4 => 1
  | 4, 2, 0 => 1
  | 4, 2, 1 => 1
  | 4, 2, 2 => 1
  | 4, 2, 3 => 1
  | 4, 2, 4 => 1
  | 4, 3, 0 => 1
  | 4, 3, 1 => 2
  | 4, 3, 2 => 1
  | 4, 3, 3 => 1
  | 4, 3, 4 => 1
  | 4, 4, 0 => 1
  | 4, 4, 1 => 2
  | 4, 4, 2 => 2
  | 4, 4, 3 => 1
  | 4, 4, 4 => 1
  | _, _, _ => 0

/-- Chaser/guard move pair the cops play from ordered state (c1, c2, r):
an immediate capture when `capT5 c1 c2 r = 1`, otherwise a move after
which every robber reply strictly lowers the capture horizon. -/
def strat5 (a b c : Fin 5) : Fin 5 × Fin 5 :=
  match a.val, b.val, c.val with
  | 0, 0, 0 => ((4 : Fin 5), (0 : Fin 5))
  | 0, 0, 1 => ((4 : Fin 5), (1 : Fin 5))
  | 0, 0, 2 => ((1 : Fin 5), (4 : Fin 5))
  | 0, 0, 3 => ((1 : Fin 5), (4 : Fin 5))
  | 0, 0, 4 => ((4 : Fin 5), (0 : Fin 5))
  | 0, 1, 0 => ((4 : Fin 5), (0 : Fin 5))
  | 0, 1, 1 => ((4 : Fin 5), (1 : Fin 5))
  | 0, 1, 2 => ((4 : Fin 5), (2 : Fin 5))
  | 0, 1, 3 => ((0 : Fin 5), (2 : Fin 5))
  | 0, 1, 4 => ((4 : Fin 5), (1 : Fin 5))
  | 0, 2, 0 => ((0 : Fin 5), (2 : Fin 5))
  | 0, 2, 1 => ((4 : Fin 5), (1 : Fin 5))
  | 0, 2, 2 => ((4 : Fin 5), (2 : Fin 5))
  | 0, 2, 3 => ((4 : Fin 5), (3 : Fin 5))
  | 0, 2, 4 => ((4 : Fin 5), (2 : Fin 5))
  | 0, 3, 0 => ((0 : Fin 5), (3 : Fin 5))
  | 0, 3, 1 => ((1 : Fin 5), (3 : Fin 5))
  | 0, 3, 2 => ((4 : Fin 5), (2 : Fin 5))
  | 0, 3, 3 => ((4 : Fin 5), (3 : Fin 5))
  | 0, 3, 4 => ((4 : Fin 5), (3 : Fin 5))
  | 0, 4, 0 => ((4 : Fin 5), (0 : Fin 5))
  | 0, 4, 1 => ((1 : Fin 5), (4 : Fin 5))
  | 0, 4, 2 => ((0 : Fin 5), (3 : Fin 5))
  | 0, 4, 3 => ((4 : Fin 5), (3 : Fin 5))
  | 0, 4, 4 => ((4 : Fin 5), (4 : Fin 5))
  | 1, 0, 0 => ((0 : Fin 5), (0 : Fin 5))
  | 1, 0, 1 => ((0 : Fin 5), (1 : Fin 5))
  | 1, 0, 2 => ((2 : Fin 5), (0 : Fin 5))
  | 1, 0, 3 => ((1 : Fin 5), (4 : Fin 5))
  | 1, 0, 4 => ((0 : Fin 5), (4 : Fin 5))
  | 1, 1, 0 => ((0 : Fin 5), (1 : Fin 5))
  | 1, 1, 1 => ((0 : Fin 5), (1 : Fin 5))
  | 1, 1, 2 => ((0 : Fin 5), (2 : Fin 5))
  | 1, 1, 3 => ((2 : Fin 5), (0 : Fin 5))
  | 1, 1, 4 => ((2 : Fin 5), (0 : Fin 5))
  | 1, 2, 0 => ((0 : Fin 5), (2 : Fin 5))
  | 1, 2, 1 => ((0 : Fin 5), (1 : Fin 5))
  | 1, 2, 2 => ((0 : Fin 5), (2 : Fin 5))
  | 1, 2, 3 => ((0 : Fin 5), (3 : Fin 5))
  | 1, 2, 4 => ((1 : Fin 5), (3 : Fin 5))
  | 1, 3, 0 => ((0 : Fin 5), (3 : Fin 5))
  | 1, 3, 1 => ((1 : Fin 5), (3 : Fin 5))
  | 1, 3, 2 => ((0 : Fin 5), (2 : Fin 5))
  | 1, 3, 3 => ((0 : Fin 5), (3 : Fin 5))
  | 1, 3, 4 => ((0 : Fin 5), (4 : Fin 5))
  | 1, 4, 0 => ((0 : Fin 5), (4 : Fin 5))
  | 1, 4, 1 => ((1 : Fin 5), (4 : Fin 5))
  | 1, 4, 2 => ((2 : Fin 5), (4 : Fin 5))
  | 1, 4, 3 => ((0 : Fin 5), (3 : Fin 5))
  | 1, 4, 4 => ((0 : Fin 5), (4 : Fin 5))
  | 2, 0, 0 => ((1 : Fin 5), (0 : Fin 5))
  | 2, 0, 1 => ((1 : Fin 5), (0 : Fin 5))
  | 2, 0, 2 => ((2 : Fin 5), (0 : Fin 5))
  | 2, 0, 3 => ((3 : Fin 5), (0 : Fin 5))
  | 2, 0, 4 => ((1 : Fin 5), (4 : Fin 5))
  | 2, 1, 0 => ((1 : Fin 5), (0 : Fin 5))
  | 2, 1, 1 => ((1 : Fin 5), (1 : Fin 5))
  | 2, 1, 2 => ((1 : Fin 5), (2 : Fin 5))
  | 2, 1, 3 => ((3 : Fin 5), (1 : Fin 5))
  | 2, 1, 4 => ((2 : Fin 5), (0 : Fin 5))
  | 2, 2, 0 => ((3 : Fin 5), (1 : Fin 5))
  | 2, 2, 1 => ((1 : Fin 5), (2 : Fin 5))
  | 2, 2, 2 => ((1 : Fin 5), (2 : Fin 5))
  | 2, 2, 3 => ((1 : Fin 5), (3 : Fin 5))
  | 2, 2, 4 => ((3 : Fin 5), (1 : Fin 5))
  | 2, 3, 0 => ((2 : Fin 5), (4 : Fin 5))
  | 2, 3, 1 => ((1 : Fin 5), (3 : Fin 5))
  | 2, 3, 2 => ((1 : Fin 5), (2 : Fin 5))
  | 2, 3, 3 => ((1 : Fin 5), (3 : Fin 5))
  | 2, 3, 4 => ((1 : Fin 5), (4 : Fin 5))
  | 2, 4, 0 => ((1 : Fin 5), (0 : Fin 5))
  | 2, 4, 1 => ((1 : Fin 5), (4 : Fin 5))
  | 2, 4, 2 => ((2 : Fin 5), (4 : Fin 5))
  | 2, 4, 3 => ((1 : Fin 5), (3 : Fin 5))
  | 2, 4, 4 => ((1 : Fin 5), (4 : Fin 5))
  | 3, 0, 0 => ((2 : Fin 5), (0 : Fin 5))
  | 3, 0, 1 => ((2 : Fin 5), (1 : Fin 5))
  | 3, 0, 2 => ((2 : Fin 5), (0 : Fin 5))
  | 3, 0, 3 => ((3 : Fin 5), (0 : Fin 5))
  | 3, 0, 4 => ((2 : Fin 5), (4 : Fin 5))
  | 3, 1, 0 => ((2 : Fin 5), (0 : Fin 5))
  | 3, 1, 1 => ((2 : Fin 5), (1 : Fin 5))
  | 3, 1, 2 => ((2 : Fin 5), (1 : Fin 5))
  | 3, 1, 3 => ((3 : Fin 5), (1 : Fin 5))
  | 3, 1, 4 => ((4 : Fin 5), (1 : Fin 5))
  | 3, 2, 0 => ((3 : Fin 5), (1 : Fin 5))
  | 3, 2, 1 => ((2 : Fin 5), (1 : Fin 5))
  | 3, 2, 2 => ((2 : Fin 5), (2 : Fin 5))
  | 3, 2, 3 => ((2 : Fin 5), (3 : Fin 5))
  | 3, 2, 4 => ((4 : Fin 5), (2 : Fin 5))
  | 3, 3, 0 => ((4 : Fin 5), (2 : Fin 5))
  | 3, 3, 1 => ((4 : Fin 5), (2 : Fin 5))
  | 3, 3, 2 => ((2 : Fin 5), (3 : Fin 5))
  | 3, 3, 3 => ((2 : Fin 5), (3 : Fin 5))
  | 3, 3, 4 => ((2 : Fin 5), (4 : Fin 5))
  | 3, 4, 0 => ((2 : Fin 5), (0 : Fin 5))
  | 3, 4, 1 => ((3 : Fin 5), (0 : Fin 5))
  | 3, 4, 2 => ((2 : Fin 5), (4 : Fin 5))
  | 3, 4, 3 => ((2 : Fin 5), (3 : Fin 5))
  | 3, 4, 4 => ((2 : Fin 5), (4 : Fin 5))
  | 4, 0, 0 => ((3 : Fin 5), (0 : Fin 5))
  | 4, 0, 1 => ((3 : Fin 5), (1 : Fin 5))
  | 4, 0, 2 => ((4 : Fin 5), (1 : Fin 5))
  | 4, 0, 3 => ((3 : Fin 5), (0 : Fin 5))
  | 4, 0, 4 => ((3 : Fin 5), (4 : Fin 5))
  | 4, 1, 0 => ((3 : Fin 5), (0 : Fin 5))
  | 4, 1, 1 => ((3 : Fin 5), (1 : Fin 5))
  | 4, 1, 2 => ((3 : Fin 5), (2 : Fin 5))
  | 4, 1, 3 => ((3 : Fin 5), (1 : Fin 5))
  | 4, 1, 4 => ((4 : Fin 5), (1 : Fin 5))
  | 4, 2, 0 => ((0 : Fin 5), (2 : Fin 5))
  | 4, 2, 1 => ((3 : Fin 5), (1 : Fin 5))
  | 4, 2, 2 => ((3 : Fin 5), (2 : Fin 5))
  | 4, 2, 3 => ((3 : Fin 5), (2 : Fin 5))
  | 4, 2, 4 => ((4 : Fin 5), (2 : Fin 5))
  | 4, 3, 0 => ((0 : Fin 5), (3 : Fin 5))
  | 4, 3, 1 => ((4 : Fin 5), (2 : Fin 5))
  | 4, 3, 2 => ((3 : Fin 5), (2 : Fin 5))
  | 4, 3, 3 => ((3 : Fin 5), (3 : Fin 5))
  | 4, 3, 4 => ((3 : Fin 5), (4 : Fin 5))
  | 4, 4, 0 => ((3 : Fin 5), (0 : Fin 5))
  | 4, 4, 1 => ((0 : Fin 5), (3 : Fin 5))
  | 4, 4, 2 => ((0 : Fin 5), (3 : Fin 5))
  | 4, 4, 3 => ((3 : Fin 5), (4 : Fin 5))
  | 4, 4, 4 => ((3 : Fin 5), (4 : Fin 5))
  | _, _, _ => ((0 : Fin 5), (0 : Fin 5))


/-- Strategy certificate for one ordered state `(a, b, c)` of `C_5`: the cops'
played pair `(d1, d2) := strat5 a b c` consists of legal moves, and either it
captures the robber outright or every robber reply strictly lowers the capture
horizon `capT5`. -/
def repOK5 (a b c : Fin 5) : Bool :=
  decide ((strat5 a b c).1 = a ∨ (strat5 a b c).1 = cw5 a ∨ (strat5 a b c).1 = ccw5 a) &&
    decide ((strat5 a b c).2 = b ∨ (strat5 a b c).2 = cw5 b ∨ (strat5 a b c).2 = ccw5 b) &&
    (decide ((strat5 a b c).1 = c ∨ (strat5 a b c).2 = c) ||
      (moves1 G5 c).all
        (fun r' => decide (capT5 (strat5 a b c).1 (strat5 a b c).2 r' < capT5 a b c)))

theorem all_nil_true2 {α : Type} (f : α → Bool) : ([] : List α).all f = true := rfl

theorem moves1_any_true {n : Nat} (G : Cyc n) {x w : Fin n} {f : Fin n → Bool}
    (hw : w = x ∨ w = G.cw x ∨ w = G.ccw x) (hf : f w = true) :
    (moves1 G x).any f = true := by
  rcases hw with h | h | h
  · rw [h] at hf
    exact any_cons_true hf
  · rw [h] at hf
    exact any_cons_tail (any_cons_true hf)
  · rw [h] at hf
    exact any_cons_tail (any_cons_tail (any_cons_true hf))

/-- Full 125-state check of the strategy certificate (kernel computation over
 the explicit tables). -/
theorem repOK5_true : ∀ a b c : Fin 5, repOK5 a b c = true := by
  intro a
  refine fin5_cases (p := fun a => ∀ b c : Fin 5, repOK5 a b c = true) ?_ ?_ ?_ ?_ ?_ a
  all_goals
    intro b
    refine fin5_cases (p := fun b => ∀ c : Fin 5, repOK5 _ b c = true) ?_ ?_ ?_ ?_ ?_ b
  all_goals
    intro c
    refine fin5_cases (p := fun c => repOK5 _ _ c = true) ?_ ?_ ?_ ?_ ?_ c
  all_goals
    decide

/-- The capture horizon is a winning certificate: from any ordered state with
`capT5 a b c ≤ K`, two cops force capture within `K` rounds. -/
theorem capT_sound : ∀ (K : Nat) (a b c : Fin 5), capT5 a b c ≤ K → win2 G5 K a b c = true := by
  intro K
  induction K with
  | zero =>
    intro a
    refine fin5_cases (p := fun a => ∀ b c : Fin 5, capT5 a b c ≤ 0 → win2 G5 0 a b c = true)
      ?_ ?_ ?_ ?_ ?_ a
    all_goals
      intro b
      refine fin5_cases (p := fun b => ∀ c : Fin 5, capT5 _ b c ≤ 0 → win2 G5 0 _ b c = true)
        ?_ ?_ ?_ ?_ ?_ b
    all_goals
      intro c
      refine fin5_cases (p := fun c => capT5 _ _ c ≤ 0 → win2 G5 0 _ _ c = true)
        ?_ ?_ ?_ ?_ ?_ c
    all_goals
      decide
  | succ K IH =>
    intro a b c h
    show (moves1 G5 a).any
      (fun d1 => (moves1 G5 b).any fun d2 =>
        d1 == c || d2 == c ||
          ((moves1 G5 c).all fun r' => win2 G5 K d1 d2 r')) = true
    -- unpack the strategy certificate for the state (a, b, c)
    have hrep : repOK5 a b c = true := repOK5_true a b c
    have hlegs := and_true_l hrep
    have hplay := and_true_r hrep
    have hd1 : (strat5 a b c).1 = a ∨ (strat5 a b c).1 = cw5 a ∨ (strat5 a b c).1 = ccw5 a :=
      of_decide_eq_true (and_true_l hlegs)
    have hd2 : (strat5 a b c).2 = b ∨ (strat5 a b c).2 = cw5 b ∨ (strat5 a b c).2 = ccw5 b :=
      of_decide_eq_true (and_true_r hlegs)
    have hdec : ((strat5 a b c).1 = c ∨ (strat5 a b c).2 = c) ∨
        ((moves1 G5 c).all
          (fun r' => decide (capT5 (strat5 a b c).1 (strat5 a b c).2 r' < capT5 a b c))) = true := by
      rcases or_true_cases hplay with he | hall
      · exact Or.inl (of_decide_eq_true he)
      · exact Or.inr hall
    -- the cops' played pair wins the round
    have hinner : ((fun d2 => (strat5 a b c).1 == c || d2 == c ||
        ((moves1 G5 c).all fun r' => win2 G5 K (strat5 a b c).1 d2 r'))
          (strat5 a b c).2) = true := by
      show ((strat5 a b c).1 == c || (strat5 a b c).2 == c ||
        ((moves1 G5 c).all fun r' => win2 G5 K (strat5 a b c).1 (strat5 a b c).2 r')) = true
      rcases hdec with he | hall
      · rcases he with he | he
        · exact or3l (beq_true_of_eq he)
        · exact or3ml (beq_true_of_eq he)
      · have e1 := and_true_l hall
        have e2 := and_true_l (and_true_r hall)
        have e3 := and_true_l (and_true_r (and_true_r hall))
        have w1 : win2 G5 K (strat5 a b c).1 (strat5 a b c).2 c = true := by
          have hlt : capT5 (strat5 a b c).1 (strat5 a b c).2 c < capT5 a b c := of_decide_eq_true e1
          exact IH _ _ _ (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hlt h))
        have w2 : win2 G5 K (strat5 a b c).1 (strat5 a b c).2 (cw5 c) = true := by
          have hlt : capT5 (strat5 a b c).1 (strat5 a b c).2 (cw5 c) < capT5 a b c :=
            of_decide_eq_true e2
          exact IH _ _ _ (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hlt h))
        have w3 : win2 G5 K (strat5 a b c).1 (strat5 a b c).2 (ccw5 c) = true := by
          have hlt : capT5 (strat5 a b c).1 (strat5 a b c).2 (ccw5 c) < capT5 a b c :=
            of_decide_eq_true e3
          exact IH _ _ _ (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hlt h))
        exact or3r (all_cons_true2 w1 (all_cons_true2 w2 (all_cons_true2 w3 (all_nil_true2 _))))
    -- assemble: play (strat5 a b c).1 and (strat5 a b c).2
    exact moves1_any_true G5 hd1 (moves1_any_true G5 hd2 hinner)

/-- Two cops always capture on `C_5`, within `capT5 a b c ≤ 2` rounds. -/
theorem two_cops_win : ∀ a b c : Fin 5, win2 G5 (capT5 a b c) a b c = true :=
  fun a b c => capT_sound (capT5 a b c) a b c (Nat.le_refl (capT5 a b c))

/-- The worst-case capture horizon on `C_5` is 2 rounds. -/
theorem capT5_le : ∀ a b c : Fin 5, capT5 a b c ≤ 2 := by
  intro a
  refine fin5_cases (p := fun a => ∀ b c : Fin 5, capT5 a b c ≤ 2) ?_ ?_ ?_ ?_ ?_ a
  all_goals
    intro b
    refine fin5_cases (p := fun b => ∀ c : Fin 5, capT5 _ b c ≤ 2) ?_ ?_ ?_ ?_ ?_ b
  all_goals
    intro c
    refine fin5_cases (p := fun c => capT5 _ _ c ≤ 2) ?_ ?_ ?_ ?_ ?_ c
  all_goals
    decide

/-! ### Part 3 — outerplanarity of `C_5` and the infinite family -/

/-- Chord crossing test on the circle with vertices `0,1,2,3,4` in cyclic
order: straight chords `(a, b)` and `(c, d)` (endpoints written with
`a < b`, `c < d`, all four distinct) cross iff they interleave. -/
def chordsCross (a b c d : Nat) : Bool :=
  (a < c && c < b && b < d) || (c < a && a < d && d < b)

/-- `C_5` drawn as a convex pentagon: the five boundary edges
`(0,1), (1,2), (2,3), (3,4), (0,4)`.  Of the 10 edge pairs, 5 share an
endpoint (no crossing by definition) and the 5 disjoint pairs are checked
here — none crosses, so the pentagon IS an outer embedding (all vertices on
the boundary face). -/
def noCross5 : Bool :=
  chordsCross 0 1 2 3 = false && chordsCross 0 1 3 4 = false &&
    chordsCross 1 2 3 4 = false && chordsCross 1 2 0 4 = false &&
    chordsCross 2 3 0 4 = false

theorem outer5 : noCross5 = true := by decide

/-- The cycle graph `C_n` as a dependent pair: vertex count plus symmetric
adjacency on `Fin n` (`i ~ j` iff `j = i ± 1 mod n`). -/
def cycleGraph (n : Nat) : Σ n : Nat, (Fin n → Fin n → Bool) :=
  ⟨n, fun i j => ((i.val + 1) % n == j.val || (i.val + n - 1) % n == j.val) || (i.val == j.val && n == 1)⟩

/-- Distinct family members have distinct vertex counts; vertex count is an
isomorphism invariant (a bijection `Fin m ≃ Fin n` forces `m = n`), so the
members `C_4, C_5, C_6, …` are pairwise non-isomorphic. -/
theorem cycle_count_inj (m n : Nat) (h : (cycleGraph m).1 = (cycleGraph n).1) : m = n := h

/-! ### Headline -/

/-- Disproof certificate for conjecture 00000001215.

The conjecture asserts that the cop number of an outerplanar graph is at most
two **with only finitely many graphs attaining the bound up to isomorphism**.
The components below certify the attack:

1. one cop never wins on ANY cycle (`Cyc`, all `n`) — cop number `≥ 2`;
2. two cops always win on `C_5` — cop number `≤ 2`, so `C_5` ATTAINS the
   bound (capture within `capT5 ≤ 2` rounds);
3. `C_5` has a straight-line outer embedding — it IS outerplanar;
4. the family `n ↦ C_n` is injective on vertex counts, hence pairwise
   non-isomorphic; by the polygon argument (text) every `C_n`, `n ≥ 4`, is
   outerplanar with cop number exactly 2 — infinitely many counterexamples to
   the finitude claim. -/
theorem disproof_00000001215 :
    (∀ (n : Nat) (G : Cyc n) (c : Fin n), ¬ ∃ k : Nat, ∀ r : Fin n, win1 G k c r = true) ∧
      (∀ a b c : Fin 5, win2 G5 (capT5 a b c) a b c = true) ∧
      (∀ a b c : Fin 5, capT5 a b c ≤ 2) ∧
      (noCross5 = true) ∧
      (∀ m n : Nat, (cycleGraph m).1 = (cycleGraph n).1 → m = n) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact fun n G c => one_cop_never_wins G c
  · exact two_cops_win
  · exact capT5_le
  · exact outer5
  · exact cycle_count_inj

end TLMC1215
