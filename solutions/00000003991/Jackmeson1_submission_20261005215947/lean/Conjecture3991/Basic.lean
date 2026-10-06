import Mathlib

/-!
# Conjecture 00000003991 (functional PHP and cutting planes): disproof

The conjecture asserts that every cutting-plane (CP) refutation of the functional pigeonhole
principle `PHP_n` (`n+1` pigeons, `n` holes) has length at least `2^(n/8)`, and that the
constant `1/8` cannot be improved for CP with bounded coefficients.

We build the CP proof system from scratch (lines are integer linear inequalities `a·x ≥ b`;
rules: Boolean axioms `x ≥ 0`, `-x ≥ -1`, positive integer linear combination of two earlier
lines, and division with ceiling rounding when the divisor divides every coefficient; the
length of a refutation is its number of lines). We then construct, for every `n ≥ 1`, an
explicit CP refutation of the functional `PHP_n` with at most `8 n^3` lines, in which every
coefficient and every constant term has absolute value at most `2n`. Consequently, for every
`ε > 0` and `c > 0`, for all large `n` there is a refutation shorter than `c · 2^(ε n)`, so
there is no lower bound `2^(n/8)` (nor `c · 2^(n/8)`), even for CP restricted to coefficients
bounded by `2n`.
-/

open Filter Asymptotics

namespace C3991

section CP

variable {V : Type} [DecidableEq V]

/-- A line `(a, b)` of a cutting-plane proof stands for the inequality `∑ v, a v * x v ≥ b`. -/
abbrev Line (V : Type) := (V → ℤ) × ℤ

/-- The contradictory line `0 ≥ 1`. -/
def falsum : Line V := (0, 1)

/-- One inference of the Cutting Planes system, from the axiom set `Ax` and the earlier lines
`prev`: an axiom of `Ax`, a Boolean axiom `x_v ≥ 0` or `-x_v ≥ -1`, a linear combination
`α A + β B` of two earlier lines with positive integers `α, β`, or the division (rounding) rule:
from an earlier line `A` and a positive integer `α` dividing every coefficient of `A`, infer
`(A/α) x ≥ ⌈A.2 / α⌉`. -/
inductive Step (Ax : Set (Line V)) (prev : List (Line V)) : Line V → Prop
  | ax {L : Line V} : L ∈ Ax → Step Ax prev L
  | boolLow (v : V) : Step Ax prev (Pi.single v 1, 0)
  | boolUp (v : V) : Step Ax prev (Pi.single v (-1), -1)
  | comb {A B : Line V} {α β : ℤ} : A ∈ prev → B ∈ prev → 0 < α → 0 < β →
      Step Ax prev (α • A + β • B)
  | round {A : Line V} {α : ℤ} : A ∈ prev → 0 < α → (∀ v, α ∣ A.1 v) →
      Step Ax prev (fun v => A.1 v / α, ⌈(A.2 : ℚ) / (α : ℚ)⌉)

/-- A CP derivation from `Ax`: a list of lines, each inferred by one `Step` from the lines
strictly before it. -/
def IsDerivation (Ax : Set (Line V)) (l : List (Line V)) : Prop :=
  ∀ k (hk : k < l.length), Step Ax (l.take k) l[k]

/-- A CP refutation of `Ax`: a derivation whose last line is `0 ≥ 1`.
Its length is `l.length`, the number of lines. -/
def IsRefutation (Ax : Set (Line V)) (l : List (Line V)) : Prop :=
  IsDerivation Ax l ∧ l.getLast? = some falsum

/-- All coefficients and the constant term of a line have absolute value at most `B`. -/
def Bdd (B : ℕ) (L : Line V) : Prop := (∀ v, |L.1 v| ≤ B) ∧ |L.2| ≤ B

theorem Step.mono {Ax : Set (Line V)} {prev prev' : List (Line V)}
    (h : ∀ A ∈ prev, A ∈ prev') {L : Line V} : Step Ax prev L → Step Ax prev' L
  | .ax hL => .ax hL
  | .boolLow v => .boolLow v
  | .boolUp v => .boolUp v
  | .comb hA hB ha hb => .comb (h _ hA) (h _ hB) ha hb
  | .round hA ha hd => .round (h _ hA) ha hd

theorem IsDerivation.snoc {Ax : Set (Line V)} {l : List (Line V)} (hl : IsDerivation Ax l)
    {L : Line V} (hL : Step Ax l L) : IsDerivation Ax (l ++ [L]) := by
  intro k hk
  rw [List.length_append, List.length_singleton] at hk
  rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk' | rfl
  · rw [List.getElem_append_left hk', List.take_append_of_le_length hk'.le]
    exact hl k hk'
  · simpa using hL

theorem IsDerivation.take {Ax : Set (Line V)} {l : List (Line V)} (hl : IsDerivation Ax l)
    (p : ℕ) : IsDerivation Ax (l.take p) := by
  intro k hk
  rw [List.length_take] at hk
  have hkp : k < p := lt_of_lt_of_le hk (min_le_left _ _)
  have hkl : k < l.length := lt_of_lt_of_le hk (min_le_right _ _)
  rw [List.getElem_take, List.take_take, min_eq_left hkp.le]
  exact hl k hkl

/-- Derivations with all lines bounded by `B`. -/
def Good (Ax : Set (Line V)) (B : ℕ) (l : List (Line V)) : Prop :=
  IsDerivation Ax l ∧ ∀ A ∈ l, Bdd B A

theorem Good.snoc {Ax : Set (Line V)} {B : ℕ} {l : List (Line V)} (hl : Good Ax B l)
    {L : Line V} (hL : Step Ax l L) (hB : Bdd B L) : Good Ax B (l ++ [L]) := by
  refine ⟨hl.1.snoc hL, fun A hA => ?_⟩
  rcases List.mem_append.1 hA with h | h
  · exact hl.2 A h
  · rw [List.mem_singleton.1 h]; exact hB

/-- If a bounded derivation contains `0 ≥ 1`, truncating it gives a bounded refutation. -/
theorem refutation_of_mem {Ax : Set (Line V)} {B : ℕ} {l : List (Line V)} (hl : Good Ax B l)
    (h : falsum ∈ l) :
    ∃ l', IsRefutation Ax l' ∧ l'.length ≤ l.length ∧ ∀ L ∈ l', Bdd B L := by
  obtain ⟨i, hi, hfi⟩ := List.getElem_of_mem h
  refine ⟨l.take (i + 1), ⟨hl.1.take _, ?_⟩, by simp, fun L hL => hl.2 L (List.mem_of_mem_take hL)⟩
  rw [List.getLast?_eq_getElem?]
  simp [List.length_take, Nat.min_eq_left (Nat.succ_le_of_lt hi), hfi]

end CP

/-! ## The functional pigeonhole principle -/

/-- Variables `x (i, j)`, "pigeon `i` sits in hole `j`", for `n+1` pigeons and `n` holes. -/
abbrev Var (n : ℕ) := Fin (n + 1) × Fin n

variable {n : ℕ}

/-- Pigeon axiom: `∑_j x (i, j) ≥ 1`. -/
def pigeonAx (i : Fin (n + 1)) : Line (Var n) := (fun v => if v.1 = i then 1 else 0, 1)

/-- Hole axiom `x (i, j) + x (i', j) ≤ 1`, written `-x (i, j) - x (i', j) ≥ -1`. -/
def holeAx (i i' : Fin (n + 1)) (j : Fin n) : Line (Var n) :=
  (fun v => if (v.1 = i ∨ v.1 = i') ∧ v.2 = j then -1 else 0, -1)

/-- Functionality axiom `x (i, j) + x (i, j') ≤ 1`, written `-x (i, j) - x (i, j') ≥ -1`. -/
def funAx (i : Fin (n + 1)) (j j' : Fin n) : Line (Var n) :=
  (fun v => if v.1 = i ∧ (v.2 = j ∨ v.2 = j') then -1 else 0, -1)

/-- The functional pigeonhole principle `PHP_n` as a set of CP axioms: every pigeon is in some
hole, no two distinct pigeons share a hole, and no pigeon is in two distinct holes. -/
def FPHP (n : ℕ) : Set (Line (Var n)) :=
  {L | (∃ i, L = pigeonAx i) ∨ (∃ i i' j, i ≠ i' ∧ L = holeAx i i' j) ∨
    (∃ i j j', j ≠ j' ∧ L = funAx i j j')}

theorem hole_mem {i i' : Fin (n + 1)} (h : i ≠ i') (j : Fin n) : holeAx i i' j ∈ FPHP n :=
  Or.inr (Or.inl ⟨i, i', j, h, rfl⟩)

theorem pigeon_mem (i : Fin (n + 1)) : pigeonAx i ∈ FPHP n := Or.inl ⟨i, rfl⟩

/-- `x` satisfies the line `L`. -/
def Sat (L : Line (Var n)) (x : Var n → ℤ) : Prop := L.2 ≤ ∑ v, L.1 v * x v

theorem sum_two {a b : Var n} (hab : a ≠ b) (c x : Var n → ℤ)
    (hc : ∀ v, c v = if v = a ∨ v = b then -1 else 0) : ∑ v, c v * x v = -(x a + x b) := by
  rw [Fintype.sum_eq_add a b hab]
  · simp [hc, hab, hab.symm]; ring
  · intro v hv; simp [hc, hv.1, hv.2]

theorem sat_pigeon (i : Fin (n + 1)) (x : Var n → ℤ) :
    Sat (pigeonAx i) x ↔ 1 ≤ ∑ j, x (i, j) := by
  unfold Sat
  rw [Fintype.sum_prod_type, Finset.sum_eq_single i]
  · simp [pigeonAx]
  · intro b _ hb; simp [pigeonAx, hb]
  · simp

theorem sat_hole {i i' : Fin (n + 1)} (h : i ≠ i') (j : Fin n) (x : Var n → ℤ) :
    Sat (holeAx i i' j) x ↔ x (i, j) + x (i', j) ≤ 1 := by
  unfold Sat
  rw [sum_two (a := (i, j)) (b := (i', j)) (by simp [h]) _ _ (fun v => by
    simp only [holeAx, Prod.ext_iff]; congr 1; apply propext; tauto)]
  simp only [holeAx]; omega

theorem sat_fun (i : Fin (n + 1)) {j j' : Fin n} (h : j ≠ j') (x : Var n → ℤ) :
    Sat (funAx i j j') x ↔ x (i, j) + x (i, j') ≤ 1 := by
  unfold Sat
  rw [sum_two (a := (i, j)) (b := (i, j')) (by simp [h]) _ _ (fun v => by
    simp only [funAx, Prod.ext_iff]; congr 1; apply propext; tauto)]
  simp only [funAx]; omega

/-- **Faithfulness of the encoding.** A `0/1` assignment satisfies all axioms of `FPHP n`
exactly when it is the graph of an injective map from the `n+1` pigeons to the `n` holes. -/
theorem fphp_sat_iff (x : Var n → ℤ) (hx : ∀ v, x v = 0 ∨ x v = 1) :
    (∀ L ∈ FPHP n, Sat L x) ↔
      ∃ f : Fin (n + 1) → Fin n, Function.Injective f ∧ ∀ v, x v = if f v.1 = v.2 then 1 else 0 := by
  constructor
  · intro hS
    have hex : ∀ i, ∃ j, x (i, j) = 1 := by
      intro i
      by_contra hne
      simp only [not_exists] at hne
      have h0 : ∀ j, x (i, j) = 0 := fun j => (hx (i, j)).resolve_right (hne j)
      have := (sat_pigeon i x).1 (hS _ (pigeon_mem i))
      simp [h0] at this
    choose f hf using hex
    have hiff : ∀ i j, x (i, j) = 1 ↔ f i = j := by
      intro i j
      refine ⟨fun h1 => ?_, fun h => h ▸ hf i⟩
      by_contra hne
      have := (sat_fun i hne x).1 (hS _ (Or.inr (Or.inr ⟨i, f i, j, hne, rfl⟩)))
      rw [hf i, h1] at this; omega
    refine ⟨f, fun i i' hii => ?_, fun v => ?_⟩
    · by_contra hne
      have := (sat_hole hne (f i) x).1 (hS _ (hole_mem hne _))
      rw [(hiff i (f i)).2 rfl, (hiff i' (f i)).2 hii.symm] at this; omega
    · split_ifs with h
      · exact (hiff v.1 v.2).2 h
      · exact (hx v).resolve_right (fun h1 => h ((hiff v.1 v.2).1 h1))
  · rintro ⟨f, hinj, hfx⟩ L hL
    rcases hL with ⟨i, rfl⟩ | ⟨i, i', j, h, rfl⟩ | ⟨i, j, j', h, rfl⟩
    · rw [sat_pigeon]; simp [hfx]
    · rw [sat_hole h, hfx, hfx]
      have : ¬ (f i = j ∧ f i' = j) := fun ⟨h1, h2⟩ => h (hinj (h1.trans h2.symm))
      split_ifs <;> simp_all
    · rw [sat_fun i h, hfx, hfx]
      split_ifs with h1 h2 <;> simp_all

/-- Consequently no `0/1` assignment satisfies `FPHP n`: there is no injection `n+1 → n`. -/
theorem fphp_unsat (x : Var n → ℤ) (hx : ∀ v, x v = 0 ∨ x v = 1) : ¬ ∀ L ∈ FPHP n, Sat L x := by
  rw [fphp_sat_iff x hx]
  rintro ⟨f, hf, -⟩
  have := Fintype.card_le_of_injective f hf
  simp at this

/-! ### The explicit refutation -/

/-- `T j m`: `-∑_{i < m} x (i, j) ≥ -1` (at most one of the first `m` pigeons is in hole `j`). -/
def T (j : Fin n) (m : ℕ) : Line (Var n) :=
  (fun v => if v.2 = j ∧ (v.1 : ℕ) < m then -1 else 0, -1)

/-- `C j m k = (m-1) T j m + ∑_{i ≤ k} holeAx i m j`. -/
def C (j : Fin n) (m k : ℕ) : Line (Var n) :=
  (fun v => if v.2 = j then
      ((if (v.1 : ℕ) < m then -((m : ℤ) - 1) else 0) - (if (v.1 : ℕ) ≤ k then 1 else 0) -
        (if (v.1 : ℕ) = m then (k : ℤ) + 1 else 0)) else 0,
    -((m : ℤ) - 1) - ((k : ℤ) + 1))

/-- `G k = ∑_{i ≤ k} pigeonAx i`. -/
def G (k : ℕ) : Line (Var n) := (fun v => if (v.1 : ℕ) ≤ k then 1 else 0, (k : ℤ) + 1)

/-- `H k = G n + ∑_{j < k} T j (n+1)`. -/
def H (k : ℕ) : Line (Var n) := (fun v => if (v.2 : ℕ) < k then 0 else 1, (n : ℤ) + 1 - k)

theorem T_two (hn : 1 ≤ n) (j : Fin n) : T j 2 = holeAx ⟨0, by omega⟩ ⟨1, by omega⟩ j := by
  refine Prod.ext (funext fun v => ?_) rfl
  simp only [T, holeAx, Fin.ext_iff]
  split_ifs <;> omega

theorem C_zero (j : Fin n) {m : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    C j m 0 = ((m : ℤ) - 1) • T j m + (1 : ℤ) • holeAx ⟨0, by omega⟩ ⟨m, by omega⟩ j := by
  refine Prod.ext (funext fun v => ?_) ?_
  · simp only [C, T, holeAx, Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Fin.ext_iff]
    split_ifs <;> omega
  · simp [C, T, holeAx]; ring

theorem C_succ (j : Fin n) {m k : ℕ} (hk : k + 1 < m) (hmn : m ≤ n) :
    C j m (k + 1) = (1 : ℤ) • C j m k + (1 : ℤ) • holeAx ⟨k + 1, by omega⟩ ⟨m, by omega⟩ j := by
  refine Prod.ext (funext fun v => ?_) ?_
  · simp only [C, holeAx, Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Fin.ext_iff]
    split_ifs <;> push_cast <;> omega
  · simp [C, holeAx]; ring

theorem C_last_coeff (j : Fin n) {m : ℕ} (hm : 1 ≤ m) (v : Var n) :
    (C j m (m - 1)).1 v = (m : ℤ) * (T j (m + 1)).1 v := by
  simp only [C, T, Fin.ext_iff]
  split_ifs <;> omega

theorem round_C (j : Fin n) {m : ℕ} (hm : 1 ≤ m) :
    ((fun v => (C j m (m - 1)).1 v / (m : ℤ)),
      ⌈((C j m (m - 1)).2 : ℚ) / (((m : ℤ) : ℚ))⌉) = T j (m + 1) := by
  have hm0 : (m : ℤ) ≠ 0 := by omega
  refine Prod.ext (funext fun v => ?_) ?_
  · simp only [C_last_coeff j hm v]
    exact Int.mul_ediv_cancel_left _ hm0
  · have h2 : ((C j m (m - 1)).2 : ℚ) = -(2 * (m : ℚ) - 1) := by
      simp only [C]; push_cast [Nat.cast_sub hm]; ring
    have hmq : (0 : ℚ) < m := by exact_mod_cast hm
    have hm1 : (1 : ℚ) ≤ m := by exact_mod_cast hm
    rw [h2, Int.cast_natCast, Int.ceil_eq_iff]
    simp only [T]
    constructor
    · rw [lt_div_iff₀ hmq]; push_cast; linarith
    · rw [div_le_iff₀ hmq]; push_cast; linarith

/-! ### Coefficient bounds -/

theorem bdd_hole (hn : 1 ≤ n) (i i' : Fin (n + 1)) (j : Fin n) : Bdd (2 * n) (holeAx i i' j) := by
  refine ⟨fun v => ?_, ?_⟩ <;> simp only [holeAx] <;> (try split_ifs) <;> simp <;> omega

theorem bdd_pigeon (hn : 1 ≤ n) (i : Fin (n + 1)) : Bdd (2 * n) (pigeonAx i) := by
  refine ⟨fun v => ?_, ?_⟩ <;> simp only [pigeonAx] <;> (try split_ifs) <;> simp <;> omega

theorem bdd_T (hn : 1 ≤ n) (j : Fin n) (m : ℕ) : Bdd (2 * n) (T j m) := by
  refine ⟨fun v => ?_, ?_⟩ <;> simp only [T] <;> (try split_ifs) <;> simp <;> omega

theorem bdd_C (j : Fin n) {m k : ℕ} (hk : k < m) (hmn : m ≤ n) : Bdd (2 * n) (C j m k) := by
  refine ⟨fun v => ?_, ?_⟩ <;> simp only [C] <;> (try split_ifs) <;> rw [abs_le] <;>
    constructor <;> push_cast <;> omega

theorem bdd_G (hn : 1 ≤ n) {k : ℕ} (hk : k ≤ n) : Bdd (2 * n) (G (n := n) k) := by
  refine ⟨fun v => ?_, ?_⟩ <;> simp only [G] <;> (try split_ifs) <;> rw [abs_le] <;>
    constructor <;> push_cast <;> omega

theorem bdd_H (hn : 1 ≤ n) {k : ℕ} (hk : k ≤ n) : Bdd (2 * n) (H (n := n) k) := by
  refine ⟨fun v => ?_, ?_⟩ <;> simp only [H] <;> (try split_ifs) <;> rw [abs_le] <;>
    constructor <;> push_cast <;> omega

/-! ### Building the refutation -/

/-- The state "a bounded derivation `l'` extending `l` by at most `k` lines contains `L`". -/
def Reach (l : List (Line (Var n))) (k : ℕ) (L : Line (Var n)) : Prop :=
  ∃ l', Good (FPHP n) (2 * n) l' ∧ (∀ A ∈ l, A ∈ l') ∧ l'.length ≤ l.length + k ∧ L ∈ l'

theorem reach_snoc {l : List (Line (Var n))} (hl : Good (FPHP n) (2 * n) l) {L : Line (Var n)}
    (hL : Step (FPHP n) l L) (hB : Bdd (2 * n) L) : Reach l 1 L :=
  ⟨l ++ [L], hl.snoc hL hB, fun A hA => List.mem_append_left _ hA, by simp, by simp⟩

/-- From `T j m` (with `2 ≤ m ≤ n`) derive `T j (m+1)` with at most `2n+1` new lines. -/
theorem hole_step (j : Fin n) {m : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n)
    {l : List (Line (Var n))} (hl : Good (FPHP n) (2 * n) l) (hT : T j m ∈ l) :
    Reach l (2 * n + 1) (T j (m + 1)) := by
  have hne : ∀ k (hk : k < m), (⟨k, by omega⟩ : Fin (n + 1)) ≠ ⟨m, by omega⟩ := by
    intro k hk h; simp [Fin.ext_iff] at h; omega
  have inner : ∀ k, k < m → Reach l (2 * (k + 1)) (C j m k) := by
    intro k
    induction k with
    | zero =>
      intro hk
      obtain ⟨l1, g1, s1, n1, m1⟩ := reach_snoc hl (Step.ax (hole_mem (hne 0 hk) j))
        (bdd_hole (by omega) _ _ j)
      obtain ⟨l2, g2, s2, n2, m2⟩ := reach_snoc g1 (L := C j m 0)
        (by rw [C_zero j (by omega) hmn]; exact Step.comb (s1 _ hT) m1 (by omega) one_pos) (bdd_C j hk hmn)
      exact ⟨l2, g2, fun A hA => s2 _ (s1 _ hA), by omega, m2⟩
    | succ k ih =>
      intro hk
      obtain ⟨l0, g0, s0, n0, m0⟩ := ih (by omega)
      obtain ⟨l1, g1, s1, n1, m1⟩ := reach_snoc g0 (Step.ax (hole_mem (hne (k + 1) hk) j))
        (bdd_hole (by omega) _ _ j)
      obtain ⟨l2, g2, s2, n2, m2⟩ := reach_snoc g1 (L := C j m (k + 1))
        (by rw [C_succ j hk hmn]; exact Step.comb (s1 _ m0) m1 one_pos one_pos) (bdd_C j hk hmn)
      exact ⟨l2, g2, fun A hA => s2 _ (s1 _ (s0 _ hA)), by omega, m2⟩
  obtain ⟨l1, g1, s1, n1, m1⟩ := inner (m - 1) (by omega)
  have hstep : Step (FPHP n) l1 (T j (m + 1)) := by
    rw [← round_C j (by omega)]
    exact Step.round m1 (by omega) (fun v => by rw [C_last_coeff j (by omega)]; exact dvd_mul_right _ _)
  obtain ⟨l2, g2, s2, n2, m2⟩ := reach_snoc g1 hstep (bdd_T (by omega) j _)
  refine ⟨l2, g2, fun A hA => s2 _ (s1 _ hA), ?_, m2⟩
  have : 2 * (m - 1 + 1) ≤ 2 * n := by omega
  omega

/-- For one hole `j`, derive `T j (n+1)`: `-∑_i x (i, j) ≥ -1`. -/
theorem hole_full (hn : 1 ≤ n) (j : Fin n) {l : List (Line (Var n))}
    (hl : Good (FPHP n) (2 * n) l) : Reach l (1 + n * (2 * n + 1)) (T j (n + 1)) := by
  have key : ∀ t, t + 2 ≤ n + 1 → Reach l (1 + t * (2 * n + 1)) (T j (t + 2)) := by
    intro t
    induction t with
    | zero =>
      intro _
      obtain ⟨l1, g1, s1, n1, m1⟩ := reach_snoc hl (L := T j 2)
        (by rw [T_two hn j]; exact Step.ax (hole_mem (by simp [Fin.ext_iff]) j)) (bdd_T hn j 2)
      exact ⟨l1, g1, s1, by omega, m1⟩
    | succ t ih =>
      intro ht
      obtain ⟨l1, g1, s1, n1, m1⟩ := ih (by omega)
      obtain ⟨l2, g2, s2, n2, m2⟩ := hole_step j (m := t + 2) (by omega) (by omega) g1 m1
      refine ⟨l2, g2, fun A hA => s2 _ (s1 _ hA), ?_, m2⟩
      have : (t + 1) * (2 * n + 1) = t * (2 * n + 1) + (2 * n + 1) := by ring
      omega
  obtain ⟨l1, g1, s1, n1, m1⟩ := key (n - 1) (by omega)
  refine ⟨l1, g1, s1, ?_, by rwa [show n - 1 + 2 = n + 1 by omega] at m1⟩
  have : (n - 1) * (2 * n + 1) ≤ n * (2 * n + 1) := Nat.mul_le_mul_right _ (by omega)
  omega

/-- Derive `T j (n+1)` for every hole `j`. -/
theorem all_holes (hn : 1 ≤ n) : ∀ t ≤ n, ∃ l, Good (FPHP n) (2 * n) l ∧
    l.length ≤ t * (1 + n * (2 * n + 1)) ∧ ∀ j : Fin n, (j : ℕ) < t → T j (n + 1) ∈ l := by
  intro t
  induction t with
  | zero => exact fun _ => ⟨[], ⟨fun k hk => by simp at hk, by simp⟩, by simp, fun j hj => by omega⟩
  | succ t ih =>
    intro ht
    obtain ⟨l1, g1, n1, m1⟩ := ih (by omega)
    obtain ⟨l2, g2, s2, n2, m2⟩ := hole_full hn ⟨t, by omega⟩ g1
    refine ⟨l2, g2, by rw [Nat.succ_mul]; omega, fun j hj => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | h
    · exact s2 _ (m1 j h)
    · have : j = ⟨t, by omega⟩ := Fin.ext h
      rw [this]; exact m2

theorem G_zero : G (n := n) 0 = pigeonAx 0 := by
  refine Prod.ext (funext fun v => ?_) rfl
  simp only [G, pigeonAx, Fin.ext_iff, Fin.val_zero]
  split_ifs <;> omega

theorem G_succ {k : ℕ} (hk : k + 1 ≤ n) :
    G (n := n) (k + 1) = (1 : ℤ) • G k + (1 : ℤ) • pigeonAx ⟨k + 1, by omega⟩ := by
  refine Prod.ext (funext fun v => ?_) ?_
  · simp only [G, pigeonAx, Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Fin.ext_iff]
    split_ifs <;> omega
  · simp [G, pigeonAx]

/-- Sum the pigeon axioms: derive `G k = ∑_{i ≤ k} pigeonAx i`. -/
theorem pigeons (hn : 1 ≤ n) {l : List (Line (Var n))} (hl : Good (FPHP n) (2 * n) l) :
    ∀ k ≤ n, Reach l (2 * k + 1) (G k) := by
  intro k
  induction k with
  | zero =>
    intro _
    obtain ⟨l1, g1, s1, n1, m1⟩ := reach_snoc hl (L := G 0)
      (by rw [G_zero]; exact Step.ax (pigeon_mem 0)) (bdd_G hn (by omega))
    exact ⟨l1, g1, s1, by omega, m1⟩
  | succ k ih =>
    intro hk
    obtain ⟨l0, g0, s0, n0, m0⟩ := ih (by omega)
    obtain ⟨l1, g1, s1, n1, m1⟩ := reach_snoc g0 (Step.ax (pigeon_mem ⟨k + 1, by omega⟩))
      (bdd_pigeon hn _)
    obtain ⟨l2, g2, s2, n2, m2⟩ := reach_snoc g1 (L := G (k + 1))
      (by rw [G_succ hk]; exact Step.comb (s1 _ m0) m1 one_pos one_pos) (bdd_G hn hk)
    exact ⟨l2, g2, fun A hA => s2 _ (s1 _ (s0 _ hA)), by omega, m2⟩

theorem H_zero : H (n := n) 0 = G n := by
  refine Prod.ext (funext fun v => ?_) (by simp [H, G])
  simp only [H, G]
  have := v.1.isLt
  split_ifs <;> omega

theorem H_succ {k : ℕ} (hk : k < n) :
    H (n := n) (k + 1) = (1 : ℤ) • H k + (1 : ℤ) • T ⟨k, hk⟩ (n + 1) := by
  refine Prod.ext (funext fun v => ?_) ?_
  · simp only [H, T, Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Fin.ext_iff]
    have := v.1.isLt
    split_ifs <;> omega
  · simp [H, T]; ring

theorem H_n : H (n := n) n = falsum := by
  refine Prod.ext (funext fun v => ?_) (by simp [H, falsum])
  simp [H, falsum]

/-- Add the hole lines to `G n`: derive `H k`. -/
theorem holes_sum (hn : 1 ≤ n) {l : List (Line (Var n))} (hl : Good (FPHP n) (2 * n) l)
    (hG : G n ∈ l) (hT : ∀ j : Fin n, T j (n + 1) ∈ l) : ∀ k ≤ n, Reach l k (H k) := by
  intro k
  induction k with
  | zero => exact fun _ => ⟨l, hl, fun A hA => hA, by omega, by rw [H_zero]; exact hG⟩
  | succ k ih =>
    intro hk
    obtain ⟨l0, g0, s0, n0, m0⟩ := ih (by omega)
    obtain ⟨l1, g1, s1, n1, m1⟩ := reach_snoc g0 (L := H (k + 1))
      (by rw [H_succ (by omega)]; exact Step.comb m0 (s0 _ (hT _)) one_pos one_pos)
      (bdd_H hn hk)
    exact ⟨l1, g1, fun A hA => s1 _ (s0 _ hA), by omega, m1⟩

/-- **Short refutations.** For every `n ≥ 1`, the functional pigeonhole principle `FPHP n` has
a CP refutation with at most `8 n^3` lines, all of whose coefficients and constant terms have
absolute value at most `2n`. -/
theorem fphp_short_refutation (n : ℕ) (hn : 1 ≤ n) :
    ∃ l, IsRefutation (FPHP n) l ∧ l.length ≤ 8 * n ^ 3 ∧ ∀ L ∈ l, Bdd (2 * n) L := by
  obtain ⟨l1, g1, n1, m1⟩ := all_holes hn n le_rfl
  obtain ⟨l2, g2, s2, n2, m2⟩ := pigeons hn g1 n le_rfl
  obtain ⟨l3, g3, s3, n3, m3⟩ :=
    holes_sum hn g2 m2 (fun j => s2 _ (m1 j j.isLt)) n le_rfl
  rw [H_n] at m3
  obtain ⟨l4, r4, n4, b4⟩ := refutation_of_mem g3 m3
  refine ⟨l4, r4, ?_, b4⟩
  have h1 : 1 ≤ n ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h2 : n ≤ n ^ 3 := Nat.le_self_pow (by norm_num) n
  have h3 : n ^ 2 ≤ n ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h4 : n * (1 + n * (2 * n + 1)) = 2 * n ^ 3 + n ^ 2 + n := by ring
  omega

/-- Polynomials are eventually below `c · 2^(ε n)`. -/
theorem eventually_poly_lt (K k : ℕ) {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, (K : ℝ) * (n : ℝ) ^ k < c * (2 : ℝ) ^ (ε * n) := by
  have hb : 0 < ε * Real.log 2 := mul_pos hε (Real.log_pos one_lt_two)
  have h := (isLittleO_pow_exp_pos_mul_atTop k hb).comp_tendsto tendsto_natCast_atTop_atTop
  have hd : 0 < c / (2 * ((K : ℝ) + 1)) := by positivity
  filter_upwards [h.def hd] with n hn
  simp only [Function.comp, Real.norm_eq_abs, abs_pow, Nat.abs_cast, Real.abs_exp] at hn
  have he : (2 : ℝ) ^ (ε * n) = Real.exp (ε * Real.log 2 * n) := by
    rw [Real.rpow_def_of_pos two_pos]; ring_nf
  rw [he]
  have hp : 0 < Real.exp (ε * Real.log 2 * n) := Real.exp_pos _
  have hK : (K : ℝ) * (n : ℝ) ^ k ≤ ((K : ℝ) + 1) * (n : ℝ) ^ k :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have h2 : ((K : ℝ) + 1) * (n : ℝ) ^ k ≤ c / 2 * Real.exp (ε * Real.log 2 * n) := by
    have := mul_le_mul_of_nonneg_left hn (by positivity : (0 : ℝ) ≤ (K : ℝ) + 1)
    calc ((K : ℝ) + 1) * (n : ℝ) ^ k
        ≤ ((K : ℝ) + 1) * (c / (2 * ((K : ℝ) + 1)) * Real.exp (ε * Real.log 2 * n)) := this
      _ = c / 2 * Real.exp (ε * Real.log 2 * n) := by field_simp
  nlinarith

/-- For every `ε > 0` and `c > 0`, for all large `n` the functional `PHP_n` has a CP refutation
with coefficients bounded by `2n` and fewer than `c · 2^(ε n)` lines. -/
theorem fphp_subexponential {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, ∃ l, IsRefutation (FPHP n) l ∧ (∀ L ∈ l, Bdd (2 * n) L) ∧
      (l.length : ℝ) < c * (2 : ℝ) ^ (ε * n) := by
  filter_upwards [eventually_poly_lt 8 3 hε hc, eventually_ge_atTop 1] with n hn h1
  obtain ⟨l, hr, hlen, hb⟩ := fphp_short_refutation n h1
  refine ⟨l, hr, hb, lt_of_le_of_lt ?_ hn⟩
  exact_mod_cast hlen

/-- No exponential lower bound `c · 2^(ε n)` holds for CP refutations of the functional
`PHP_n`, not even for refutations whose coefficients are bounded by `2n`. -/
theorem no_exponential_lower_bound {ε : ℝ} (hε : 0 < ε) :
    ¬ ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ l, IsRefutation (FPHP n) l →
      (∀ L ∈ l, Bdd (2 * n) L) → c * (2 : ℝ) ^ (ε * n) ≤ l.length := by
  rintro ⟨c, hc, h⟩
  obtain ⟨n, hn1, hn2⟩ := (h.and (fphp_subexponential hε hc)).exists
  obtain ⟨l, hr, hb, hlt⟩ := hn2
  exact absurd (hn1 l hr hb) (not_le.2 hlt)

/-- **Conjecture 00000003991 is false.** Neither "every CP refutation of the functional `PHP_n`
has at least `2^(n/8)` lines for all large `n`" nor the same claim restricted to refutations
with coefficients bounded by `2n` holds. -/
theorem conjecture_3991_false :
    (¬ ∀ᶠ n : ℕ in atTop, ∀ l, IsRefutation (FPHP n) l → (2 : ℝ) ^ ((n : ℝ) / 8) ≤ l.length) ∧
    (¬ ∀ᶠ n : ℕ in atTop, ∀ l, IsRefutation (FPHP n) l → (∀ L ∈ l, Bdd (2 * n) L) →
      (2 : ℝ) ^ ((n : ℝ) / 8) ≤ l.length) := by
  have key := no_exponential_lower_bound (ε := 1 / 8) (by norm_num)
  have e : ∀ n : ℕ, (2 : ℝ) ^ ((n : ℝ) / 8) = 1 * (2 : ℝ) ^ (1 / 8 * (n : ℝ)) := by
    intro n; rw [one_mul]; ring_nf
  refine ⟨fun h => key ⟨1, one_pos, ?_⟩, fun h => key ⟨1, one_pos, ?_⟩⟩
  · filter_upwards [h] with n hn l hl _
    rw [← e]; exact hn l hl
  · filter_upwards [h] with n hn l hl hb
    rw [← e]; exact hn l hl hb

end C3991
