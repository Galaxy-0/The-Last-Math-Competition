/-!
# Conjecture 00000009617: Fischer cover size versus Hankel rank

The conjecture claims (among other things) that

  "The Fisher minimal state count of a sofic shift equals the rank of the
   Hankel matrix of its language."

We refute this clause with the **even shift** `X`: the set of bi-infinite
binary sequences `x : ℤ → {0,1}` that contain no block `0 1^(2k+1) 0`
(every run of 1s between two 0s has even length).

* `X` is sofic.  Its minimal right-resolving presentation (Fischer cover) has
  exactly 2 states, and in fact *no* presentation of any kind has fewer than
  2 states (`fisher_count`, `min_presentation_count`).  Presentations are
  labelled graphs, and the shift they present is the set of label sequences
  of bi-infinite paths; this is proved from scratch, in both directions, for
  the 2-state graph `fisher` (`fisher_sound`, `fisher_complete`).
* The language `L(X)` (blocks that occur in points of `X`) is characterised
  for *all* words (`lang_iff`).  The Hankel matrix `H[u][v] = [uv ∈ L(X)]`
  has a 3×3 minor with determinant `-1` (rows `11, 0, 01`, columns
  `0, 10, 1`).  So the rank of `H` is at least 3 over `ℚ` and over every
  `ℤ/p` (`hankel_rank_ge_three`, `hankel_rank_ge_three_mod`); the minor even
  has an integer inverse (`minor_unimodular`).
* Hence `2 ≠ rank H` and the clause is false
  (`conjecture_00000009617_false` and its variants).

Symbols: `false` is the letter 0 and `true` is the letter 1.
Everything is core Lean 4 (no Mathlib).
-/

namespace EvenShiftHankel

/-! ## Shift spaces over `{0,1}` and the even shift -/

/-- A point of the full shift: a bi-infinite binary sequence. -/
abbrev Config := Int → Bool

/-- The forbidden block `0 1^(2k+1) 0` occurs in `x` starting at position `i`. -/
def ForbiddenAt (x : Config) (i : Int) (k : Nat) : Prop :=
  x i = false ∧ (∀ t : Nat, t < 2 * k + 1 → x (i + 1 + t) = true) ∧
    x (i + (2 * k + 2)) = false

/-- The even shift: no block `0 1^(odd) 0` occurs, i.e. every run of 1s that
is bounded by 0s on both sides has even length. -/
def EvenShift (x : Config) : Prop := ∀ (i : Int) (k : Nat), ¬ ForbiddenAt x i k

/-- The word `w` occurs in `x` starting at position `i`. -/
def OccursAt (x : Config) : Int → List Bool → Prop
  | _, [] => True
  | i, a :: w => x i = a ∧ OccursAt x (i + 1) w

/-- The language `L(X)` of a shift space: all words occurring in points of `X`. -/
def Lang (X : Config → Prop) (w : List Bool) : Prop :=
  ∃ x, X x ∧ ∃ i, OccursAt x i w

/-! ## Labelled graphs, presentations, Fischer count -/

/-- A labelled graph with vertex set `Fin n` over the alphabet `{0,1}`:
`E p a q = true` iff there is an edge `p → q` with label `a`.
(Parallel edges with equal labels do not change the presented shift.) -/
abbrev LGraph (n : Nat) := Fin n → Bool → Fin n → Bool

/-- `x` is the label sequence of a bi-infinite path `… s(i) --x(i)--> s(i+1) …`. -/
def IsPathLabel {n : Nat} (E : LGraph n) (x : Config) : Prop :=
  ∃ s : Int → Fin n, ∀ i, E (s i) (x i) (s (i + 1)) = true

/-- `E` presents `X`: `X` is exactly the set of bi-infinite path labels `X_E`. -/
def Presents {n : Nat} (E : LGraph n) (X : Config → Prop) : Prop :=
  ∀ x, X x ↔ IsPathLabel E x

/-- Right-resolving: the out-edges of each vertex carry distinct labels. -/
def RightResolving {n : Nat} (E : LGraph n) : Prop :=
  ∀ p a q q', E p a q = true → E p a q' = true → q = q'

/-- A sofic shift is one that has a finite labelled-graph presentation. -/
def Sofic (X : Config → Prop) : Prop := ∃ n, ∃ E : LGraph n, Presents E X

/-- `m` is the least natural number with property `P`. -/
def MinOf (P : Nat → Prop) (m : Nat) : Prop := P m ∧ ∀ n, n < m → ¬ P n

theorem MinOf.unique {P : Nat → Prop} {m m' : Nat} (h : MinOf P m) (h' : MinOf P m') :
    m = m' := by
  rcases Nat.lt_trichotomy m m' with hl | he | hg
  · exact absurd h.1 (h'.2 m hl)
  · exact he
  · exact absurd h'.1 (h.2 m' hg)

def HasRRPresentation (X : Config → Prop) (n : Nat) : Prop :=
  ∃ E : LGraph n, RightResolving E ∧ Presents E X

def HasPresentation (X : Config → Prop) (n : Nat) : Prop :=
  ∃ E : LGraph n, Presents E X

/-- Fischer ("Fisher") minimal state count: the number of states of the minimal
right-resolving presentation, i.e. the least number of vertices of a
right-resolving presentation. -/
def IsFisherCount (X : Config → Prop) (m : Nat) : Prop := MinOf (HasRRPresentation X) m

/-- The least number of vertices of any presentation (not necessarily right-resolving). -/
def IsMinPresCount (X : Config → Prop) (m : Nat) : Prop := MinOf (HasPresentation X) m

/-! ## Hankel matrix of the language and its rank -/

section
open Classical

/-- Hankel matrix entry `H[u][v] = 1` if `uv ∈ L(X)` and `0` otherwise. -/
noncomputable def hankelEntry (X : Config → Prop) (u v : List Bool) : Int :=
  if Lang X (u ++ v) then 1 else 0

end

/-- The finite submatrix of the Hankel matrix with the given rows and columns. -/
noncomputable def minor (X : Config → Prop) (rows cols : List (List Bool)) : List (List Int) :=
  rows.map (fun u => cols.map (fun v => hankelEntry X u v))

/-- Determinant by Laplace expansion along the first row (the first argument is
the size). -/
def detAux : Nat → List (List Int) → Int
  | 0, _ => 1
  | n + 1, M =>
    match M with
    | [] => 0
    | r :: rest =>
      ((List.range (n + 1)).map (fun j =>
        (if j % 2 = 0 then (1 : Int) else -1) * r.getD j 0 *
          detAux n (rest.map (fun row => row.eraseIdx j)))).foldr (· + ·) 0

/-- Determinant of a square matrix given as a list of rows. -/
def det (M : List (List Int)) : Int := detAux M.length M

/-- Rank over `ℚ` is at least `r`: some `r × r` minor of the Hankel matrix is
nonsingular (nonzero integer determinant). This is the determinantal rank of
the infinite matrix `H` (sup of the ranks of its finite submatrices). -/
def HankelRankAtLeast (X : Config → Prop) (r : Nat) : Prop :=
  ∃ rows cols : List (List Bool), rows.length = r ∧ cols.length = r ∧
    det (minor X rows cols) ≠ 0

/-- Rank over `ℤ/p` is at least `r` (for prime `p`: rank over the field `𝔽_p`). -/
def HankelRankAtLeastMod (p : Nat) (X : Config → Prop) (r : Nat) : Prop :=
  ∃ rows cols : List (List Bool), rows.length = r ∧ cols.length = r ∧
    ¬ ((p : Int) ∣ det (minor X rows cols))

/-- The Hankel matrix has rank exactly `m` over `ℚ`. -/
def HankelRankIs (X : Config → Prop) (m : Nat) : Prop :=
  HankelRankAtLeast X m ∧ ¬ HankelRankAtLeast X (m + 1)

/-- The Hankel matrix has rank exactly `m` over `ℤ/p`. -/
def HankelRankIsMod (p : Nat) (X : Config → Prop) (m : Nat) : Prop :=
  HankelRankAtLeastMod p X m ∧ ¬ HankelRankAtLeastMod p X (m + 1)

/-! ## The clause of the conjecture -/

/-- "The Fisher minimal state count of a sofic shift equals the rank of the
Hankel matrix of its language" (rank over `ℚ`). -/
def Claim : Prop :=
  ∀ X : Config → Prop, Sofic X → ∀ m, IsFisherCount X m → HankelRankIs X m

/-- The same clause with the rank taken over `ℤ/p`. -/
def ClaimMod (p : Nat) : Prop :=
  ∀ X : Config → Prop, Sofic X → ∀ m, IsFisherCount X m → HankelRankIsMod p X m

/-- The same clause with "Fisher count" read as the least number of states of
an arbitrary (not necessarily right-resolving) presentation. -/
def ClaimAnyPresentation : Prop :=
  ∀ X : Config → Prop, Sofic X → ∀ m, IsMinPresCount X m → HankelRankIs X m

/-! ## The language of the even shift, for all words -/

/-- The forbidden block `0 1^(2k+1) 0` occurs inside the finite word `w` at `i`. -/
def BlockAt (w : List Bool) (i k : Nat) : Prop :=
  w.getD i true = false ∧ (∀ t, t < 2 * k + 1 → w.getD (i + 1 + t) false = true) ∧
    w.getD (i + (2 * k + 2)) true = false

/-- A finite word avoids all forbidden blocks (bounded, hence decidable, form). -/
def WordOK (w : List Bool) : Prop :=
  ∀ i, i < w.length → ∀ k, k < w.length → ¬ BlockAt w i k

instance (w : List Bool) (i k : Nat) : Decidable (BlockAt w i k) := by
  unfold BlockAt; infer_instance

instance (w : List Bool) : Decidable (WordOK w) := by
  unfold WordOK; infer_instance

theorem getD_ge {w : List Bool} {i : Nat} (h : w.length ≤ i) (d : Bool) : w.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem getD_lt {w : List Bool} {i : Nat} (h : i < w.length) (d d' : Bool) :
    w.getD i d = w.getD i d' := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem wordOK_iff (w : List Bool) : WordOK w ↔ ∀ i k, ¬ BlockAt w i k := by
  constructor
  · intro h i k hb
    have hi : i < w.length := by
      apply Classical.byContradiction; intro hn
      have := hb.1; rw [getD_ge (by omega)] at this; exact Bool.noConfusion this
    have hj : i + (2 * k + 2) < w.length := by
      apply Classical.byContradiction; intro hn
      have := hb.2.2; rw [getD_ge (by omega)] at this; exact Bool.noConfusion this
    exact h i hi k (by omega) hb
  · intro h i _ k _; exact h i k

theorem occurs_get {x : Config} {w : List Bool} {i : Int} (h : OccursAt x i w) :
    ∀ j : Nat, j < w.length → ∀ d, x (i + j) = w.getD j d := by
  induction w generalizing i with
  | nil => intro j hj; simp at hj
  | cons a w ih =>
    intro j hj d
    cases j with
    | zero => simp [OccursAt] at h ⊢; exact h.1
    | succ j =>
      have h2 := ih h.2 j (by simp at hj; omega) d
      have e : i + ((j + 1 : Nat) : Int) = i + 1 + j := by omega
      rw [e, h2]; simp

theorem occurs_of_get {x : Config} {w : List Bool} {i : Int}
    (h : ∀ j : Nat, j < w.length → x (i + j) = w.getD j true) : OccursAt x i w := by
  induction w generalizing i with
  | nil => trivial
  | cons a w ih =>
    refine ⟨?_, ?_⟩
    · have := h 0 (by simp); simpa using this
    · apply ih; intro j hj
      have := h (j + 1) (by simp; omega)
      have e : i + ((j + 1 : Nat) : Int) = i + 1 + j := by omega
      rw [e] at this; simpa using this

/-- The canonical extension `… 1 1 w 1 1 …` of a finite word. -/
def ext (w : List Bool) : Config := fun i =>
  if 0 ≤ i ∧ i < w.length then w.getD i.toNat true else true

theorem ext_false {w : List Bool} {i : Int} (h : ext w i = false) :
    0 ≤ i ∧ i < w.length ∧ w.getD i.toNat true = false := by
  unfold ext at h
  by_cases hc : 0 ≤ i ∧ i < w.length
  · rw [if_pos hc] at h; exact ⟨hc.1, hc.2, h⟩
  · rw [if_neg hc] at h; exact Bool.noConfusion h

theorem ext_in {w : List Bool} {i : Int} (h0 : 0 ≤ i) (h1 : i < w.length) :
    ext w i = w.getD i.toNat true := by
  unfold ext; rw [if_pos ⟨h0, h1⟩]

theorem ext_evenShift {w : List Bool} (hw : WordOK w) : EvenShift (ext w) := by
  intro i k ⟨h0, h1, h2⟩
  obtain ⟨a0, a1, a2⟩ := ext_false h0
  obtain ⟨b0, b1, b2⟩ := ext_false h2
  refine (wordOK_iff w).1 hw i.toNat k ⟨a2, ?_, ?_⟩
  · intro t ht
    have h3 := h1 t ht
    have e : i + 1 + (t : Int) = ((i.toNat + 1 + t : Nat) : Int) := by omega
    rw [e, ext_in (by omega) (by omega)] at h3
    have e2 : ((i.toNat + 1 + t : Nat) : Int).toNat = i.toNat + 1 + t := by omega
    rw [e2] at h3
    rw [getD_lt (by omega) false true]; exact h3
  · have e : (i + (2 * k + 2 : Nat)).toNat = i.toNat + (2 * k + 2) := by omega
    have e' : i + ((2 * k + 2 : Nat) : Int) = i + (2 * (k : Int) + 2) := by omega
    rw [← e', e] at b2; exact b2

theorem ext_occurs (w : List Bool) : OccursAt (ext w) 0 w := by
  apply occurs_of_get; intro j hj
  rw [ext_in (by omega) (by omega)]; simp

/-- The language of the even shift, for every word: `w ∈ L(X)` iff `w`
contains no block `0 1^(2k+1) 0`. -/
theorem lang_iff (w : List Bool) : Lang EvenShift w ↔ WordOK w := by
  constructor
  · rintro ⟨x, hx, i, hocc⟩
    rw [wordOK_iff]
    intro j k ⟨h0, h1, h2⟩
    have hj : j < w.length := by
      apply Classical.byContradiction; intro hn
      rw [getD_ge (by omega)] at h0; exact Bool.noConfusion h0
    have hj2 : j + (2 * k + 2) < w.length := by
      apply Classical.byContradiction; intro hn
      rw [getD_ge (by omega)] at h2; exact Bool.noConfusion h2
    apply hx (i + j) k
    refine ⟨?_, ?_, ?_⟩
    · rw [occurs_get hocc j hj true]; exact h0
    · intro t ht
      have e : i + j + 1 + (t : Int) = i + ((j + 1 + t : Nat) : Int) := by omega
      rw [e, occurs_get hocc (j + 1 + t) (by omega) false]; exact h1 t ht
    · have e : i + j + (2 * (k : Int) + 2) = i + ((j + (2 * k + 2) : Nat) : Int) := by omega
      rw [e, occurs_get hocc _ hj2 true]; exact h2
  · intro hw; exact ⟨ext w, ext_evenShift hw, 0, ext_occurs w⟩

/-- So membership in `L(X)` is decidable, and `decide` evaluates it. -/
instance (w : List Bool) : Decidable (Lang EvenShift w) :=
  decidable_of_iff _ (lang_iff w).symm

theorem hankelEntry_eq (u v : List Bool) :
    hankelEntry EvenShift u v = if WordOK (u ++ v) then 1 else 0 := by
  unfold hankelEntry
  by_cases h : WordOK (u ++ v)
  · rw [if_pos ((lang_iff _).2 h), if_pos h]
  · rw [if_neg (fun h' => h ((lang_iff _).1 h')), if_neg h]

/-! ## The Fischer cover of the even shift -/

/-- The 2-state graph: `A --0--> A`, `A --1--> B`, `B --1--> A` with `A = 0`, `B = 1`. -/
def fisher : LGraph 2 := fun p a q =>
  (p.val == 0 && !a && q.val == 0) || (p.val == 0 && a && q.val == 1) ||
    (p.val == 1 && a && q.val == 0)

theorem fisher_edge : ∀ p a q, fisher p a q = true ↔
    (p = 0 ∧ a = false ∧ q = 0) ∨ (p = 0 ∧ a = true ∧ q = 1) ∨ (p = 1 ∧ a = true ∧ q = 0) := by
  decide

theorem fisher_rightResolving : RightResolving fisher := by
  unfold RightResolving; decide

/-- Irreducible: `A → B` and `B → A` are edges. Follower-separated: `0` labels a
path from `A` but not from `B`. -/
theorem fisher_irreducible_separated :
    fisher 0 true 1 = true ∧ fisher 1 true 0 = true ∧
    fisher 0 false 0 = true ∧ fisher 1 false 0 = false ∧ fisher 1 false 1 = false := by
  decide

/-- Every bi-infinite path label of the Fischer graph lies in the even shift. -/
theorem fisher_sound (x : Config) (h : IsPathLabel fisher x) : EvenShift x := by
  obtain ⟨s, hs⟩ := h
  intro i k ⟨h0, h1, h2⟩
  have hA : s (i + 1) = 0 := by
    have := (fisher_edge _ _ _).1 (hs i)
    rw [h0] at this
    rcases this with ⟨_, _, h⟩ | ⟨_, h, _⟩ | ⟨_, h, _⟩
    · exact h
    · exact Bool.noConfusion h
    · exact Bool.noConfusion h
  have key : ∀ t : Nat, t ≤ 2 * k + 1 → s (i + 1 + t) = if t % 2 = 0 then 0 else 1 := by
    intro t
    induction t with
    | zero => intro _; simpa using hA
    | succ t ih =>
      intro ht
      have hx := h1 t (by omega)
      have he := (fisher_edge _ _ _).1 (hs (i + 1 + t))
      have e : i + 1 + ((t + 1 : Nat) : Int) = i + 1 + t + 1 := by omega
      rw [e]
      rw [hx, ih (by omega)] at he
      by_cases hp : t % 2 = 0
      · rw [if_pos hp] at he
        rw [if_neg (by omega)]
        rcases he with ⟨_, h, _⟩ | ⟨_, _, h⟩ | ⟨h, _, _⟩
        · exact Bool.noConfusion h
        · exact h
        · exact absurd h (by decide)
      · rw [if_neg hp] at he
        rw [if_pos (by omega)]
        rcases he with ⟨h, _, _⟩ | ⟨h, _, _⟩ | ⟨_, _, h⟩
        · exact absurd h (by decide)
        · exact absurd h (by decide)
        · exact h
  have hB := key (2 * k + 1) (Nat.le_refl _)
  rw [if_neg (by omega)] at hB
  have he := (fisher_edge _ _ _).1 (hs (i + (2 * k + 2)))
  have e : i + (2 * (k : Int) + 2) = i + 1 + ((2 * k + 1 : Nat) : Int) := by omega
  rw [e, hB] at he
  rw [e] at h2
  rw [h2] at he
  rcases he with ⟨h, _, _⟩ | ⟨h, _, _⟩ | ⟨_, h, _⟩
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact Bool.noConfusion h

/-! ### Completeness: every point of the even shift labels a path -/

/-- `t` is the first index with `f t = false`. -/
def First (f : Nat → Bool) (t : Nat) : Prop := f t = false ∧ ∀ r, r < t → f r = true

theorem First.unique {f : Nat → Bool} {t t' : Nat} (h : First f t) (h' : First f t') :
    t = t' := by
  rcases Nat.lt_trichotomy t t' with hl | he | hg
  · have := h'.2 t hl; rw [h.1] at this; exact Bool.noConfusion this
  · exact he
  · have := h.2 t' hg; rw [h'.1] at this; exact Bool.noConfusion this

theorem First.exists {f : Nat → Bool} (t : Nat) (ht : f t = false) : ∃ t', First f t' := by
  induction t using Nat.strongRecOn with
  | ind t ih =>
    by_cases h : ∀ r, r < t → f r = true
    · exact ⟨t, ht, h⟩
    · apply Classical.byContradiction; intro hn
      apply h; intro r hr
      cases hfr : f r with
      | true => rfl
      | false => exact absurd (ih r hr hfr) hn

/-- Distance (number of 1s) to the next 0 at or after position `i`. -/
def Fwd (x : Config) (i : Int) : Nat → Bool := fun r => x (i + r)
/-- Number of 1s between the last 0 strictly before `i` and `i`. -/
def Bwd (x : Config) (i : Int) : Nat → Bool := fun r => x (i - 1 - r)

/-- The path state at position `i` is `B` (= 1) under this condition. -/
def BState (x : Config) (i : Int) : Prop :=
  (∃ t, First (Fwd x i) t ∧ t % 2 = 1) ∨
  ((¬ ∃ t : Nat, x (i + t) = false) ∧ ∃ t, First (Bwd x i) t ∧ t % 2 = 1) ∨
  ((∀ j, x j = true) ∧ i % 2 = 1)

section
open Classical

/-- The bi-infinite path through the Fischer graph read off from `x`. -/
noncomputable def pathOf (x : Config) (i : Int) : Fin 2 := if BState x i then 1 else 0

end

theorem bstate_of_zero {x : Config} {i : Int} (h : x i = false) : ¬ BState x i := by
  have f0 : First (Fwd x i) 0 := ⟨by simpa [Fwd] using h, fun r hr => absurd hr (by omega)⟩
  rintro (⟨t, ht, hodd⟩ | ⟨hn, _⟩ | ⟨hall, _⟩)
  · rw [← f0.unique ht] at hodd; exact absurd hodd (by decide)
  · exact hn ⟨0, by simpa using h⟩
  · rw [hall i] at h; exact Bool.noConfusion h

theorem bstate_after_zero {x : Config} (hx : EvenShift x) {i : Int} (h : x i = false) :
    ¬ BState x (i + 1) := by
  have b0 : First (Bwd x (i + 1)) 0 :=
    ⟨by simp [Bwd]; simpa using h, fun r hr => absurd hr (by omega)⟩
  rintro (⟨t, ⟨hz, hones⟩, hodd⟩ | ⟨_, t, ht, hodd⟩ | ⟨hall, _⟩)
  · apply hx i (t / 2)
    refine ⟨h, ?_, ?_⟩
    · intro r hr
      have := hones r (by omega)
      simpa [Fwd] using this
    · have e : i + (2 * ((t / 2 : Nat) : Int) + 2) = i + 1 + (t : Int) := by omega
      rw [e]; simpa [Fwd] using hz
  · rw [← b0.unique ht] at hodd; exact absurd hodd (by decide)
  · rw [hall i] at h; exact Bool.noConfusion h

theorem bstate_step {x : Config} {i : Int} (h : x i = true) :
    (BState x (i + 1) ↔ ¬ BState x i) := by
  by_cases hF : ∃ t : Nat, x (i + 1 + t) = false
  · obtain ⟨t0, ht0⟩ := hF
    obtain ⟨t, hz, hones⟩ := First.exists (f := Fwd x (i + 1)) t0 (by simpa [Fwd] using ht0)
    have hz' : x (i + 1 + t) = false := by simpa [Fwd] using hz
    have fi : First (Fwd x i) (t + 1) := by
      refine ⟨?_, ?_⟩
      · have e : i + ((t + 1 : Nat) : Int) = i + 1 + t := by omega
        simp only [Fwd]; rw [e]; exact hz'
      · intro r hr
        cases r with
        | zero => simpa [Fwd] using h
        | succ r =>
          have e : i + ((r + 1 : Nat) : Int) = i + 1 + r := by omega
          simp only [Fwd]; rw [e]
          have := hones r (by omega); simpa [Fwd] using this
    have fi1 : First (Fwd x (i + 1)) t := ⟨hz, hones⟩
    have nall : ¬ ∀ j, x j = true := fun hall => by rw [hall] at hz'; exact Bool.noConfusion hz'
    have c1 : BState x (i + 1) ↔ t % 2 = 1 := by
      constructor
      · rintro (⟨t', ht', hodd⟩ | ⟨hn, _⟩ | ⟨hall, _⟩)
        · rw [fi1.unique ht']; exact hodd
        · exact absurd ⟨t, hz'⟩ hn
        · exact absurd hall nall
      · intro hodd; exact Or.inl ⟨t, fi1, hodd⟩
    have c0 : BState x i ↔ (t + 1) % 2 = 1 := by
      constructor
      · rintro (⟨t', ht', hodd⟩ | ⟨hn, _⟩ | ⟨hall, _⟩)
        · rw [fi.unique ht']; exact hodd
        · exact absurd ⟨t + 1, by simpa [Fwd] using fi.1⟩ hn
        · exact absurd hall nall
      · intro hodd; exact Or.inl ⟨t + 1, fi, hodd⟩
    rw [c1, c0]; omega
  · have hF0 : ¬ ∃ t : Nat, x (i + t) = false := by
      rintro ⟨t, ht⟩
      cases t with
      | zero => simp at ht; rw [h] at ht; exact Bool.noConfusion ht
      | succ t =>
        apply hF; refine ⟨t, ?_⟩
        have e : i + ((t + 1 : Nat) : Int) = i + 1 + t := by omega
        rw [e] at ht; exact ht
    have hF1 : ¬ ∃ t : Nat, x (i + 1 + t) = false := hF
    have nf0 : ¬ ∃ t, First (Fwd x i) t ∧ t % 2 = 1 :=
      fun ⟨t, ht, _⟩ => hF0 ⟨t, by simpa [Fwd] using ht.1⟩
    have nf1 : ¬ ∃ t, First (Fwd x (i + 1)) t ∧ t % 2 = 1 :=
      fun ⟨t, ht, _⟩ => hF1 ⟨t, by simpa [Fwd] using ht.1⟩
    by_cases hB : ∃ t : Nat, x (i - 1 - t) = false
    · obtain ⟨t0, ht0⟩ := hB
      obtain ⟨t, hz, hones⟩ := First.exists (f := Bwd x i) t0 (by simpa [Bwd] using ht0)
      have hz' : x (i - 1 - t) = false := by simpa [Bwd] using hz
      have bi : First (Bwd x i) t := ⟨hz, hones⟩
      have bi1 : First (Bwd x (i + 1)) (t + 1) := by
        refine ⟨?_, ?_⟩
        · have e : i + 1 - 1 - ((t + 1 : Nat) : Int) = i - 1 - t := by omega
          simp only [Bwd]; rw [e]; exact hz'
        · intro r hr
          cases r with
          | zero => simp only [Bwd]; have e : i + 1 - 1 - ((0 : Nat) : Int) = i := by omega
                    rw [e]; exact h
          | succ r =>
            have e : i + 1 - 1 - ((r + 1 : Nat) : Int) = i - 1 - r := by omega
            simp only [Bwd]; rw [e]
            have := hones r (by omega); simpa [Bwd] using this
      have nall : ¬ ∀ j, x j = true := fun hall => by rw [hall] at hz'; exact Bool.noConfusion hz'
      have c0 : BState x i ↔ t % 2 = 1 := by
        constructor
        · rintro (hf | ⟨_, t', ht', hodd⟩ | ⟨hall, _⟩)
          · exact absurd hf nf0
          · rw [bi.unique ht']; exact hodd
          · exact absurd hall nall
        · intro hodd; exact Or.inr (Or.inl ⟨hF0, t, bi, hodd⟩)
      have c1 : BState x (i + 1) ↔ (t + 1) % 2 = 1 := by
        constructor
        · rintro (hf | ⟨_, t', ht', hodd⟩ | ⟨hall, _⟩)
          · exact absurd hf nf1
          · rw [bi1.unique ht']; exact hodd
          · exact absurd hall nall
        · intro hodd; exact Or.inr (Or.inl ⟨hF1, t + 1, bi1, hodd⟩)
      rw [c1, c0]; omega
    · have hall : ∀ j, x j = true := by
        intro j
        cases hxj : x j with
        | true => rfl
        | false =>
          exfalso
          rcases Int.lt_trichotomy j i with hl | he | hg
          · apply hB; refine ⟨(i - 1 - j).toNat, ?_⟩
            have e : i - 1 - (((i - 1 - j).toNat : Nat) : Int) = j := by omega
            rw [e]; exact hxj
          · rw [he, h] at hxj; exact Bool.noConfusion hxj
          · apply hF; refine ⟨(j - i - 1).toNat, ?_⟩
            have e : i + 1 + (((j - i - 1).toNat : Nat) : Int) = j := by omega
            rw [e]; exact hxj
      have nb : ∀ i', ¬ ∃ t, First (Bwd x i') t ∧ t % 2 = 1 := fun i' ⟨t, ht, _⟩ => by
        have := ht.1; simp only [Bwd] at this; rw [hall] at this; exact Bool.noConfusion this
      have c0 : BState x i ↔ i % 2 = 1 := by
        constructor
        · rintro (hf | ⟨_, hb⟩ | ⟨_, hp⟩)
          · exact absurd hf nf0
          · exact absurd hb (nb i)
          · exact hp
        · intro hp; exact Or.inr (Or.inr ⟨hall, hp⟩)
      have c1 : BState x (i + 1) ↔ (i + 1) % 2 = 1 := by
        constructor
        · rintro (hf | ⟨_, hb⟩ | ⟨_, hp⟩)
          · exact absurd hf nf1
          · exact absurd hb (nb (i + 1))
          · exact hp
        · intro hp; exact Or.inr (Or.inr ⟨hall, hp⟩)
      rw [c1, c0]; omega

/-- Every point of the even shift is the label of a bi-infinite path in the
Fischer graph. -/
theorem fisher_complete (x : Config) (hx : EvenShift x) : IsPathLabel fisher x := by
  refine ⟨pathOf x, fun i => ?_⟩
  rw [fisher_edge]
  unfold pathOf
  cases hxi : x i with
  | false =>
    left
    rw [if_neg (bstate_of_zero hxi), if_neg (bstate_after_zero hx hxi)]
    exact ⟨rfl, rfl, rfl⟩
  | true =>
    have hs := bstate_step hxi
    by_cases hb : BState x i
    · right; right
      rw [if_pos hb, if_neg (fun h' => (hs.1 h') hb)]
      exact ⟨rfl, rfl, rfl⟩
    · right; left
      rw [if_neg hb, if_pos (hs.2 hb)]
      exact ⟨rfl, rfl, rfl⟩

/-- The Fischer graph presents the even shift. -/
theorem fisher_presents : Presents fisher EvenShift :=
  fun x => ⟨fisher_complete x, fisher_sound x⟩

theorem evenShift_sofic : Sofic EvenShift := ⟨2, fisher, fisher_presents⟩

/-! ## No presentation with fewer than 2 states -/

theorem allZero_mem : EvenShift (fun _ => false) := fun _ _ ⟨_, h1, _⟩ => by
  have := h1 0 (by omega); exact Bool.noConfusion this

theorem allOne_mem : EvenShift (fun _ => true) := fun _ _ ⟨h0, _, _⟩ => Bool.noConfusion h0

/-- `… 0 0 1 0 0 …` (a single 1) is not in the even shift. -/
theorem single_one_not_mem : ¬ EvenShift (fun j => decide (j = 0)) := by
  intro h
  apply h (-1) 0
  refine ⟨by decide, ?_, by decide⟩
  intro t ht
  have : t = 0 := by omega
  subst this; decide

theorem no_zero_state (E : LGraph 0) : ¬ Presents E EvenShift := by
  intro h
  obtain ⟨s, _⟩ := (h _).1 allZero_mem
  exact absurd (s 0).isLt (by omega)

/-- A one-vertex graph presents the full shift on its loop labels `T`, and no
`T ⊆ {0,1}` gives the even shift. -/
theorem no_one_state (E : LGraph 1) : ¬ Presents E EvenShift := by
  intro h
  have z : ∀ a : Fin 1, a = 0 := fun a => Fin.ext (by have := a.isLt; simp)
  have l0 : E 0 false 0 = true := by
    obtain ⟨s, hs⟩ := (h _).1 allZero_mem
    have := hs 0; rw [z (s 0), z (s (0 + 1))] at this; exact this
  have l1 : E 0 true 0 = true := by
    obtain ⟨s, hs⟩ := (h _).1 allOne_mem
    have := hs 0; rw [z (s 0), z (s (0 + 1))] at this; exact this
  apply single_one_not_mem
  apply (h _).2
  refine ⟨fun _ => 0, fun i => ?_⟩
  show E 0 (decide (i = 0)) 0 = true
  cases decide (i = 0) <;> assumption

theorem lt_two_cases {n : Nat} (h : n < 2) : n = 0 ∨ n = 1 := by omega

/-- **Fischer count of the even shift is 2.** -/
theorem fisher_count : IsFisherCount EvenShift 2 := by
  refine ⟨⟨fisher, fisher_rightResolving, fisher_presents⟩, fun n hn => ?_⟩
  rcases lt_two_cases hn with rfl | rfl
  · rintro ⟨E, _, hE⟩; exact no_zero_state E hE
  · rintro ⟨E, _, hE⟩; exact no_one_state E hE

/-- Even among arbitrary presentations, the least number of states is 2. -/
theorem min_presentation_count : IsMinPresCount EvenShift 2 := by
  refine ⟨⟨fisher, fisher_presents⟩, fun n hn => ?_⟩
  rcases lt_two_cases hn with rfl | rfl
  · rintro ⟨E, hE⟩; exact no_zero_state E hE
  · rintro ⟨E, hE⟩; exact no_one_state E hE

/-! ## The Hankel matrix has rank at least 3 -/

/-- Rows `11, 0, 01`. -/
def rows3 : List (List Bool) := [[true, true], [false], [false, true]]
/-- Columns `0, 10, 1`. -/
def cols3 : List (List Bool) := [[false], [true, false], [true]]

/-- The 3×3 minor of the Hankel matrix of `L(X)`, computed from the language. -/
theorem minor_eq : minor EvenShift rows3 cols3 = [[1, 1, 1], [1, 0, 1], [0, 1, 1]] := by
  simp only [minor, rows3, cols3, List.map, hankelEntry_eq]
  decide

theorem minor_det : det (minor EvenShift rows3 cols3) = -1 := by
  rw [minor_eq]; decide

/-- Plain matrix product of list matrices (for the inverse certificate). -/
def matMul (A B : List (List Int)) : List (List Int) :=
  A.map (fun r => (List.range (B.headD []).length).map (fun j =>
    ((List.range r.length).map (fun k => r.getD k 0 * (B.getD k []).getD j 0)).foldr (· + ·) 0))

/-- The minor is invertible over `ℤ`, hence over every commutative ring. -/
theorem minor_unimodular :
    matMul (minor EvenShift rows3 cols3) [[1, 0, -1], [1, -1, 0], [-1, 1, 1]] =
      [[1, 0, 0], [0, 1, 0], [0, 0, 1]] ∧
    matMul [[1, 0, -1], [1, -1, 0], [-1, 1, 1]] (minor EvenShift rows3 cols3) =
      [[1, 0, 0], [0, 1, 0], [0, 0, 1]] := by
  rw [minor_eq]; decide

/-- The three rows `11, 0, 01` of the Hankel matrix are linearly independent
over `ℚ` (integer coefficients suffice after clearing denominators). -/
theorem rows_independent (a b c : Int)
    (h : ∀ v ∈ cols3, a * hankelEntry EvenShift [true, true] v +
      b * hankelEntry EvenShift [false] v + c * hankelEntry EvenShift [false, true] v = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have h1 := h [false] (by decide)
  have h2 := h [true, false] (by decide)
  have h3 := h [true] (by decide)
  simp only [hankelEntry_eq] at h1 h2 h3
  have e1 : WordOK ([true, true] ++ [false]) := by decide
  have e2 : WordOK ([false] ++ [false]) := by decide
  have e3 : ¬ WordOK ([false, true] ++ [false]) := by decide
  have e4 : WordOK ([true, true] ++ [true, false]) := by decide
  have e5 : ¬ WordOK ([false] ++ [true, false]) := by decide
  have e6 : WordOK ([false, true] ++ [true, false]) := by decide
  have e7 : WordOK ([true, true] ++ [true]) := by decide
  have e8 : WordOK ([false] ++ [true]) := by decide
  have e9 : WordOK ([false, true] ++ [true]) := by decide
  simp only [e1, e2, e3, e4, e5, e6, e7, e8, e9, if_true, if_false] at h1 h2 h3
  omega

theorem hankel_rank_ge_three : HankelRankAtLeast EvenShift 3 :=
  ⟨rows3, cols3, rfl, rfl, by rw [minor_det]; decide⟩

theorem not_dvd_neg_one (p : Nat) (hp : 2 ≤ p) : ¬ ((p : Int) ∣ -1) := by
  intro h
  have := Int.natAbs_dvd_natAbs.mpr h
  simp at this
  omega

/-- Rank at least 3 over `ℤ/p` for every `p ≥ 2`, in particular over every
prime field `𝔽_p`. -/
theorem hankel_rank_ge_three_mod (p : Nat) (hp : 2 ≤ p) : HankelRankAtLeastMod p EvenShift 3 :=
  ⟨rows3, cols3, rfl, rfl, by rw [minor_det]; exact not_dvd_neg_one p hp⟩

/-! ## Refutation -/

/-- For the even shift, the Fischer count is 2 and the Hankel rank exceeds it. -/
theorem evenShift_counterexample :
    Sofic EvenShift ∧ IsFisherCount EvenShift 2 ∧ IsMinPresCount EvenShift 2 ∧
    HankelRankAtLeast EvenShift 3 ∧ (∀ p, 2 ≤ p → HankelRankAtLeastMod p EvenShift 3) :=
  ⟨evenShift_sofic, fisher_count, min_presentation_count, hankel_rank_ge_three,
    hankel_rank_ge_three_mod⟩

/-- Whatever number `m` is the Fischer count of the even shift, it is 2 and the
Hankel rank is at least `m + 1`. -/
theorem fisher_lt_rank (m : Nat) (h : IsFisherCount EvenShift m) :
    m = 2 ∧ HankelRankAtLeast EvenShift (m + 1) := by
  have := h.unique fisher_count
  subst this
  exact ⟨rfl, hankel_rank_ge_three⟩

/-- **The clause is false** (rank over `ℚ`). -/
theorem conjecture_00000009617_false : ¬ Claim := by
  intro h
  exact (h EvenShift evenShift_sofic 2 fisher_count).2 hankel_rank_ge_three

/-- The clause is false with the rank over `ℤ/p`, for every `p ≥ 2`
(so over every prime field, hence over every field). -/
theorem conjecture_00000009617_false_mod (p : Nat) (hp : 2 ≤ p) : ¬ ClaimMod p := by
  intro h
  exact (h EvenShift evenShift_sofic 2 fisher_count).2 (hankel_rank_ge_three_mod p hp)

/-- The clause is false also when "Fisher count" means the least number of
states of an arbitrary presentation. -/
theorem conjecture_00000009617_false_any_presentation : ¬ ClaimAnyPresentation := by
  intro h
  exact (h EvenShift evenShift_sofic 2 min_presentation_count).2 hankel_rank_ge_three

/-! ## Sanity checks (non-vacuity) -/

/-- The language is not trivial: it contains `0110` and `111` but not `010`. -/
example : Lang EvenShift [false, true, true, false] ∧ Lang EvenShift [true, true, true] ∧
    ¬ Lang EvenShift [false, true, false] := by decide

/-- The determinant routine is not degenerate: it gives `0` on a singular matrix
and `1` on the identity. -/
example : det [[1, 1, 0], [1, 1, 0], [0, 0, 1]] = 0 ∧ det [[1, 0, 0], [0, 1, 0], [0, 0, 1]] = 1 := by
  decide

end EvenShiftHankel

#print axioms EvenShiftHankel.lang_iff
#print axioms EvenShiftHankel.fisher_presents
#print axioms EvenShiftHankel.fisher_count
#print axioms EvenShiftHankel.min_presentation_count
#print axioms EvenShiftHankel.minor_det
#print axioms EvenShiftHankel.minor_unimodular
#print axioms EvenShiftHankel.rows_independent
#print axioms EvenShiftHankel.evenShift_counterexample
#print axioms EvenShiftHankel.fisher_lt_rank
#print axioms EvenShiftHankel.conjecture_00000009617_false
#print axioms EvenShiftHankel.conjecture_00000009617_false_mod
#print axioms EvenShiftHankel.conjecture_00000009617_false_any_presentation
