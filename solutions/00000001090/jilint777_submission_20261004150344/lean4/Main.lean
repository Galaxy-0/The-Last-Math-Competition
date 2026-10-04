/-!
# Conjecture 00000001090: there is no ternary MDS code of type [12,6]

The conjecture claims that the maximal order of the automorphism group of an MDS code
over GF(3) of type `[12,6]` is 660 (attained by an `M₁₁` embedding), and that the orders
for all other equivalence classes divide 132.

An MDS `[12,6]` code has minimum distance `12 - 6 + 1 = 7`. We prove (`no_mds_ternary`)
that for `k ≥ 2` and `n ≥ k + 3` no `k × n` matrix over `F₃` has all nonzero
combinations of its rows of weight `≥ n - k + 1`. Hence no ternary MDS `[12,6]` code
exists (`no_mds_12_6`), nothing attains the order 660, and the conjecture is false
(`conjecture_00000001090_false`, `conjecture_00000001090_monomial_false`), whatever
the notion of automorphism group (`no_mds_12_6_with`).

Proof of `no_mds_ternary`: by linear dependence (`dep`) there are two independent
messages whose codewords `u, v` vanish on the first `k - 2` coordinates.  The eight
nonzero combinations `a u + b v` are nonzero codewords, so their weights sum to at least
`8 (n - k + 1)`.  Each of the remaining `n - k + 2` coordinates is nonzero in exactly 0
or 6 of them (`cnt_le`), so the sum is at most `6 (n - k + 2)`.  This forces `n ≤ k + 2`.

Other readings (all refuted below):
* "[12,6]" read as length 12 and distance 6: no MDS `[12,7,6]` code (`no_mds_12_7`).
* "MDS" read as the ternary Golay code `[12,6,6]` (the intended object, probably): the
  definition uses the stabiliser of the *permutation* equivalence class, i.e. `PAut`.
  The code `golay'` (column 6 of `golay` doubled) is a `[12,6,6]` code
  (`golay'_12_6_6`) with at least 720 > 660 distinct permutation automorphisms
  (`golay_reading_witness`, `golay_reading_false`, `golay'_order_ge`).  In fact
  `PAut(golay') ≅ M₁₁` has order 7920, and `golay` itself has `|PAut| = 660`
  (exact orders in `verify.py`).
* "MDS" dropped (all `[12,6]` codes): the repeated-pair code has at least 768
  permutation automorphisms (`atMost660_false`, `pair_order_ge`).

Codes are given by generator matrices `G : Nat → Nat → F3` (row `i < k`, column `j < n`).
Arithmetic in `F₃ = Fin 3` is checked by `decide`.
-/

namespace TernaryMDS

abbrev F3 := Fin 3

def sumTo (n : Nat) (f : Nat → Nat) : Nat :=
  match n with
  | 0 => 0
  | n + 1 => sumTo n f + f n

theorem sumTo_succ (n : Nat) (f : Nat → Nat) : sumTo (n + 1) f = sumTo n f + f n := rfl

def comb : Nat → (Nat → F3) → (Nat → Nat → F3) → Nat → F3
  | 0, _, _, _ => 0
  | k + 1, c, G, j => comb k c G j + c k * G k j

def ind (x : F3) : Nat := if x = 0 then 0 else 1

def wt (n : Nat) (w : Nat → F3) : Nat := sumTo n (fun j => ind (w j))

theorem comb_congr_coef (k : Nat) (c c' : Nat → F3) (G : Nat → Nat → F3) (j : Nat)
    (h : ∀ i, i < k → c i = c' i) : comb k c G j = comb k c' G j := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [comb]
    rw [ih (fun i hi => h i (by omega)), h k (by omega)]

theorem comb_congr_vec (k : Nat) (c : Nat → F3) (G G' : Nat → Nat → F3) (j j' : Nat)
    (h : ∀ i, i < k → G i j = G' i j') : comb k c G j = comb k c G' j' := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [comb]
    rw [ih (fun i hi => h i (by omega)), h k (by omega)]

theorem comb_zero_coef (k : Nat) (c : Nat → F3) (G : Nat → Nat → F3) (j : Nat)
    (h : ∀ i, i < k → c i = 0) : comb k c G j = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [comb]
    rw [ih (fun i hi => h i (by omega)), h k (by omega)]
    generalize G k j = x
    revert x; decide

theorem comb_zero_vec (k : Nat) (c : Nat → F3) (G : Nat → Nat → F3) (j : Nat)
    (h : ∀ i, i < k → G i j = 0) : comb k c G j = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [comb]
    rw [ih (fun i hi => h i (by omega)), h k (by omega)]
    generalize c k = x
    revert x; decide

theorem comb_ind (k : Nat) (c : Nat → F3) (t j : Nat) (ht : t < k) :
    comb k c (fun i _ => if i = t then 1 else 0) j = c t := by
  induction k with
  | zero => omega
  | succ k ih =>
    simp only [comb]
    by_cases htk : t = k
    · subst htk
      rw [comb_zero_vec t c _ j (fun i hi => by simp [show i ≠ t by omega])]
      simp only [if_pos rfl]
      generalize c t = x
      revert x; decide
    · rw [ih (by omega)]
      simp only [show k ≠ t by omega, if_false]
      generalize c t = x
      generalize c k = y
      revert x y; decide

theorem comb_lin (k : Nat) (a b : F3) (c1 c2 : Nat → F3) (G : Nat → Nat → F3) (j : Nat) :
    comb k (fun i => a * c1 i + b * c2 i) G j = a * comb k c1 G j + b * comb k c2 G j := by
  induction k with
  | zero => simp only [comb]; revert a b; decide
  | succ k ih =>
    simp only [comb]
    rw [ih]
    clear ih
    generalize comb k c1 G j = X
    generalize comb k c2 G j = Y
    generalize c1 k = x
    generalize c2 k = y
    generalize G k j = g
    revert a b X Y x y g; decide

/-- Row operation: subtract from every vector `v i` the multiple `(v i j0 * v piv j0)` of
the pivot vector `v piv`.  When `v piv j0 ≠ 0`, the result vanishes at coordinate `j0`. -/
def elimV (v : Nat → Nat → F3) (j0 piv : Nat) : Nat → Nat → F3 :=
  fun i j => v i j - (v i j0 * v piv j0) * v piv j

theorem comb_elimV (k : Nat) (c : Nat → F3) (v : Nat → Nat → F3) (j0 piv j : Nat) :
    comb k c (elimV v j0 piv) j
      = comb k c v j - comb k c (fun i _ => v i j0 * v piv j0) 0 * v piv j := by
  induction k with
  | zero => simp only [comb]; generalize v piv j = x; revert x; decide
  | succ k ih =>
    simp only [comb]
    rw [ih]
    simp only [elimV]
    generalize comb k c v j = X
    generalize comb k c (fun i _ => v i j0 * v piv j0) 0 = B
    generalize v piv j = w
    generalize v k j0 * v piv j0 = s
    generalize v k j = x
    generalize c k = ck
    revert X B w s x ck; decide

/-- Delete coordinate `j0` (shift the later coordinates down by one). -/
def skipCoord (v : Nat → Nat → F3) (j0 : Nat) : Nat → Nat → F3 :=
  fun i j => v i (if j < j0 then j else j + 1)

def Nonzero (k : Nat) (m : Nat → F3) : Prop := ∃ i, i < k ∧ m i ≠ 0

/-- Linear dependence: `k > r` vectors of `F₃^r` have a nontrivial vanishing combination. -/
theorem dep (r : Nat) : ∀ (k : Nat) (v : Nat → Nat → F3), r < k →
    ∃ c : Nat → F3, Nonzero k c ∧ ∀ j, j < r → comb k c v j = 0 := by
  induction r with
  | zero =>
    intro k v hk
    exact ⟨fun i => if i = 0 then 1 else 0, ⟨0, hk, by decide⟩, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ r ih =>
    intro k v hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    by_cases hex : ∃ j0, j0 < r + 1 ∧ v k' j0 ≠ 0
    · obtain ⟨j0, hj0, hp⟩ := hex
      obtain ⟨c', ⟨i1, hi1, hc'⟩, hc'0⟩ := ih k' (skipCoord (elimV v j0 k') j0) (by omega)
      refine ⟨fun i => if i = k' then 0 - comb k' c' (fun i _ => v i j0 * v k' j0) 0 else c' i, ⟨i1, by omega, ?_⟩, ?_⟩
      · simp only [show i1 ≠ k' by omega, if_false]; exact hc'
      · intro j hj
        simp only [comb]
        rw [comb_congr_coef k' _ c' v j (fun i hi => by simp [show i ≠ k' by omega])]
        have key : comb k' c' (elimV v j0 k') j = 0 := by
          by_cases hjj : j = j0
          · subst hjj
            apply comb_zero_vec
            intro i _
            simp only [elimV]
            generalize v i j = x
            generalize v k' j = y at hp
            revert x y; decide
          · by_cases hlt : j < j0
            · rw [comb_congr_vec k' c' _ (skipCoord (elimV v j0 k') j0) j j
                (fun i _ => by simp [skipCoord, hlt])]
              exact hc'0 j (by omega)
            · rw [comb_congr_vec k' c' _ (skipCoord (elimV v j0 k') j0) j (j - 1)
                (fun i _ => by simp [skipCoord, show ¬ (j - 1 < j0) by omega,
                  show j - 1 + 1 = j by omega])]
              exact hc'0 (j - 1) (by omega)
        rw [comb_elimV] at key
        rw [if_pos trivial]
        generalize comb k' c' (fun i _ => v i j0 * v k' j0) 0 = b at key ⊢
        generalize comb k' c' v j = X at key ⊢
        generalize v k' j = y at key ⊢
        revert X y b; decide
    · refine ⟨fun i => if i = k' then 1 else 0, ⟨k', by omega, by simp⟩, ?_⟩
      intro j hj
      have hz : v k' j = 0 :=
        Decidable.byContradiction (fun hne => hex ⟨j, hj, hne⟩)
      simp only [comb]
      rw [comb_zero_coef k' _ v j (fun i hi => by simp [show i ≠ k' by omega]), hz]
      decide


/-! ## Codes, weights, minimum distance, MDS -/

/-- The codeword with message `m` for the generator matrix `G` (rows `i < k`). -/
def codeword (k : Nat) (G : Nat → Nat → F3) (m : Nat → F3) : Nat → F3 :=
  fun j => comb k m G j

/-- `G` (rows `0..k-1`, columns `0..n-1`) has linearly independent rows, i.e. it
generates a ternary linear code of length `n` and dimension `k`. -/
def IsGenMatrix (n k : Nat) (G : Nat → Nat → F3) : Prop :=
  ∀ m, Nonzero k m → ∃ j, j < n ∧ codeword k G m j ≠ 0

/-- Membership of a word of length `n` in the code generated by `G`. -/
def InCode (n k : Nat) (G : Nat → Nat → F3) (w : Nat → F3) : Prop :=
  ∃ m, ∀ j, j < n → w j = codeword k G m j

/-- Every nonzero codeword has Hamming weight at least `d`. -/
def MinDistGe (n k : Nat) (G : Nat → Nat → F3) (d : Nat) : Prop :=
  ∀ m, Nonzero k m → d ≤ wt n (codeword k G m)

/-- The minimum distance is exactly `d`. -/
def HasMinDist (n k : Nat) (G : Nat → Nat → F3) (d : Nat) : Prop :=
  MinDistGe n k G d ∧ ∃ m, Nonzero k m ∧ wt n (codeword k G m) = d

/-- `G` generates a ternary `[n, k, n - k + 1]` (maximum distance separable) code. -/
def IsMDS (n k : Nat) (G : Nat → Nat → F3) : Prop :=
  IsGenMatrix n k G ∧ HasMinDist n k G (n - k + 1)

/-! ## The counting lemma for two-dimensional subcodes -/

/-- For one coordinate with entries `x` (of `u`) and `y` (of `v`): the number of the eight
nonzero pairs `(a, b)` with `a x + b y ≠ 0`. -/
def cnt (x y : F3) : Nat :=
  ind (1 * x + 0 * y) + ind (2 * x + 0 * y) + ind (0 * x + 1 * y) + ind (0 * x + 2 * y) +
  ind (1 * x + 1 * y) + ind (1 * x + 2 * y) + ind (2 * x + 1 * y) + ind (2 * x + 2 * y)

theorem cnt_le : ∀ x y : F3, cnt x y ≤ 6 := by decide

theorem cnt_zero : cnt 0 0 = 0 := by decide

/-- Sum of the weights of the eight nonzero combinations `a u + b v`. -/
def pairWt (n : Nat) (u v : Nat → F3) : Nat :=
  wt n (fun j => 1 * u j + 0 * v j) + wt n (fun j => 2 * u j + 0 * v j) +
  wt n (fun j => 0 * u j + 1 * v j) + wt n (fun j => 0 * u j + 2 * v j) +
  wt n (fun j => 1 * u j + 1 * v j) + wt n (fun j => 1 * u j + 2 * v j) +
  wt n (fun j => 2 * u j + 1 * v j) + wt n (fun j => 2 * u j + 2 * v j)

theorem pairWt_eq (n : Nat) (u v : Nat → F3) :
    pairWt n u v = sumTo n (fun j => cnt (u j) (v j)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold pairWt wt at ih ⊢
    simp only [sumTo_succ, cnt] at ih ⊢
    omega

theorem sumTo_bound (n r : Nat) (g : Nat → Nat) (h6 : ∀ j, g j ≤ 6)
    (h0 : ∀ j, j < r → g j = 0) : sumTo n g ≤ 6 * (n - r) := by
  induction n with
  | zero => simp [sumTo]
  | succ n ih =>
    simp only [sumTo]
    have := h6 n
    by_cases hn : n < r
    · have := h0 n hn; omega
    · omega

/-! ## Main theorem: ternary MDS codes satisfy `n ≤ k + 2` (for `k ≥ 2`) -/

/-- Extra coordinate trick: coordinates `< r` are those of `G`, coordinate `r` is the
indicator of row `i0`. -/
def augment (G : Nat → Nat → F3) (r i0 : Nat) : Nat → Nat → F3 :=
  fun i j => if j < r then G i j else if i = i0 then 1 else 0

theorem nonzero_left : ∀ a x b : F3, a ≠ 0 → x ≠ 0 → a * x + b * 0 ≠ 0 := by decide
theorem nonzero_right : ∀ x b y : F3, b ≠ 0 → y ≠ 0 → 0 * x + b * y ≠ 0 := by decide

/-- **No ternary `[n, k, n-k+1]` code with `k ≥ 2` and `n ≥ k + 3` exists**: in fact no
`k × n` matrix over `F₃` has all nonzero combinations of its rows of weight `≥ n - k + 1`. -/
theorem no_mds_ternary (n k : Nat) (hk : 2 ≤ k) (hn : k + 3 ≤ n) (G : Nat → Nat → F3) :
    ¬ MinDistGe n k G (n - k + 1) := by
  intro hmd
  -- a nonzero message whose codeword vanishes on the first `k - 2` coordinates
  obtain ⟨m1, ⟨i0, hi0, hm1⟩, h1⟩ := dep (k - 2) k G (by omega)
  -- a second one, which in addition has coordinate `0` at row `i0`
  obtain ⟨m2, ⟨i2, hi2, hm2⟩, h2⟩ := dep (k - 1) k (augment G (k - 2) i0) (by omega)
  have h2a : ∀ j, j < k - 2 → comb k m2 G j = 0 := by
    intro j hj
    rw [comb_congr_vec k m2 G (augment G (k - 2) i0) j j (fun i _ => by simp [augment, hj])]
    exact h2 j (by omega)
  have h2b : m2 i0 = 0 := by
    have := h2 (k - 2) (by omega)
    rw [comb_congr_vec k m2 (augment G (k - 2) i0) (fun i _ => if i = i0 then 1 else 0)
      (k - 2) (k - 2) (fun i _ => by simp [augment])] at this
    rwa [comb_ind k m2 i0 _ hi0] at this
  -- every nonzero combination a u + b v is a nonzero codeword
  have hpair : ∀ a b : F3, (a ≠ 0 ∨ b ≠ 0) →
      n - k + 1 ≤ wt n (fun j => a * comb k m1 G j + b * comb k m2 G j) := by
    intro a b hab
    have hnz : Nonzero k (fun i => a * m1 i + b * m2 i) := by
      by_cases ha : a = 0
      · have hb : b ≠ 0 := by
          cases hab with
          | inl h => exact absurd ha h
          | inr h => exact h
        subst ha
        exact ⟨i2, hi2, nonzero_right _ _ _ hb hm2⟩
      · exact ⟨i0, hi0, by show a * m1 i0 + b * m2 i0 ≠ 0; rw [h2b]; exact nonzero_left _ _ _ ha hm1⟩
    have := hmd _ hnz
    have e : codeword k G (fun i => a * m1 i + b * m2 i)
        = fun j => a * comb k m1 G j + b * comb k m2 G j :=
      funext (fun j => comb_lin k a b m1 m2 G j)
    rwa [e] at this
  have t1 := hpair 1 0 (by decide)
  have t2 := hpair 2 0 (by decide)
  have t3 := hpair 0 1 (by decide)
  have t4 := hpair 0 2 (by decide)
  have t5 := hpair 1 1 (by decide)
  have t6 := hpair 1 2 (by decide)
  have t7 := hpair 2 1 (by decide)
  have t8 := hpair 2 2 (by decide)
  have hsum := pairWt_eq n (fun j => comb k m1 G j) (fun j => comb k m2 G j)
  have hb := sumTo_bound n (k - 2) (fun j => cnt (comb k m1 G j) (comb k m2 G j))
    (fun j => cnt_le _ _) (fun j hj => by simp only [h1 j hj, h2a j hj, cnt_zero])
  simp only [pairWt] at hsum
  omega


/-! ## Automorphism groups -/

/-- `j`-th entry of a list (0 if out of range); structural, so the kernel evaluates it fast. -/
def nth : List Nat → Nat → Nat
  | [], _ => 0
  | a :: _, 0 => a
  | _ :: l, n + 1 => nth l n

theorem nth_mem : ∀ (l : List Nat) (j : Nat), j < l.length → nth l j ∈ l := by
  intro l
  induction l with
  | nil => intro j h; exact absurd h (Nat.not_lt_zero _)
  | cons a l ih =>
    intro j h
    cases j with
    | zero => exact List.mem_cons_self ..
    | succ j =>
      exact List.mem_cons_of_mem _ (ih j (by simp only [List.length_cons] at h; omega))

theorem nth_map (f : Nat → Nat) : ∀ (l : List Nat) (j : Nat), j < l.length →
    nth (l.map f) j = f (nth l j) := by
  intro l
  induction l with
  | nil => intro j h; exact absurd h (Nat.not_lt_zero _)
  | cons a l ih =>
    intro j h
    cases j with
    | zero => rfl
    | succ j => exact ih j (by simp only [List.length_cons] at h; omega)

/-- A coordinate permutation of `{0, …, n-1}` is stored as the list of images. -/
def applyL (σ : List Nat) (j : Nat) : Nat := nth σ j

def IsPermL (n : Nat) (σ : List Nat) : Prop := σ.length = n ∧ σ.Nodup ∧ ∀ x ∈ σ, x < n

instance (n : Nat) : DecidablePred (IsPermL n) := fun σ => by unfold IsPermL; infer_instance

/-- Permutation automorphism: the coordinate permutation `σ` maps every codeword `c` to a
codeword `j ↦ c (σ j)` (for a finite code this means `σ` stabilises the code). -/
def IsPAut (n k : Nat) (G : Nat → Nat → F3) (σ : List Nat) : Prop :=
  IsPermL n σ ∧ ∀ m, InCode n k G (fun j => codeword k G m (applyL σ j))

/-- Monomial automorphism: permutation `σ` followed by nonzero scalars `s`. -/
def IsMAut (n k : Nat) (G : Nat → Nat → F3) (σ : List Nat) (s : List F3) : Prop :=
  IsPermL n σ ∧ s.length = n ∧ (∀ x ∈ s, x ≠ 0) ∧
    ∀ m, InCode n k G (fun j => s.getD j 0 * codeword k G m (applyL σ j))

/-- The permutation automorphism group of the code generated by `G` has order `N`. -/
def PAutOrder (n k : Nat) (G : Nat → Nat → F3) (N : Nat) : Prop :=
  ∃ L : List (List Nat), L.Nodup ∧ L.length = N ∧ ∀ σ, σ ∈ L ↔ IsPAut n k G σ

/-- The monomial automorphism group of the code generated by `G` has order `N`. -/
def MAutOrder (n k : Nat) (G : Nat → Nat → F3) (N : Nat) : Prop :=
  ∃ L : List (List Nat × List F3), L.Nodup ∧ L.length = N ∧
    ∀ σ s, (σ, s) ∈ L ↔ IsMAut n k G σ s

/-! ## The conjecture and its refutation -/

/-- Conjecture 00000001090 (automorphism group = permutation automorphism group):
the maximal order is 660 and is attained; all other orders divide 132. -/
def Conjecture1090 : Prop :=
  (∃ G, IsMDS 12 6 G ∧ PAutOrder 12 6 G 660) ∧
  (∀ G N, IsMDS 12 6 G → PAutOrder 12 6 G N → N ≤ 660) ∧
  (∀ G N, IsMDS 12 6 G → PAutOrder 12 6 G N → N ≠ 660 → N ∣ 132)

/-- The same with the monomial automorphism group. -/
def Conjecture1090Mon : Prop :=
  (∃ G, IsMDS 12 6 G ∧ MAutOrder 12 6 G 660) ∧
  (∀ G N, IsMDS 12 6 G → MAutOrder 12 6 G N → N ≤ 660) ∧
  (∀ G N, IsMDS 12 6 G → MAutOrder 12 6 G N → N ≠ 660 → N ∣ 132)

/-- Even "minimum distance at least 7" is impossible for a ternary `[12,6]` code. -/
theorem no_dist7_12_6 (G : Nat → Nat → F3) : ¬ MinDistGe 12 6 G 7 :=
  no_mds_ternary 12 6 (by decide) (by decide) G

/-- There is no MDS ternary code of type `[12,6]`. -/
theorem no_mds_12_6 : ¬ ∃ G, IsMDS 12 6 G :=
  fun ⟨G, _, hmd, _⟩ => no_dist7_12_6 G hmd

/-- Hence no MDS `[12,6]` ternary code has *any* property `P` (e.g. any notion of
automorphism group of order 660, or containing `M₁₁`). -/
theorem no_mds_12_6_with (P : (Nat → Nat → F3) → Prop) : ¬ ∃ G, IsMDS 12 6 G ∧ P G :=
  fun ⟨G, h, _⟩ => no_mds_12_6 ⟨G, h⟩

/-- The attainment clause is false. -/
theorem attained_false : ¬ ∃ G, IsMDS 12 6 G ∧ PAutOrder 12 6 G 660 :=
  no_mds_12_6_with _

theorem conjecture_00000001090_false : ¬ Conjecture1090 :=
  fun h => attained_false h.1

theorem conjecture_00000001090_monomial_false : ¬ Conjecture1090Mon :=
  fun h => no_mds_12_6_with _ h.1

/-- Reading `[12,6]` as length 12 and minimum distance 6 (so `k = 7`): no such MDS code either. -/
theorem no_mds_12_7 : ¬ ∃ G, IsMDS 12 7 G :=
  fun ⟨G, _, hmd, _⟩ => no_mds_ternary 12 7 (by decide) (by decide) G hmd

/-! ## Non-vacuity: the notions are satisfiable -/

def getF : List F3 → Nat → F3
  | [], _ => 0
  | a :: _, 0 => a
  | _ :: l, n + 1 => getF l n

def getRow : List (List F3) → Nat → List F3
  | [], _ => []
  | a :: _, 0 => a
  | _ :: l, n + 1 => getRow l n

/-- The matrix with the given rows (entries outside are 0). -/
def matOf (rows : List (List F3)) : Nat → Nat → F3 := fun i j => getF (getRow rows i) j

def msgL (l : List F3) : Nat → F3 := fun i => l.getD i 0

/-- The tetracode, a ternary `[4,2,3]` MDS code: the bound `n ≤ k + 2` is sharp. -/
def tetra : Nat → Nat → F3 := matOf [[1, 0, 1, 1], [0, 1, 1, 2]]

theorem codeword2 (G : Nat → Nat → F3) (m : Nat → F3) :
    codeword 2 G m = codeword 2 G (msgL [m 0, m 1]) := by
  funext j
  apply comb_congr_coef
  intro i hi
  have : i = 0 ∨ i = 1 := by omega
  rcases this with rfl | rfl <;> rfl

theorem nonzero2 (m : Nat → F3) (h : Nonzero 2 m) : m 0 ≠ 0 ∨ m 1 ≠ 0 := by
  obtain ⟨i, hi, hm⟩ := h
  have : i = 0 ∨ i = 1 := by omega
  rcases this with rfl | rfl
  · exact Or.inl hm
  · exact Or.inr hm

theorem tetra_check : ∀ a b : F3, (a ≠ 0 ∨ b ≠ 0) →
    3 ≤ wt 4 (codeword 2 tetra (msgL [a, b])) := by decide

theorem tetra_mds : IsMDS 4 2 tetra := by
  refine ⟨?_, ?_, ⟨msgL [1, 0], ⟨0, by decide, by decide⟩, by decide⟩⟩
  · intro m hm
    have h3 := tetra_check (m 0) (m 1) (nonzero2 m hm)
    rw [← codeword2] at h3
    refine Decidable.byContradiction (fun hne => ?_)
    have hz : ∀ j, j < 4 → codeword 2 tetra m j = 0 := fun j hj =>
      Decidable.byContradiction (fun h => hne ⟨j, hj, h⟩)
    have : wt 4 (codeword 2 tetra m) = 0 := by
      simp only [wt, sumTo, ind, hz 0 (by decide), hz 1 (by decide), hz 2 (by decide),
        hz 3 (by decide)]
      decide
    omega
  · intro m hm
    have h3 := tetra_check (m 0) (m 1) (nonzero2 m hm)
    rwa [← codeword2] at h3


/-- The extended ternary Golay code `[12,6,6]`, generator matrix `[I₆ | A]`. -/
def golay : Nat → Nat → F3 := matOf
  [[1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1],
   [0, 1, 0, 0, 0, 0, 1, 0, 1, 2, 2, 1],
   [0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 2, 2],
   [0, 0, 0, 1, 0, 0, 1, 2, 1, 0, 1, 2],
   [0, 0, 0, 0, 1, 0, 1, 2, 2, 1, 0, 1],
   [0, 0, 0, 0, 0, 1, 1, 1, 2, 2, 1, 0]]

theorem codeword6 (G : Nat → Nat → F3) (m : Nat → F3) :
    codeword 6 G m = codeword 6 G (msgL [m 0, m 1, m 2, m 3, m 4, m 5]) := by
  funext j
  apply comb_congr_coef
  intro i hi
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem nonzero6 (m : Nat → F3) (h : Nonzero 6 m) :
    m 0 ≠ 0 ∨ m 1 ≠ 0 ∨ m 2 ≠ 0 ∨ m 3 ≠ 0 ∨ m 4 ≠ 0 ∨ m 5 ≠ 0 := by
  obtain ⟨i, hi, hm⟩ := h
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [hm]

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 1024 in
theorem golay_check : ∀ a b c d e f : F3,
    (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 ∨ d ≠ 0 ∨ e ≠ 0 ∨ f ≠ 0) →
    6 ≤ wt 12 (codeword 6 golay (msgL [a, b, c, d, e, f])) := by decide +kernel

/-- The ternary Golay code is a `[12,6]` code with minimum distance exactly 6: ternary
`[12,6]` codes exist, and it is precisely distance 7 (MDS) that is impossible. -/
theorem golay_12_6_6 : IsGenMatrix 12 6 golay ∧ HasMinDist 12 6 golay 6 := by
  have hge : MinDistGe 12 6 golay 6 := by
    intro m hm
    have h := golay_check _ _ _ _ _ _ (nonzero6 m hm)
    rwa [← codeword6] at h
  refine ⟨?_, hge, ⟨msgL [1, 0, 0, 0, 0, 0], ⟨0, by decide, by decide⟩, by decide⟩⟩
  intro m hm
  refine Decidable.byContradiction (fun hne => ?_)
  have hz : ∀ j, j < 12 → codeword 6 golay m j = 0 := fun j hj =>
    Decidable.byContradiction (fun h => hne ⟨j, hj, h⟩)
  have h0 : wt 12 (codeword 6 golay m) = 0 := by
    simp only [wt, sumTo, ind, hz 0 (by decide), hz 1 (by decide), hz 2 (by decide),
      hz 3 (by decide), hz 4 (by decide), hz 5 (by decide), hz 6 (by decide),
      hz 7 (by decide), hz 8 (by decide), hz 9 (by decide), hz 10 (by decide),
      hz 11 (by decide)]
    decide
  have := hge m hm
  omega


/-! ## Reading without "MDS": `[12,6]` ternary codes with more than 660 automorphisms -/

/-- The code of repeated pairs `(x₀,x₀,x₁,x₁,…,x₅,x₅)`, a ternary `[12,6,2]` code. -/
def pairG : Nat → Nat → F3 := fun i j => if i = j / 2 then 1 else 0

theorem codeword_pair (m : Nat → F3) (j : Nat) (hj : j < 12) :
    codeword 6 pairG m j = m (j / 2) := by
  unfold codeword
  rw [comb_congr_vec 6 m pairG (fun i _ => if i = j / 2 then 1 else 0) j j (fun i _ => rfl)]
  exact comb_ind 6 m (j / 2) j (by omega)

theorem pair_gen : IsGenMatrix 12 6 pairG := by
  intro m ⟨i, hi, hm⟩
  refine ⟨2 * i, by omega, ?_⟩
  rw [codeword_pair m (2 * i) (by omega), show 2 * i / 2 = i by omega]
  exact hm

/-- `σ` maps each coordinate pair `{2i, 2i+1}` onto a coordinate pair. -/
def PairResp (σ : List Nat) : Prop := ∀ i, i < 6 → applyL σ (2 * i) / 2 = applyL σ (2 * i + 1) / 2

instance : DecidablePred PairResp := fun σ => by unfold PairResp; infer_instance

theorem applyL_lt (σ : List Nat) (n j : Nat) (h : IsPermL n σ) (hj : j < n) : applyL σ j < n :=
  h.2.2 _ (nth_mem σ j (by rw [h.1]; exact hj))

theorem pair_aut (σ : List Nat) (h1 : IsPermL 12 σ) (h2 : PairResp σ) : IsPAut 12 6 pairG σ := by
  refine ⟨h1, fun m => ⟨fun i => m (applyL σ (2 * i) / 2), fun j hj => ?_⟩⟩
  show codeword 6 pairG m (applyL σ j) = codeword 6 pairG (fun i => m (applyL σ (2 * i) / 2)) j
  rw [codeword_pair m _ (applyL_lt σ 12 j h1 hj), codeword_pair _ j hj]
  show m (applyL σ j / 2) = m (applyL σ (2 * (j / 2)) / 2)
  rcases Nat.mod_two_eq_zero_or_one j with h | h
  · rw [show 2 * (j / 2) = j by omega]
  · have hj' : j = 2 * (j / 2) + 1 := by omega
    rw [h2 (j / 2) (by omega), ← hj']

/-- Block permutations: the dihedral group of order 12 acting on the 6 pairs. -/
def blk (t i : Nat) : Nat := if t < 6 then (i + t) % 6 else (t + 12 - i) % 6

/-- Block permutation `t` combined with the swap pattern `s` (one bit per pair). -/
def mkPerm (t s : Nat) : List Nat :=
  (List.range 12).map (fun j => 2 * blk t (j / 2) + (j % 2 + s / 2 ^ (j / 2)) % 2)

/-- 12 · 64 = 768 permutations of the 12 coordinates preserving the pair partition. -/
def pairAuts : List (List Nat) := (List.range 12).flatMap (fun t => (List.range 64).map (mkPerm t))

theorem pairAuts_length : pairAuts.length = 768 := by decide +kernel

/-- Recover the block permutation index `t` and the swap pattern `s` from `σ`. -/
def keyOf (σ : List Nat) : Nat :=
  let p0 := applyL σ 0 / 2
  let p1 := applyL σ 2 / 2
  let t := if p1 = (p0 + 1) % 6 then p0 else p0 + 6
  let s := (List.range 6).foldr (fun i acc => applyL σ (2 * i) % 2 * 2 ^ i + acc) 0
  64 * t + s

theorem pairAuts_keys : pairAuts.map keyOf = List.range 768 := by decide +kernel

theorem pairAuts_nodup : pairAuts.Nodup := by
  have h : (pairAuts.map keyOf).Nodup := by rw [pairAuts_keys]; exact List.nodup_range
  exact List.Pairwise.of_map keyOf (fun a b hab e => hab (e ▸ rfl)) h

theorem pairAuts_ok : ∀ σ ∈ pairAuts, IsPermL 12 σ ∧ PairResp σ := by decide +kernel

theorem pairAuts_aut : ∀ σ ∈ pairAuts, IsPAut 12 6 pairG σ :=
  fun σ h => pair_aut σ (pairAuts_ok σ h).1 (pairAuts_ok σ h).2

/-- Reading "the maximal order is 660" for all ternary `[12,6]` codes (MDS dropped):
no `[12,6]` code has more than 660 distinct permutation automorphisms. -/
def AtMost660 : Prop :=
  ∀ G (L : List (List Nat)), IsGenMatrix 12 6 G → L.Nodup →
    (∀ σ ∈ L, IsPAut 12 6 G σ) → L.length ≤ 660

theorem atMost660_false : ¬ AtMost660 := by
  intro h
  have := h pairG pairAuts pair_gen pairAuts_nodup pairAuts_aut
  rw [pairAuts_length] at this
  omega

theorem nodup_length_le {α : Type} [DecidableEq α] :
    ∀ (L M : List α), L.Nodup → (∀ x ∈ L, x ∈ M) → L.length ≤ M.length := by
  intro L
  induction L with
  | nil => intro M _ _; exact Nat.zero_le _
  | cons a L ih =>
    intro M hnd hsub
    rw [List.nodup_cons] at hnd
    have ha : a ∈ M := hsub a (List.mem_cons_self ..)
    have h' : ∀ x ∈ L, x ∈ M.erase a := by
      intro x hx
      have hxa : x ≠ a := fun e => hnd.1 (e ▸ hx)
      exact (List.mem_erase_of_ne hxa).2 (hsub x (List.mem_cons_of_mem _ hx))
    have := ih (M.erase a) hnd.2 h'
    rw [List.length_erase_of_mem ha] at this
    have := List.length_pos_of_mem ha
    simp only [List.length_cons]
    omega

/-- Whatever the order `N` of the permutation automorphism group of the pair code is,
it is at least 768 > 660 (the true value is 2⁶ · 6! = 46080). -/
theorem pair_order_ge (N : Nat) (h : PAutOrder 12 6 pairG N) : 768 ≤ N := by
  obtain ⟨L, _, hlen, hiff⟩ := h
  have := nodup_length_le pairAuts L pairAuts_nodup (fun σ hσ => (hiff σ).2 (pairAuts_aut σ hσ))
  rw [pairAuts_length] at this
  omega

/-! ## The Golay reading: `[12,6,6]` ternary codes with more than 660 permutation automorphisms

Up to monomial equivalence the extended ternary Golay code is the unique `[12,6,6]` ternary
code, but its monomial class splits into several *permutation* equivalence classes with
different permutation automorphism groups.  `golay` (above) has `|PAut| = 660`; scaling its
column 6 by `2` gives `golay'`, whose `PAut` is `M₁₁` of order 7920 (exact orders: `verify.py`).
Here we prove that `golay'` is a `[12,6,6]` code with at least 720 > 660 permutation
automorphisms. -/

/-- `golay` with column 6 multiplied by 2 (a monomially equivalent code). -/
def golay' : Nat → Nat → F3 := fun i j => if j = 6 then 2 * golay i j else golay i j

theorem comb_smul (k : Nat) (m : Nat → F3) (G : Nat → Nat → F3) (s : F3) (j : Nat) :
    comb k m (fun i j' => s * G i j') j = s * comb k m G j := by
  induction k with
  | zero => simp only [comb]; revert s; decide
  | succ k ih =>
    simp only [comb]
    rw [ih]
    clear ih
    generalize comb k m G j = X
    generalize m k = c
    generalize G k j = g
    revert s X c g; decide

theorem codeword_golay' (m : Nat → F3) (j : Nat) :
    codeword 6 golay' m j = (if j = 6 then 2 else 1) * codeword 6 golay m j := by
  unfold codeword
  by_cases h : j = 6
  · subst h
    rw [comb_congr_vec 6 m golay' (fun i j' => 2 * golay i j') 6 6 (fun i _ => rfl), comb_smul]
    rfl
  · rw [comb_congr_vec 6 m golay' golay j j (fun i _ => by simp [golay', h])]
    simp only [h, if_false]
    generalize comb 6 m golay j = x
    revert x; decide

theorem sumTo_congr (n : Nat) (f g : Nat → Nat) (h : ∀ j, j < n → f j = g j) :
    sumTo n f = sumTo n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumTo]
    rw [ih (fun j hj => h j (by omega)), h n (by omega)]

theorem wt_golay' (m : Nat → F3) : wt 12 (codeword 6 golay' m) = wt 12 (codeword 6 golay m) := by
  apply sumTo_congr
  intro j _
  rw [codeword_golay']
  generalize codeword 6 golay m j = x
  by_cases h : j = 6
  · simp only [h, if_true]; revert x; decide
  · simp only [h, if_false]; revert x; decide

/-- `golay'` generates a `[12,6]` code of minimum distance exactly 6. -/
theorem golay'_12_6_6 : IsGenMatrix 12 6 golay' ∧ HasMinDist 12 6 golay' 6 := by
  obtain ⟨hgen, hge, m0, hm0, hw0⟩ := golay_12_6_6
  refine ⟨?_, ?_, m0, hm0, by rw [wt_golay']; exact hw0⟩
  · intro m hm
    obtain ⟨j, hj, hne⟩ := hgen m hm
    refine ⟨j, hj, ?_⟩
    rw [codeword_golay']
    generalize codeword 6 golay m j = x at hne
    by_cases h : j = 6
    · simp only [h, if_true]; revert x; decide
    · simp only [h, if_false]; revert x; decide
  · intro m hm
    rw [wt_golay']
    exact hge m hm

/-- Combinations of combinations. -/
theorem comb_comb (K k : Nat) (m : Nat → F3) (M : Nat → Nat → F3) (G : Nat → Nat → F3) (j : Nat) :
    comb K m (fun i j' => comb k (M i) G j') j
      = comb k (fun l => comb K m (fun i _ => M i l) 0) G j := by
  induction K with
  | zero =>
    simp only [comb]
    exact (comb_zero_coef k _ G j (fun _ _ => rfl)).symm
  | succ K ih =>
    simp only [comb]
    rw [ih, comb_congr_coef k (fun l => comb K m (fun i _ => M i l) 0 + m K * M K l)
      (fun l => 1 * comb K m (fun i _ => M i l) 0 + m K * M K l) G j
      (fun l _ => by
        show comb K m (fun i _ => M i l) 0 + m K * M K l
          = 1 * comb K m (fun i _ => M i l) 0 + m K * M K l
        generalize comb K m (fun i _ => M i l) 0 = X
        generalize m K * M K l = y
        revert X y; decide),
      comb_lin]
    generalize comb k (fun l => comb K m (fun i _ => M i l) 0) G j = X
    generalize comb k (M K) G j = Y
    generalize m K = c
    revert X Y c; decide

/-- A permutation is an automorphism as soon as every permuted generator row is the
codeword of its own first `k` entries (a finite, decidable check). -/
theorem paut_of_rows (n k : Nat) (G : Nat → Nat → F3) (σ : List Nat) (hp : IsPermL n σ)
    (hrows : ∀ i, i < k → ∀ j, j < n →
      G i (applyL σ j) = comb k (fun l => G i (applyL σ l)) G j) :
    IsPAut n k G σ := by
  refine ⟨hp, fun m => ⟨fun l => comb k m (fun i _ => G i (applyL σ l)) 0, fun j hj => ?_⟩⟩
  show comb k m G (applyL σ j) = comb k (fun l => comb k m (fun i _ => G i (applyL σ l)) 0) G j
  calc comb k m G (applyL σ j)
      = comb k m (fun i j' => comb k (fun l => G i (applyL σ l)) G j') j :=
        comb_congr_vec k m G _ (applyL σ j) j (fun i hi => hrows i hi j hj)
    _ = _ := comb_comb k k m (fun i l => G i (applyL σ l)) G j

/-- `golay'` is systematic: its first six columns form the identity matrix. -/
theorem golay'_sys (m : Nat → F3) (j : Nat) (hj : j < 6) : comb 6 m golay' j = m j := by
  have h : ∀ i, i < 6 → ∀ j, j < 6 → golay' i j = if i = j then 1 else 0 := by decide
  rw [comb_congr_vec 6 m golay' (fun i _ => if i = j then 1 else 0) j j
    (fun i hi => h i hi j hj)]
  exact comb_ind 6 m j j hj

/-- Decidable check on the six redundancy coordinates of every permuted generator row. -/
def RowsOK (σ : List Nat) : Prop :=
  ∀ i, i < 6 → ∀ t, t < 6 →
    golay' i (applyL σ (6 + t)) = comb 6 (fun l => golay' i (applyL σ l)) golay' (6 + t)

instance : DecidablePred RowsOK := fun σ => by unfold RowsOK; infer_instance

theorem rows_of_RowsOK (σ : List Nat) (h : RowsOK σ) : ∀ i, i < 6 → ∀ j, j < 12 →
    golay' i (applyL σ j) = comb 6 (fun l => golay' i (applyL σ l)) golay' j := by
  intro i hi j hj
  by_cases hj6 : j < 6
  · rw [golay'_sys _ j hj6]
  · have := h i hi (j - 6) (by omega)
    rwa [show 6 + (j - 6) = j by omega] at this

/-- Composition of permutation lists: `(comp σ τ)[j] = σ[τ[j]]`. -/
def comp (σ τ : List Nat) : List Nat := τ.map (applyL σ)

theorem applyL_comp (σ τ : List Nat) (j : Nat) (hj : j < τ.length) :
    applyL (comp σ τ) j = applyL σ (applyL τ j) :=
  nth_map (applyL σ) τ j hj

/-- Length 12, values `< 12`, and codewords are mapped to codewords. -/
def AutCore (σ : List Nat) : Prop :=
  σ.length = 12 ∧ (∀ j, j < 12 → applyL σ j < 12) ∧
    ∀ m, InCode 12 6 golay' (fun j => codeword 6 golay' m (applyL σ j))

theorem autCore_of_paut (σ : List Nat) (h : IsPAut 12 6 golay' σ) : AutCore σ :=
  ⟨h.1.1, fun j hj => applyL_lt σ 12 j h.1 hj, h.2⟩

/-- Products of automorphisms are automorphisms. -/
theorem autCore_comp (σ τ : List Nat) (hσ : AutCore σ) (hτ : AutCore τ) : AutCore (comp σ τ) := by
  refine ⟨by unfold comp; rw [List.length_map]; exact hτ.1, fun j hj => ?_, fun m => ?_⟩
  · rw [applyL_comp σ τ j (by rw [hτ.1]; exact hj)]
    exact hσ.2.1 _ (hτ.2.1 j hj)
  · obtain ⟨m1, h1⟩ := hσ.2.2 m
    obtain ⟨m2, h2⟩ := hτ.2.2 m1
    refine ⟨m2, fun j hj => ?_⟩
    have e1 := h1 (applyL τ j) (hτ.2.1 j hj)
    have e2 := h2 j hj
    show codeword 6 golay' m (applyL (comp σ τ) j) = codeword 6 golay' m2 j
    rw [applyL_comp σ τ j (by rw [hτ.1]; exact hj)]
    exact e1.trans e2

/-- 30 automorphisms of `golay'` with pairwise different images of the points `(0, 1)`. -/
def H1 : List (List Nat) := [
  [0,  1,  2,  3,  4,  5,  6,  7,  8,  9,  10,  11],
  [0,  2,  1,  3,  6,  5,  4,  9,  11,  7,  10,  8],
  [0,  3,  1,  2,  5,  6,  4,  7,  11,  9,  8,  10],
  [0,  4,  1,  5,  2,  6,  3,  7,  8,  10,  11,  9],
  [0,  5,  1,  2,  3,  4,  6,  11,  7,  8,  9,  10],
  [0,  6,  1,  3,  2,  4,  5,  11,  9,  10,  7,  8],
  [0,  7,  1,  2,  8,  10,  6,  9,  5,  3,  11,  4],
  [0,  8,  1,  2,  7,  6,  10,  5,  9,  11,  3,  4],
  [0,  9,  1,  2,  11,  4,  10,  3,  8,  7,  5,  6],
  [0,  10,  1,  3,  9,  5,  8,  6,  7,  11,  2,  4],
  [0,  11,  1,  2,  9,  10,  4,  8,  3,  5,  7,  6],
  [1,  0,  2,  3,  4,  8,  10,  9,  5,  7,  6,  11],
  [1,  2,  0,  3,  10,  8,  4,  7,  11,  9,  6,  5],
  [1,  3,  0,  2,  8,  10,  4,  9,  11,  7,  5,  6],
  [1,  4,  0,  5,  11,  9,  3,  10,  8,  7,  2,  6],
  [1,  5,  0,  2,  9,  10,  6,  8,  7,  11,  3,  4],
  [1,  6,  0,  3,  7,  8,  5,  10,  9,  11,  2,  4],
  [1,  7,  0,  2,  11,  4,  6,  3,  5,  9,  8,  10],
  [1,  8,  0,  2,  3,  4,  10,  11,  9,  5,  7,  6],
  [1,  9,  0,  2,  5,  6,  10,  7,  8,  3,  11,  4],
  [1,  10,  0,  3,  2,  4,  8,  11,  7,  6,  9,  5],
  [1,  11,  0,  2,  7,  6,  4,  5,  3,  8,  9,  10],
  [2,  0,  1,  3,  6,  11,  10,  7,  5,  9,  4,  8],
  [2,  1,  0,  3,  10,  11,  6,  9,  8,  7,  4,  5],
  [2,  3,  0,  1,  11,  10,  6,  7,  8,  9,  5,  4],
  [2,  4,  0,  3,  9,  11,  5,  10,  7,  8,  1,  6],
  [2,  5,  0,  1,  7,  10,  4,  11,  9,  8,  3,  6],
  [2,  6,  0,  4,  8,  9,  1,  11,  10,  7,  3,  5],
  [2,  7,  0,  1,  5,  4,  10,  9,  11,  3,  8,  6],
  [2,  8,  0,  1,  9,  4,  6,  5,  3,  11,  7,  10]]

/-- 24 automorphisms of `golay'` fixing the points `0` and `1`. -/
def H2 : List (List Nat) := [
  [0,  1,  2,  3,  4,  5,  6,  7,  8,  9,  10,  11],
  [0,  1,  2,  5,  6,  3,  4,  11,  9,  8,  10,  7],
  [0,  1,  2,  7,  6,  8,  10,  9,  11,  3,  4,  5],
  [0,  1,  2,  8,  10,  7,  6,  5,  3,  11,  4,  9],
  [0,  1,  2,  9,  10,  11,  4,  3,  5,  7,  6,  8],
  [0,  1,  2,  11,  4,  9,  10,  8,  7,  5,  6,  3],
  [0,  1,  3,  2,  4,  6,  5,  9,  10,  7,  8,  11],
  [0,  1,  3,  6,  5,  2,  4,  11,  7,  10,  8,  9],
  [0,  1,  3,  7,  8,  11,  4,  2,  6,  9,  5,  10],
  [0,  1,  3,  9,  5,  10,  8,  7,  11,  2,  4,  6],
  [0,  1,  3,  10,  8,  9,  5,  6,  2,  11,  4,  7],
  [0,  1,  3,  11,  4,  7,  8,  10,  9,  6,  5,  2],
  [0,  1,  4,  5,  3,  6,  2,  10,  9,  7,  11,  8],
  [0,  1,  4,  6,  2,  5,  3,  8,  7,  9,  11,  10],
  [0,  1,  4,  7,  11,  8,  3,  5,  6,  10,  2,  9],
  [0,  1,  4,  8,  3,  7,  11,  9,  10,  6,  2,  5],
  [0,  1,  4,  9,  11,  10,  2,  6,  5,  8,  3,  7],
  [0,  1,  4,  10,  2,  9,  11,  7,  8,  5,  3,  6],
  [0,  1,  5,  2,  6,  4,  3,  8,  10,  11,  9,  7],
  [0,  1,  5,  4,  3,  2,  6,  7,  11,  10,  9,  8],
  [0,  1,  5,  7,  6,  11,  9,  10,  8,  4,  3,  2],
  [0,  1,  5,  8,  3,  10,  9,  11,  7,  2,  6,  4],
  [0,  1,  5,  10,  9,  8,  3,  4,  2,  7,  6,  11],
  [0,  1,  5,  11,  9,  7,  6,  2,  4,  8,  3,  10]]

theorem H1_ok : ∀ σ ∈ H1, IsPermL 12 σ ∧ RowsOK σ := by decide +kernel

theorem H2_ok : ∀ σ ∈ H2, IsPermL 12 σ ∧ RowsOK σ := by decide +kernel

theorem H2_fix : ∀ k ∈ H2, applyL k 0 = 0 ∧ applyL k 1 = 1 := by decide +kernel

theorem H1_sep :
    H1.Pairwise (fun a b => (applyL a 0, applyL a 1) ≠ (applyL b 0, applyL b 1)) := by
  decide +kernel

theorem H1_blocks : ∀ h ∈ H1, (H2.map (comp h)).Nodup := by decide +kernel

theorem autCore_H1 (h : List Nat) (hh : h ∈ H1) : AutCore h :=
  autCore_of_paut h (paut_of_rows 12 6 golay' h (H1_ok h hh).1 (rows_of_RowsOK h (H1_ok h hh).2))

theorem autCore_H2 (k : List Nat) (hk : k ∈ H2) : AutCore k :=
  autCore_of_paut k (paut_of_rows 12 6 golay' k (H2_ok k hk).1 (rows_of_RowsOK k (H2_ok k hk).2))

/-- The 720 products `h ∘ k` (`h ∈ H1`, `k ∈ H2`): permutation automorphisms of `golay'`. -/
def golayAuts : List (List Nat) := H1.flatMap (fun h => H2.map (comp h))

theorem golayAuts_length : golayAuts.length = 720 := by decide +kernel

theorem golayAuts_perm : ∀ σ ∈ golayAuts, IsPermL 12 σ := by decide +kernel

theorem golayAuts_aut : ∀ σ ∈ golayAuts, IsPAut 12 6 golay' σ := by
  intro σ hσ
  refine ⟨golayAuts_perm σ hσ, ?_⟩
  obtain ⟨h, hh, hσ'⟩ := List.mem_flatMap.1 hσ
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hσ'
  exact (autCore_comp h k (autCore_H1 h hh) (autCore_H2 k hk)).2.2

/-- The products are pairwise distinct: different `h` give different images of `(0, 1)`. -/
theorem golayAuts_nodup : golayAuts.Nodup := by
  unfold golayAuts List.Nodup
  rw [List.pairwise_flatMap]
  refine ⟨H1_blocks, H1_sep.imp (fun {a b} hab => ?_)⟩
  intro x hx y hy hxy
  obtain ⟨k1, hk1, rfl⟩ := List.mem_map.1 hx
  obtain ⟨k2, hk2, rfl⟩ := List.mem_map.1 hy
  apply hab
  have l1 := (H2_ok k1 hk1).1.1
  have l2 := (H2_ok k2 hk2).1.1
  have e0 : applyL (comp a k1) 0 = applyL a 0 := by
    rw [applyL_comp a k1 0 (by rw [l1]; decide), (H2_fix k1 hk1).1]
  have e1 : applyL (comp a k1) 1 = applyL a 1 := by
    rw [applyL_comp a k1 1 (by rw [l1]; decide), (H2_fix k1 hk1).2]
  have f0 : applyL (comp b k2) 0 = applyL b 0 := by
    rw [applyL_comp b k2 0 (by rw [l2]; decide), (H2_fix k2 hk2).1]
  have f1 : applyL (comp b k2) 1 = applyL b 1 := by
    rw [applyL_comp b k2 1 (by rw [l2]; decide), (H2_fix k2 hk2).2]
  rw [← e0, ← e1, ← f0, ← f1, hxy]

/-- Reading "the maximal order is 660" for ternary `[12,6,6]` (Golay) codes:
no such code has more than 660 distinct permutation automorphisms. -/
def GolayMax660 : Prop :=
  ∀ G (L : List (List Nat)), IsGenMatrix 12 6 G → HasMinDist 12 6 G 6 → L.Nodup →
    (∀ σ ∈ L, IsPAut 12 6 G σ) → L.length ≤ 660

theorem golay_reading_witness : ∃ G : Nat → Nat → F3, ∃ L : List (List Nat), IsGenMatrix 12 6 G ∧
    HasMinDist 12 6 G 6 ∧ L.Nodup ∧ (∀ σ ∈ L, IsPAut 12 6 G σ) ∧ 660 < L.length :=
  ⟨golay', golayAuts, golay'_12_6_6.1, golay'_12_6_6.2, golayAuts_nodup, golayAuts_aut,
    by rw [golayAuts_length]; decide⟩

theorem golay_reading_false : ¬ GolayMax660 := by
  intro h
  obtain ⟨G, L, h1, h2, h3, h4, h5⟩ := golay_reading_witness
  have := h G L h1 h2 h3 h4
  omega

/-- Whatever the order `N` of `PAut(golay')` is, it is at least 720 (in fact 7920). -/
theorem golay'_order_ge (N : Nat) (h : PAutOrder 12 6 golay' N) : 720 ≤ N := by
  obtain ⟨L, _, hlen, hiff⟩ := h
  have := nodup_length_le golayAuts L golayAuts_nodup
    (fun σ hσ => (hiff σ).2 (golayAuts_aut σ hσ))
  rw [golayAuts_length] at this
  omega

end TernaryMDS

open TernaryMDS in
#print axioms dep
open TernaryMDS in
#print axioms no_mds_ternary
open TernaryMDS in
#print axioms no_mds_12_6
open TernaryMDS in
#print axioms conjecture_00000001090_false
open TernaryMDS in
#print axioms conjecture_00000001090_monomial_false
open TernaryMDS in
#print axioms no_mds_12_7
open TernaryMDS in
#print axioms tetra_mds
open TernaryMDS in
#print axioms golay_12_6_6
open TernaryMDS in
#print axioms atMost660_false
open TernaryMDS in
#print axioms pair_order_ge
open TernaryMDS in
#print axioms golay'_12_6_6
open TernaryMDS in
#print axioms golay_reading_witness
open TernaryMDS in
#print axioms golay_reading_false
open TernaryMDS in
#print axioms golay'_order_ge
