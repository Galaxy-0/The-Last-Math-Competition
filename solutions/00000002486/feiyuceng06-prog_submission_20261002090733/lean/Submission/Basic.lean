import Mathlib

/-!
# Conjecture 00000002486 holds

The conjecture: the dominance partial order on partitions is a lattice (joins and meets
exist), and the structure is closed under conjugation duality.

Partitions of `n` are Mathlib's `Nat.Partition n`. Writing the parts of `λ` in weakly
decreasing order `λ₁ ≥ λ₂ ≥ ⋯`, the dominance order is `λ ⊴ μ` iff
`λ₁ + ⋯ + λ_k ≤ μ₁ + ⋯ + μ_k` for every `k`. The conjugate partition `λ'` has parts
`λ'_j = #{i | λ_i ≥ j}`. We prove, for every `n`:

* dominance is a partial order on the partitions of `n`;
* every two partitions have a meet and a join, so they form a lattice;
* conjugation is an involution that reverses dominance. Hence it exchanges meets and
  joins, and the lattice is self-dual.

**Meets.** A sequence `S` is the partial-sum sequence of a partition of `n` iff
`S 0 = 0`, `S` is nondecreasing and concave, and `S k = n` for `k ≥ n`. The pointwise
minimum of two such sequences is again one; it gives the meet.

**Conjugation.** `Σ_t(λ') = ∑ᵢ min(λᵢ, t) = n - G_λ(t)` with `G_λ(t) = ∑ᵢ (λᵢ - t)⁺`. The
key identity is `Σ_J(λ) ≤ J t + G_λ(t)`, with equality for a suitable `J` given `t` and for
a suitable `t` given `J`. It yields both the order reversal and `λ'' = λ`. Joins are then
`λ ∨ μ = (λ' ∧ μ')'`.
-/

namespace Submission00000002486

open Finset

variable {n : ℕ}

/-- The parts of `p`, listed in weakly decreasing order `λ₁ ≥ λ₂ ≥ ⋯`. -/
def sortedParts (p : Nat.Partition n) : List ℕ := p.parts.sort (· ≥ ·)

/-- `partialSum p k = λ₁ + ⋯ + λ_k` (all parts once `k` exceeds the number of parts). -/
def partialSum (p : Nat.Partition n) (k : ℕ) : ℕ := ((sortedParts p).take k).sum

/-- The dominance order: `p ⊴ q` iff `p₁ + ⋯ + p_k ≤ q₁ + ⋯ + q_k` for every `k`. -/
def Dominates (p q : Nat.Partition n) : Prop := ∀ k, partialSum p k ≤ partialSum q k

/-- `m` is the meet (greatest lower bound) of `p` and `q` for dominance. -/
def IsMeet (p q m : Nat.Partition n) : Prop :=
  Dominates m p ∧ Dominates m q ∧ ∀ r, Dominates r p → Dominates r q → Dominates r m

/-- `j` is the join (least upper bound) of `p` and `q` for dominance. -/
def IsJoin (p q j : Nat.Partition n) : Prop :=
  Dominates p j ∧ Dominates q j ∧ ∀ r, Dominates p r → Dominates q r → Dominates j r

/-- `colLen p j = #{i | λ_i > j}`, the length of column `j + 1` of the Young diagram. -/
def colLen (p : Nat.Partition n) (j : ℕ) : ℕ := (p.parts.filter (j < ·)).card

lemma sum_filter_pos (s : Multiset ℕ) : (s.filter (0 < ·)).sum = s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    by_cases ha : 0 < a
    · simp [ha, ih]
    · simp [ih, Nat.eq_zero_of_not_pos ha]

lemma sum_card_filter_lt (s : Multiset ℕ) (k : ℕ) :
    ∑ j ∈ range k, (s.filter (j < ·)).card = (s.map fun x => min x k).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have h : ∀ j, (Multiset.filter (j < ·) (a ::ₘ s)).card
        = (if j < a then 1 else 0) + (s.filter (j < ·)).card := by
      intro j; by_cases hj : j < a <;> simp [hj, add_comm]
    simp_rw [h, sum_add_distrib, ih, Multiset.map_cons, Multiset.sum_cons, sum_boole]
    congr 1
    have : (range k).filter (· < a) = range (min a k) := by ext j; simp; omega
    simp [this]

lemma sum_colLen (p : Nat.Partition n) (k : ℕ) :
    ∑ j ∈ range k, colLen p j = (p.parts.map fun x => min x k).sum :=
  sum_card_filter_lt p.parts k

lemma sum_colLen_n (p : Nat.Partition n) : ∑ j ∈ range n, colLen p j = n := by
  rw [sum_colLen]
  conv_rhs => rw [← p.parts_sum]
  conv_rhs => rw [← Multiset.map_id p.parts]
  exact congrArg _ (Multiset.map_congr rfl fun x hx => min_eq_left (p.le_of_mem_parts hx))

/-- The conjugate partition `λ'`: its parts are the nonzero column lengths
`λ'_j = #{i | λ_i ≥ j}` for `j = 1, …, n`. -/
def conj (p : Nat.Partition n) : Nat.Partition n where
  parts := ((Multiset.range n).map (colLen p)).filter (0 < ·)
  parts_pos h := (Multiset.mem_filter.1 h).2
  parts_sum := by rw [sum_filter_pos]; exact sum_colLen_n p

/-! ### Partial sums through the `i`-th largest part -/

lemma sum_take_eq (L : List ℕ) (k : ℕ) : (L.take k).sum = ∑ i ∈ range k, L.getD i 0 := by
  induction L generalizing k with
  | nil => simp
  | cons a L ih =>
    cases k with
    | zero => simp
    | succ k => rw [List.take_succ_cons, List.sum_cons, ih, sum_range_succ']; simp [add_comm]

lemma sum_map_eq (L : List ℕ) (g : ℕ → ℕ) (hg : g 0 = 0) (N : ℕ) (hN : L.length ≤ N) :
    (L.map g).sum = ∑ i ∈ range N, g (L.getD i 0) := by
  induction L generalizing N with
  | nil => simp [hg]
  | cons a L ih =>
    cases N with
    | zero => simp at hN
    | succ N =>
      rw [sum_range_succ', List.map_cons, List.sum_cons, ih N (by simpa using hN)]
      simp [add_comm]

/-- `part p i` is the `(i+1)`-th largest part of `p` (`0` if there is none). -/
def part (p : Nat.Partition n) (i : ℕ) : ℕ := (sortedParts p).getD i 0

lemma length_sortedParts_le (p : Nat.Partition n) : (sortedParts p).length ≤ n := by
  rw [sortedParts, Multiset.length_sort]
  calc Multiset.card p.parts = (p.parts.map fun _ => 1).sum := by simp
    _ ≤ (p.parts.map id).sum :=
        Multiset.sum_map_le_sum_map _ _ fun x hx => p.parts_pos hx
    _ = n := by rw [Multiset.map_id, p.parts_sum]

lemma part_antitone (p : Nat.Partition n) : Antitone (part p) := by
  intro i j hij
  by_cases hj : j < (sortedParts p).length
  · have hi : i < (sortedParts p).length := lt_of_le_of_lt hij hj
    simp only [part, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      List.getElem?_eq_getElem hj, Option.getD_some]
    rcases eq_or_lt_of_le hij with rfl | hlt
    · exact le_rfl
    · exact List.pairwise_iff_getElem.1 (Multiset.pairwise_sort p.parts _) i j hi hj hlt
  · rw [part, List.getD_eq_default _ _ (by omega)]
    exact Nat.zero_le _

lemma part_eq_zero (p : Nat.Partition n) {i : ℕ} (hi : n ≤ i) : part p i = 0 :=
  List.getD_eq_default _ _ ((length_sortedParts_le p).trans hi)

lemma partialSum_eq (p : Nat.Partition n) (k : ℕ) :
    partialSum p k = ∑ i ∈ range k, part p i :=
  sum_take_eq _ _

lemma sum_parts_eq (p : Nat.Partition n) (g : ℕ → ℕ) (hg : g 0 = 0) {N : ℕ} (hN : n ≤ N) :
    (p.parts.map g).sum = ∑ i ∈ range N, g (part p i) := by
  conv_lhs => rw [← Multiset.sort_eq p.parts (· ≥ ·)]
  rw [Multiset.map_coe, Multiset.sum_coe]
  exact sum_map_eq _ g hg N ((length_sortedParts_le p).trans hN)

lemma partialSum_mono (p : Nat.Partition n) : Monotone (partialSum p) := by
  intro a b hab
  rw [partialSum_eq, partialSum_eq]
  exact sum_le_sum_of_subset (range_subset_range.2 hab)

lemma partialSum_of_le (p : Nat.Partition n) {k : ℕ} (hk : n ≤ k) : partialSum p k = n := by
  have h := sum_parts_eq p id rfl hk
  rw [Multiset.map_id, p.parts_sum] at h
  rw [partialSum_eq]
  exact h.symm

lemma partialSum_concave (p : Nat.Partition n) (k : ℕ) :
    partialSum p k + partialSum p (k + 2) ≤ 2 * partialSum p (k + 1) := by
  simp only [partialSum_eq, sum_range_succ]
  have := part_antitone p (Nat.le_add_right k 1)
  omega

lemma eq_of_partialSum_eq {p q : Nat.Partition n} (h : ∀ k, partialSum p k = partialSum q k) :
    p = q := by
  have hd : ∀ i, part p i = part q i := by
    intro i
    have h1 := h (i + 1)
    rw [partialSum_eq, partialSum_eq, sum_range_succ, sum_range_succ, ← partialSum_eq,
      ← partialSum_eq, h i] at h1
    omega
  have posp : ∀ x ∈ sortedParts p, 0 < x := fun x hx => p.parts_pos ((Multiset.mem_sort _).1 hx)
  have posq : ∀ x ∈ sortedParts q, 0 < x := fun x hx => q.parts_pos ((Multiset.mem_sort _).1 hx)
  have hL : sortedParts p = sortedParts q := by
    apply List.ext_getElem?
    intro i
    have hpi := hd i
    simp only [part, List.getD_eq_getElem?_getD] at hpi
    rcases hp' : (sortedParts p)[i]? with _ | a <;> rcases hq' : (sortedParts q)[i]? with _ | b <;>
      simp only [hp', hq', Option.getD_none, Option.getD_some] at hpi
    all_goals first
      | rfl
      | exact absurd hpi (posq _ (List.mem_of_getElem? hq')).ne
      | exact absurd hpi (posp _ (List.mem_of_getElem? hp')).ne'
      | rw [hpi]
  apply Nat.Partition.ext
  rw [← Multiset.sort_eq p.parts (· ≥ ·), ← Multiset.sort_eq q.parts (· ≥ ·)]
  exact congrArg _ hL

/-! ### Partitions given by an antitone sequence of parts -/

lemma partialSum_of_parts_eq {p : Nat.Partition n} {d : ℕ → ℕ} (hd : Antitone d) {J : ℕ}
    (hJ : ∀ j, J ≤ j → d j = 0) (hp : p.parts = (Multiset.range J).map d) (k : ℕ) :
    partialSum p k = ∑ j ∈ range k, d j := by
  have hs : sortedParts p = (List.range J).map d := by
    apply List.Perm.eq_of_pairwise' (r := (· ≥ ·)) (Multiset.pairwise_sort _ _)
    · exact List.Pairwise.map d (fun a b hab => hd hab.le) List.pairwise_lt_range
    · rw [← Multiset.coe_eq_coe]
      simp only [Multiset.sort_eq, hp]
      rfl
  rw [partialSum, hs, sum_take_eq]
  refine sum_congr rfl fun j _ => ?_
  by_cases hj : j < J
  · simp [List.getD_eq_getElem?_getD, hj]
  · rw [List.getD_eq_default _ _ (by simp; omega), hJ j (by omega)]

lemma exists_of_concave (S : ℕ → ℕ) (h0 : S 0 = 0) (hmono : Monotone S)
    (hconc : ∀ k, S k + S (k + 2) ≤ 2 * S (k + 1)) (hn : ∀ k, n ≤ k → S k = n) :
    ∃ p : Nat.Partition n, ∀ k, partialSum p k = S k := by
  set d : ℕ → ℕ := fun k => S (k + 1) - S k with hd_def
  have hd : Antitone d := antitone_nat_of_succ_le fun k => by
    have := hconc k; have := hmono (Nat.le_add_right k 1)
    have := hmono (Nat.le_add_right (k + 1) 1)
    have e : S (k + 1 + 1) = S (k + 2) := rfl
    simp only [hd_def]; omega
  have hdn : d n = 0 := by simp [hd_def, hn n le_rfl, hn (n + 1) (by omega)]
  have hex : ∃ J, d J = 0 := ⟨n, hdn⟩
  have hJ0 : ∀ j, Nat.find hex ≤ j → d j = 0 :=
    fun j hj => Nat.eq_zero_of_le_zero ((hd hj).trans (Nat.find_spec hex).le)
  have hJn : Nat.find hex ≤ n := Nat.find_min' hex hdn
  have hsum : ∀ k, ∑ i ∈ range k, d i = S k := fun k => by
    rw [sum_range_tsub hmono k, h0, Nat.sub_zero]
  refine ⟨⟨(Multiset.range (Nat.find hex)).map d, ?_, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.1 hx
    exact Nat.pos_of_ne_zero (Nat.find_min hex (Multiset.mem_range.1 hj))
  · show ∑ j ∈ range (Nat.find hex), d j = n
    rw [← hn n le_rfl, ← hsum n, ← sum_range_add_sum_Ico _ hJn,
      sum_eq_zero fun j hj => hJ0 j (mem_Ico.1 hj).1, add_zero]
  · intro k
    rw [partialSum_of_parts_eq hd hJ0 rfl k, hsum]

lemma exists_inf (T : Finset (Nat.Partition n)) (hT : T.Nonempty) :
    ∃ m : Nat.Partition n, ∀ k, partialSum m k = T.inf' hT fun r => partialSum r k := by
  obtain ⟨r₀, hr₀⟩ := id hT
  apply exists_of_concave
  · exact le_antisymm (inf'_le_of_le _ hr₀ (by simp [partialSum])) (Nat.zero_le _)
  · intro a b hab
    exact le_inf' _ _ fun r hr => (inf'_le _ hr).trans (partialSum_mono r hab)
  · intro k
    obtain ⟨r, hr, hreq⟩ := exists_mem_eq_inf' hT fun r => partialSum r (k + 1)
    have hreq' : T.inf' hT (fun r => partialSum r (k + 1)) = partialSum r (k + 1) := hreq
    have h1 : T.inf' hT (fun r => partialSum r k) ≤ partialSum r k := inf'_le _ hr
    have h2 : T.inf' hT (fun r => partialSum r (k + 2)) ≤ partialSum r (k + 2) := inf'_le _ hr
    have := partialSum_concave r k
    show T.inf' hT (fun r => partialSum r k) + T.inf' hT (fun r => partialSum r (k + 2))
      ≤ 2 * T.inf' hT (fun r => partialSum r (k + 1))
    rw [hreq']
    omega
  · intro k hk
    exact le_antisymm (inf'_le_of_le _ hr₀ (partialSum_of_le r₀ hk).le)
      (le_inf' _ _ fun r _ => (partialSum_of_le r hk).ge)

/-! ### Dominance is a partial order, and meets exist -/

lemma dominates_refl (p : Nat.Partition n) : Dominates p p := fun _ => le_rfl

lemma dominates_trans {p q r : Nat.Partition n} (h₁ : Dominates p q) (h₂ : Dominates q r) :
    Dominates p r := fun k => (h₁ k).trans (h₂ k)

lemma dominates_antisymm {p q : Nat.Partition n} (h₁ : Dominates p q) (h₂ : Dominates q p) :
    p = q :=
  eq_of_partialSum_eq fun k => le_antisymm (h₁ k) (h₂ k)

lemma exists_meet (p q : Nat.Partition n) : ∃ m, IsMeet p q m := by
  obtain ⟨m, hm⟩ := exists_inf {p, q} (insert_nonempty p {q})
  refine ⟨m, fun k => ?_, fun k => ?_, fun r hp hq k => ?_⟩
  · rw [hm]; exact inf'_le _ (mem_insert_self p {q})
  · rw [hm]; exact inf'_le _ (mem_insert_of_mem (mem_singleton_self q))
  · rw [hm]
    refine le_inf' _ _ fun s hs => ?_
    rcases mem_insert.1 hs with rfl | hs
    · exact hp k
    · rw [mem_singleton.1 hs]; exact hq k

/-! ### Conjugation reverses dominance -/

lemma colLen_antitone (p : Nat.Partition n) : Antitone (colLen p) :=
  fun _ _ hij => Multiset.card_le_card
    (Multiset.monotone_filter_right _ fun _ hx => lt_of_le_of_lt hij hx)

/-- `F p t = ∑ᵢ min(λ_i, t)`. -/
def F (p : Nat.Partition n) (t : ℕ) : ℕ := (p.parts.map fun x => min x t).sum

/-- `G p t = ∑ᵢ (λ_i - t)⁺`. -/
def G (p : Nat.Partition n) (t : ℕ) : ℕ := (p.parts.map fun x => x - t).sum

lemma F_add_G (p : Nat.Partition n) (t : ℕ) : F p t + G p t = n := by
  rw [F, G, ← Multiset.sum_map_add]
  conv_rhs => rw [← p.parts_sum]
  conv_rhs => rw [← Multiset.map_id p.parts]
  exact congrArg _ (Multiset.map_congr rfl fun x _ => show min x t + (x - t) = x by omega)

lemma partialSum_conj (p : Nat.Partition n) (k : ℕ) : partialSum (conj p) k = F p k := by
  have hn : colLen p n = 0 := by
    rw [colLen, Multiset.card_eq_zero, Multiset.filter_eq_nil]
    exact fun x hx => not_lt.2 (p.le_of_mem_parts hx)
  have hex : ∃ J, colLen p J = 0 := ⟨n, hn⟩
  have hJ0 : ∀ j, Nat.find hex ≤ j → colLen p j = 0 := fun j hj =>
    Nat.eq_zero_of_le_zero ((colLen_antitone p hj).trans (Nat.find_spec hex).le)
  have hJn : Nat.find hex ≤ n := Nat.find_min' hex hn
  have hparts : (conj p).parts = (Multiset.range (Nat.find hex)).map (colLen p) := by
    show ((Multiset.range n).map (colLen p)).filter (0 < ·) = _
    rw [Multiset.filter_map, ← range_val, ← range_val, ← filter_val]
    congr 2
    ext j
    simp only [mem_filter, mem_range, Function.comp_apply]
    constructor
    · rintro ⟨-, hj⟩
      by_contra hJ
      exact (Nat.pos_iff_ne_zero.1 hj) (hJ0 j (by omega))
    · intro hj
      exact ⟨by omega, Nat.pos_of_ne_zero (Nat.find_min hex hj)⟩
  rw [partialSum_of_parts_eq (colLen_antitone p) hJ0 hparts k, sum_colLen]
  rfl

lemma partialSum_le (p : Nat.Partition n) (J t : ℕ) : partialSum p J ≤ J * t + G p t := by
  rw [partialSum_eq, G, sum_parts_eq p (fun x => x - t) (by simp) (N := J + n) (by omega)]
  calc ∑ i ∈ range J, part p i ≤ ∑ i ∈ range J, (t + (part p i - t)) :=
        sum_le_sum fun i _ => by omega
    _ = J * t + ∑ i ∈ range J, (part p i - t) := by
        rw [sum_add_distrib, sum_const, card_range, smul_eq_mul]
    _ ≤ J * t + ∑ i ∈ range (J + n), (part p i - t) :=
        Nat.add_le_add_left (sum_le_sum_of_subset (range_subset_range.2 (Nat.le_add_right J n))) _

lemma partialSum_split (p : Nat.Partition n) (J t : ℕ) (h₁ : ∀ i < J, t ≤ part p i)
    (h₂ : ∀ i, J ≤ i → part p i ≤ t) : partialSum p J = J * t + G p t := by
  rw [partialSum_eq, G, sum_parts_eq p (fun x => x - t) (by simp) (N := J + n) (by omega),
    ← sum_range_add_sum_Ico _ (show J ≤ J + n by omega),
    sum_eq_zero (s := Ico J (J + n)) fun i hi => by have := h₂ i (mem_Ico.1 hi).1; omega,
    add_zero]
  calc ∑ i ∈ range J, part p i = ∑ i ∈ range J, (t + (part p i - t)) :=
        sum_congr rfl fun i hi => by have := h₁ i (mem_range.1 hi); omega
    _ = J * t + ∑ i ∈ range J, (part p i - t) := by
        rw [sum_add_distrib, sum_const, card_range, smul_eq_mul]

lemma exists_split_threshold (p : Nat.Partition n) (t : ℕ) :
    ∃ J, partialSum p J = J * t + G p t := by
  have hex : ∃ J, part p J ≤ t := ⟨n, by rw [part_eq_zero p le_rfl]; exact Nat.zero_le _⟩
  exact ⟨Nat.find hex, partialSum_split p _ t
    (fun i hi => (not_le.1 (Nat.find_min hex hi)).le)
    (fun i hi => (part_antitone p hi).trans (Nat.find_spec hex))⟩

lemma exists_split_index (p : Nat.Partition n) (k : ℕ) :
    ∃ j, partialSum p k = k * j + G p j :=
  ⟨part p k, partialSum_split p k _ (fun _ hi => part_antitone p hi.le)
    (fun _ hi => part_antitone p hi)⟩

theorem dominates_conj {p q : Nat.Partition n} (h : Dominates p q) :
    Dominates (conj q) (conj p) := by
  intro k
  rw [partialSum_conj, partialSum_conj]
  obtain ⟨J, hJ⟩ := exists_split_threshold p k
  have h1 := partialSum_le q J k
  have h2 := h J
  have h3 := F_add_G p k
  have h4 := F_add_G q k
  omega

theorem conj_conj (p : Nat.Partition n) : conj (conj p) = p := by
  apply eq_of_partialSum_eq
  intro k
  rw [partialSum_conj]
  have e1 := F_add_G (conj p) k
  obtain ⟨J, hJ⟩ := exists_split_threshold (conj p) k
  rw [partialSum_conj] at hJ
  have e2 := F_add_G p J
  have a1 := partialSum_le p k J
  obtain ⟨j, hj⟩ := exists_split_index p k
  have a2 := partialSum_le (conj p) j k
  rw [partialSum_conj] at a2
  have e3 := F_add_G p j
  rw [Nat.mul_comm k J] at a1
  rw [Nat.mul_comm k j] at hj
  omega

theorem dominates_iff_conj (p q : Nat.Partition n) :
    Dominates p q ↔ Dominates (conj q) (conj p) :=
  ⟨dominates_conj, fun h => by simpa only [conj_conj] using dominates_conj h⟩

lemma conj_dominates_iff (p q : Nat.Partition n) :
    Dominates (conj p) q ↔ Dominates (conj q) p := by
  rw [dominates_iff_conj, conj_conj]

lemma dominates_conj_iff (p q : Nat.Partition n) :
    Dominates p (conj q) ↔ Dominates q (conj p) := by
  rw [dominates_iff_conj, conj_conj]

theorem isMeet_iff_isJoin_conj (p q m : Nat.Partition n) :
    IsMeet p q m ↔ IsJoin (conj p) (conj q) (conj m) := by
  simp only [IsMeet, IsJoin]
  constructor
  · rintro ⟨hp, hq, hm⟩
    refine ⟨(dominates_iff_conj _ _).1 hp, (dominates_iff_conj _ _).1 hq, fun r hpr hqr => ?_⟩
    rw [conj_dominates_iff] at hpr hqr ⊢
    exact hm _ hpr hqr
  · rintro ⟨hp, hq, hm⟩
    refine ⟨(dominates_iff_conj _ _).2 hp, (dominates_iff_conj _ _).2 hq, fun r hrp hrq => ?_⟩
    rw [dominates_iff_conj] at hrp hrq ⊢
    exact hm _ hrp hrq

lemma exists_join (p q : Nat.Partition n) : ∃ j, IsJoin p q j := by
  obtain ⟨m, hm⟩ := exists_meet (conj p) (conj q)
  refine ⟨conj m, ?_⟩
  simpa only [conj_conj] using (isMeet_iff_isJoin_conj _ _ _).1 hm

/-- The dominance order on `Nat.Partition n`, bundled as a Mathlib `Lattice`. -/
@[instance_reducible]
noncomputable def dominanceLattice (n : ℕ) : Lattice (Nat.Partition n) where
  le := Dominates
  le_refl := dominates_refl
  le_trans _ _ _ := dominates_trans
  le_antisymm _ _ := dominates_antisymm
  sup p q := (exists_join p q).choose
  le_sup_left p q := (exists_join p q).choose_spec.1
  le_sup_right p q := (exists_join p q).choose_spec.2.1
  sup_le p q r := (exists_join p q).choose_spec.2.2 r
  inf p q := (exists_meet p q).choose
  inf_le_left p q := (exists_meet p q).choose_spec.1
  inf_le_right p q := (exists_meet p q).choose_spec.2.1
  le_inf r p q := (exists_meet p q).choose_spec.2.2 r

theorem dominanceLattice_le_iff (p q : Nat.Partition n) :
    (dominanceLattice n).le p q ↔ Dominates p q :=
  Iff.rfl

/-- Conjugation turns joins of the dominance lattice into meets. -/
theorem conj_sup (p q : Nat.Partition n) :
    conj ((dominanceLattice n).sup p q) = (dominanceLattice n).inf (conj p) (conj q) := by
  have hj := (exists_join p q).choose_spec
  have hm := (exists_meet (conj p) (conj q)).choose_spec
  have h : IsMeet (conj p) (conj q) (conj (exists_join p q).choose) := by
    rw [isMeet_iff_isJoin_conj, conj_conj, conj_conj, conj_conj]
    exact hj
  exact dominates_antisymm (hm.2.2 _ h.1 h.2.1) (h.2.2 _ hm.1 hm.2.1)

/-- Conjugation turns meets of the dominance lattice into joins. -/
theorem conj_inf (p q : Nat.Partition n) :
    conj ((dominanceLattice n).inf p q) = (dominanceLattice n).sup (conj p) (conj q) := by
  have h := congrArg conj (conj_sup (conj p) (conj q))
  rw [conj_conj, conj_conj, conj_conj] at h
  exact h.symm

/-- For every `n`: dominance is a partial order on the partitions of `n`; any two partitions
have a meet and a join (so it is a lattice); and conjugation is an order-reversing involution
that exchanges meets and joins (the lattice is self-dual under conjugation). -/
def ConjectureHolds : Prop :=
  ∀ n : ℕ,
    (∀ p : Nat.Partition n, Dominates p p) ∧
    (∀ p q r : Nat.Partition n, Dominates p q → Dominates q r → Dominates p r) ∧
    (∀ p q : Nat.Partition n, Dominates p q → Dominates q p → p = q) ∧
    (∀ p q : Nat.Partition n, ∃ m, IsMeet p q m) ∧
    (∀ p q : Nat.Partition n, ∃ j, IsJoin p q j) ∧
    (∀ p : Nat.Partition n, conj (conj p) = p) ∧
    (∀ p q : Nat.Partition n, Dominates p q ↔ Dominates (conj q) (conj p)) ∧
    (∀ p q m : Nat.Partition n, IsMeet p q m ↔ IsJoin (conj p) (conj q) (conj m))

theorem conjecture_00000002486 : ConjectureHolds :=
  fun _ => ⟨dominates_refl, fun _ _ _ => dominates_trans, fun _ _ => dominates_antisymm,
    exists_meet, exists_join, conj_conj, dominates_iff_conj, isMeet_iff_isJoin_conj⟩

end Submission00000002486
