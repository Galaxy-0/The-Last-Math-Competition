import Mathlib

/-!
# Conjecture 00000001025 (disproof)

Conjecture: the only exception to "the automorphism group of the extended quadratic-residue code
is a semidirect product of `PSL(2,q)` with a commutative group" is `q = 7`.

We refute it at `q = 23` (binary extended QR code of length 24, the extended Golay code `W`):
`|Aut W| ≥ 24·23·22·21·20·16 = 81 607 680`, while a commutative group of permutations of 24
points has order at most `3^8 = 6561` and `|PSL(2,23)| ≤ |SL(2,23)| ≤ 12144`; since
`12144 · 6561 = 79 676 784 < 81 607 680`, `Aut W` is not `N ⋊ A` or `A ⋊ N` with `A` commutative
and `|N| ≤ 12144` (in particular `N = PSL(2, ZMod 23)` or `N = PSL(2, ZMod 2)`).
Every finite computation is checked by `decide +kernel` (kernel reduction only).
-/

open Equiv Matrix MatrixGroups

namespace C1025

/-- Binary words of length 24. Coordinate `i < 23` is the residue class `i mod 23`, and
coordinate `23` is the point `∞`. -/
abbrev V := Fin 24 → ZMod 2

instance (x : ZMod 23) : Decidable (IsSquare x) := decidable_of_iff (∃ r, x = r * r) Iff.rfl

/-- `S t = (t + N) ∪ {∞}`, where `N` is the set of quadratic non-residues mod 23
(the non-squares of `ZMod 23`; `0 = 0 * 0` is a square, so `N ⊆ (ZMod 23)ˣ`). -/
def S (t : ZMod 23) : V := fun i =>
  if (i : ℕ) = 23 then 1 else if IsSquare (((i : ℕ) : ZMod 23) - t) then 0 else 1

/-- The all-ones word. -/
def one24 : V := fun _ => 1

/-- The extended binary quadratic-residue code of length `24` (the extended binary Golay code):
the `𝔽₂`-span of the words `S t` and the all-ones word. -/
def W : Submodule (ZMod 2) V := Submodule.span (ZMod 2) (Set.range S ∪ {one24})

/-- The (permutation) automorphism group of a binary code `C` of length 24: the coordinate
permutations `σ` with `σ(C) = C`, i.e. `v ∈ C ↔ v ∘ σ ∈ C` for every word `v`. -/
def Aut (C : Submodule (ZMod 2) V) : Subgroup (Perm (Fin 24)) where
  carrier := {σ | ∀ v : V, v ∈ C ↔ v ∘ σ ∈ C}
  one_mem' := by intro v; simp
  mul_mem' := by
    intro σ τ hσ hτ v
    rw [hσ v, hτ (v ∘ σ)]
    rfl
  inv_mem' := by
    intro σ hσ v
    have h : (v ∘ ⇑σ⁻¹) ∘ ⇑σ = v := by funext i; simp
    rw [hσ (v ∘ ⇑σ⁻¹), h]

/-! ### A systematic basis of `W` (computational certificate) -/

/-- Bit `j` of `m`, as an element of `𝔽₂`. -/
def cbit (m j : ℕ) : ZMod 2 := if m.testBit j then 1 else 0

/-- The word whose support is the set of bits of `m`. -/
def bit (m : ℕ) : V := fun i => cbit m i

/-- A permutation of `Fin 24` given by its table and the table of its inverse. -/
def mkP (f g : Fin 24 → Fin 24) (h1 : ∀ i, g (f i) = i) (h2 : ∀ i, f (g i) = i) :
    Perm (Fin 24) := ⟨f, g, h1, h2⟩

/-- Systematic basis of `W` on the information set `{0,...,11}`, as 24-bit masks (bit `i` = coordinate `i`). -/
def bm : Fin 12 → ℕ := ![13062145, 4845570, 13938692, 7221256, 10170384, 11952160, 15515712, 2019456, 4038912, 8077824, 11654144, 14919680]
/-- `B k = ∑ t, c k t • S t + c' k • 1`: masks of the coefficients (bit `t` for `S t`, bit 23 for `1`). -/
def cm : Fin 12 → ℕ := ![3146, 3067, 1177, 1400, 1722, 3444, 1485, 2000, 4000, 101, 3200, 1573]
def g1 : Perm (Fin 24) := mkP ![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 0, 23]
  ![22, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 23] (by decide) (by decide)
def g3 : Perm (Fin 24) := mkP ![23, 22, 11, 15, 17, 9, 19, 13, 20, 5, 16, 2, 21, 7, 18, 3, 10, 4, 14, 6, 8, 12, 1, 0]
  ![23, 22, 11, 15, 17, 9, 19, 13, 20, 5, 16, 2, 21, 7, 18, 3, 10, 4, 14, 6, 8, 12, 1, 0] (by decide) (by decide)
def h2a : Perm (Fin 24) := mkP ![0, 1, 2, 18, 13, 12, 10, 20, 14, 6, 21, 17, 3, 4, 11, 7, 22, 8, 5, 15, 19, 9, 16, 23]
  ![0, 1, 2, 12, 13, 18, 9, 15, 17, 21, 6, 14, 5, 4, 8, 19, 22, 11, 3, 20, 7, 10, 16, 23] (by decide) (by decide)
def h2b : Perm (Fin 24) := mkP ![0, 21, 9, 17, 13, 7, 19, 18, 22, 3, 4, 10, 16, 5, 15, 8, 11, 14, 6, 12, 2, 20, 1, 23]
  ![0, 22, 20, 9, 10, 13, 18, 5, 15, 2, 11, 16, 19, 4, 17, 14, 12, 3, 7, 6, 21, 1, 8, 23] (by decide) (by decide)
def h3a : Perm (Fin 24) := mkP ![0, 1, 18, 7, 11, 9, 15, 13, 5, 14, 4, 22, 6, 8, 3, 21, 12, 16, 20, 17, 10, 19, 2, 23]
  ![0, 1, 22, 14, 10, 8, 12, 3, 13, 5, 20, 4, 16, 7, 9, 6, 17, 19, 2, 21, 18, 15, 11, 23] (by decide) (by decide)
def h3b : Perm (Fin 24) := mkP ![0, 1, 12, 2, 10, 8, 22, 3, 13, 17, 4, 20, 7, 16, 18, 6, 5, 11, 14, 15, 9, 21, 19, 23]
  ![0, 1, 3, 7, 10, 16, 15, 12, 5, 20, 4, 17, 2, 8, 18, 19, 13, 9, 14, 22, 11, 21, 6, 23] (by decide) (by decide)
def h4a : Perm (Fin 24) := mkP ![0, 1, 2, 13, 10, 4, 5, 14, 21, 12, 11, 6, 19, 9, 22, 18, 20, 16, 7, 3, 8, 17, 15, 23]
  ![0, 1, 2, 19, 5, 6, 11, 18, 20, 13, 4, 10, 9, 3, 7, 22, 17, 21, 15, 12, 16, 8, 14, 23] (by decide) (by decide)
def h4b : Perm (Fin 24) := mkP ![0, 1, 2, 14, 15, 3, 13, 22, 12, 19, 7, 11, 18, 20, 5, 21, 9, 17, 8, 16, 6, 4, 10, 23]
  ![0, 1, 2, 5, 21, 14, 20, 10, 18, 16, 22, 11, 8, 6, 3, 4, 19, 17, 12, 9, 13, 15, 7, 23] (by decide) (by decide)
def h5a : Perm (Fin 24) := mkP ![0, 1, 2, 3, 12, 14, 19, 7, 20, 16, 4, 15, 10, 11, 17, 13, 18, 5, 9, 21, 22, 6, 8, 23]
  ![0, 1, 2, 3, 10, 17, 21, 7, 22, 18, 12, 13, 4, 15, 5, 11, 9, 14, 16, 6, 8, 19, 20, 23] (by decide) (by decide)
def h5b : Perm (Fin 24) := mkP ![0, 1, 2, 3, 8, 5, 20, 15, 4, 21, 19, 13, 16, 11, 14, 7, 12, 17, 22, 10, 6, 9, 18, 23]
  ![0, 1, 2, 3, 8, 5, 20, 15, 4, 21, 19, 13, 16, 11, 14, 7, 12, 17, 22, 10, 6, 9, 18, 23] (by decide) (by decide)
def h5c : Perm (Fin 24) := mkP ![0, 1, 2, 3, 13, 17, 12, 18, 15, 7, 21, 10, 20, 22, 5, 19, 16, 14, 9, 8, 6, 11, 4, 23]
  ![0, 1, 2, 3, 22, 14, 20, 9, 19, 18, 11, 21, 6, 4, 17, 8, 16, 5, 7, 15, 12, 10, 13, 23] (by decide) (by decide)

/-- The systematic basis vectors. -/
def B (k : Fin 12) : V := bit (bm k)

/-- The combination of the basis vectors with the coefficients read off coordinates `0..11`. -/
def comb (v : V) : V := ∑ k : Fin 12, v (Fin.castLE (by omega) k) • B k

lemma comb_mem (v : V) : comb v ∈ Submodule.span (ZMod 2) (Set.range B) :=
  Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

lemma S_sys : ∀ t : ZMod 23, S t = comb (S t) := by decide +kernel

lemma one_sys : one24 = comb one24 := by decide +kernel

lemma B_eq : ∀ k : Fin 12, B k = ∑ t : ZMod 23, cbit (cm k) t.val • S t
    + cbit (cm k) 23 • one24 := by decide +kernel

/-- `W` is spanned by the systematic basis `B`. -/
lemma W_eq : W = Submodule.span (ZMod 2) (Set.range B) := by
  apply le_antisymm
  · rw [W, Submodule.span_le]
    rintro v (⟨t, rfl⟩ | h)
    · rw [SetLike.mem_coe, S_sys t]; exact comb_mem _
    · rw [Set.mem_singleton_iff.mp h, SetLike.mem_coe, one_sys]; exact comb_mem _
  · rw [Submodule.span_le]
    rintro v ⟨k, rfl⟩
    rw [SetLike.mem_coe, B_eq k]
    exact Submodule.add_mem _ (Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Or.inl ⟨t, rfl⟩)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr rfl)))

/-- A permutation that maps each basis vector into `W` is an automorphism of `W`. -/
lemma mem_aut (σ : Perm (Fin 24)) (h : ∀ k, B k ∘ σ = comb (B k ∘ σ)) : σ ∈ Aut W := by
  have hmap : ∀ v ∈ W, v ∘ σ ∈ W := by
    intro v hv
    rw [W_eq] at hv ⊢
    induction hv using Submodule.span_induction with
    | mem x hx => obtain ⟨k, rfl⟩ := hx; rw [h k]; exact comb_mem _
    | zero => exact Submodule.zero_mem _
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | smul a x _ hx => exact Submodule.smul_mem _ a hx
  intro v
  refine ⟨hmap v, fun hv => ?_⟩
  let f : W → W := fun w => ⟨w.1 ∘ σ, hmap _ w.2⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    have := congrArg (fun w : W => (w : V) ∘ ⇑σ⁻¹) hab
    simpa [f, Function.comp_def] using this
  obtain ⟨w, hw⟩ := (Finite.injective_iff_surjective.mp hf) ⟨v ∘ σ, hv⟩
  have h2 := congrArg (fun u : W => (u : V) ∘ ⇑σ⁻¹) hw
  have : (w : V) = v := by simpa [f, Function.comp_def] using h2

  exact this ▸ w.2

/-- The eleven explicit permutations are automorphisms of `W` (kernel computation). -/
theorem gens_mem : (∀ g ∈ [g1, g3], g ∈ Aut W) ∧ (∀ g ∈ [h2a, h2b], g ∈ Aut W) ∧
    (∀ g ∈ [h3a, h3b], g ∈ Aut W) ∧ (∀ g ∈ [h4a, h4b], g ∈ Aut W) ∧
    (∀ g ∈ [h5a, h5b, h5c], g ∈ Aut W) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_⟩ <;> exact mem_aut _ (by decide +kernel)

/-! ### Orbit-stabilizer counting -/

/-- The pointwise stabilizer of `a` in `K`. -/
abbrev stab (K : Subgroup (Perm (Fin 24))) (a : Fin 24) : Subgroup (Perm (Fin 24)) :=
  K ⊓ MulAction.stabilizer (Perm (Fin 24)) a

lemma card_le_of_orbit (K : Subgroup (Perm (Fin 24))) (a : Fin 24) (T : Finset (Fin 24))
    (hT : ∀ b ∈ T, ∃ g ∈ K, g a = b) : T.card * Nat.card (stab K a) ≤ Nat.card K := by
  classical
  choose! g hgK hga using hT
  let F : T × stab K a → K := fun p => ⟨g p.1 * p.2, K.mul_mem (hgK _ p.1.2)
    (Subgroup.mem_inf.mp p.2.2).1⟩
  have hF : Function.Injective F := by
    rintro ⟨⟨b, hb⟩, ⟨s, hs⟩⟩ ⟨⟨b', hb'⟩, ⟨s', hs'⟩⟩ h
    simp only [F, Subtype.mk.injEq] at h
    have hsa : s a = a := (Subgroup.mem_inf.mp hs).2
    have hsa' : s' a = a := (Subgroup.mem_inf.mp hs').2
    have hbb : b = b' := by
      have := congrArg (fun x : Perm (Fin 24) => x a) h
      simp only [Perm.mul_apply, hsa, hsa', hga _ hb, hga _ hb'] at this
      exact this
    subst hbb
    have : s = s' := mul_left_cancel h
    subst this; rfl
  have := Nat.card_le_card_of_injective F hF
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := T), Fintype.card_coe] at this

/-- The word `w = [j₁, ..., jₗ]` in the generators `gs` evaluates to `gs[j₁] * ... * gs[jₗ]`. -/
def evalW (gs : List (Perm (Fin 24))) (w : List ℕ) : Perm (Fin 24) := (w.map fun j => gs.getD j 1).prod

lemma evalW_mem (K : Subgroup (Perm (Fin 24))) (gs : List (Perm (Fin 24)))
    (hgs : ∀ g ∈ gs, g ∈ K) (w : List ℕ) : evalW gs w ∈ K := by
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
  rw [List.getD_eq_getElem?_getD]
  cases h : gs[j]? with
  | none => exact K.one_mem
  | some y => exact hgs y (List.mem_of_getElem? h)

/-- If the words `ws` move `a` to `m` distinct points, then `m * |K_a| ≤ |K|`. -/
lemma card_le_of_words (K : Subgroup (Perm (Fin 24))) (gs : List (Perm (Fin 24)))
    (hgs : ∀ g ∈ gs, g ∈ K) (a : Fin 24) (ws : List (List ℕ)) (m : ℕ)
    (hm : (Finset.univ.filter fun b => ws.any fun w => decide (evalW gs w a = b)).card = m) :
    m * Nat.card (stab K a) ≤ Nat.card K := by
  rw [← hm]
  refine card_le_of_orbit K a _ fun b hb => ?_
  obtain ⟨w, -, hw⟩ := List.any_eq_true.mp (Finset.mem_filter.mp hb).2
  exact ⟨evalW gs w, evalW_mem K gs hgs w, of_decide_eq_true hw⟩

/-! ### `|Aut W| ≥ 24·23·22·21·20·16` via the stabilizer chain of `∞, 0, 1, 2, 3` -/

/-- Words (in the level generators) reaching each orbit point, found by breadth-first search. -/
def ws0 : List (List ℕ) := [
  [1], [0,1], [0,0,1], [0,0,0,1], [0,0,0,0,1], [0,0,0,0,0,1], [0,0,0,0,0,0,1], [1,0,0,1,0,0,1],
  [0,1,0,0,1,0,0,1], [1,0,0,0,0,0,1], [1,0,1,0,0,0,1], [1,0,0,1], [0,1,0,0,1], [0,0,1,0,0,1],
  [0,0,0,1,0,0,1], [1,0,0,0,1], [0,1,0,0,0,1], [1,0,0,0,0,1], [0,1,0,0,0,0,1],
  [1,0,0,0,0,0,0,1], [0,1,0,0,0,0,0,0,1], [1,0,1,0,0,1], [1,0,1], []]
def ws1 : List (List ℕ) := (List.range 23).map fun k => List.replicate k 0
def ws2 : List (List ℕ) := [
  [], [1,1,1], [1,0,1], [1,0,0,0,1], [0,0,1,0,1], [0,0,1], [0,0,0,1,1], [0,1,1,0,1], [0,1],
  [0,0,0,1], [0,1,1,1,0,1], [1,0,1,1], [0,1,0,0,0,1], [1,1,1,0,1], [0,0,1,1], [1,1,0,1,1],
  [1,1,0,1], [0,1,0,1], [0,1,1], [1,1], [1], [1,0,1,1,0,1]]
def ws3 : List (List ℕ) := [
  [], [0,1,0], [0,0,0,0], [0,0,0,1,1], [0,1], [1,1], [0,0,1,1], [1,0,0], [0,0,0], [0,0,0,0,0],
  [1], [0,1,1], [1,0], [0,0,1], [1,0,1,1], [1,1,0,0], [0], [1,1,0,1], [0,0], [0,0,0,1],
  [1,0,1]]
def ws4 : List (List ℕ) := [
  [], [0,1,1], [1,1], [1,1,0], [1,1,0,1], [0,1,0], [0,0], [1,0,1], [0,1,0,1], [0,0,0], [0],
  [1], [0,0,1], [1,1,0,0], [0,0,0,1,0], [1,0,0,0], [1,0,0], [1,0], [0,0,1,0], [0,1]]
def ws5 : List (List ℕ) := [
  [], [1,2,0], [1,2,1], [1], [1,2,0,0], [0,0], [0,2], [0], [2], [2,1], [1,0], [0,1,0], [1,0,0],
  [2,0], [2,0,0], [2,2]]


/-- `Kb [aₖ, ..., a₁]`: the pointwise stabilizer of `a₁, ..., aₖ` in `Aut W`. -/
def Kb : List (Fin 24) → Subgroup (Perm (Fin 24))
  | [] => Aut W
  | a :: l => stab (Kb l) a

lemma mem_Kb (gs : List (Perm (Fin 24))) (l : List (Fin 24)) (hA : ∀ g ∈ gs, g ∈ Aut W)
    (hfix : (gs.all fun g => l.all fun a => g a == a) = true) : ∀ g ∈ gs, g ∈ Kb l := by
  intro g hg
  simp only [List.all_eq_true, beq_iff_eq] at hfix
  have h := hfix g hg
  clear hfix
  induction l with
  | nil => exact hA g hg
  | cons a l ih =>
    exact Subgroup.mem_inf.mpr ⟨ih fun b hb => h b (List.mem_cons_of_mem a hb), h a List.mem_cons_self⟩

set_option maxHeartbeats 2000000 in
/-- `|Aut W| ≥ 24 · 23 · 22 · 21 · 20 · 16`: stabilizer chain of `∞, 0, 1, 2, 3, 4`. -/
theorem card_aut_ge : 81607680 ≤ Nat.card (Aut W) := by
  have l0 := card_le_of_words (Kb []) [g1, g3] (mem_Kb _ [] gens_mem.1 (by decide +kernel)) 23
    ws0 24 (by decide +kernel)
  have l1 := card_le_of_words (Kb [23]) [g1] (mem_Kb _ [23] (fun g hg => gens_mem.1 g
    (List.mem_singleton.mp hg ▸ List.mem_cons_self)) (by decide +kernel)) 0 ws1 23 (by decide +kernel)
  have l2 := card_le_of_words (Kb [0, 23]) [h2a, h2b] (mem_Kb _ _ gens_mem.2.1 (by decide +kernel))
    1 ws2 22 (by decide +kernel)
  have l3 := card_le_of_words (Kb [1, 0, 23]) [h3a, h3b] 
    (mem_Kb _ _ gens_mem.2.2.1 (by decide +kernel)) 2 ws3 21 (by decide +kernel)
  have l4 := card_le_of_words (Kb [2, 1, 0, 23]) [h4a, h4b] 
    (mem_Kb _ _ gens_mem.2.2.2.1 (by decide +kernel)) 3 ws4 20 (by decide +kernel)
  have l5 := card_le_of_words (Kb [3, 2, 1, 0, 23]) [h5a, h5b, h5c]
    (mem_Kb _ _ gens_mem.2.2.2.2 (by decide +kernel)) 4 ws5 16 (by decide +kernel)
  have l6 : 1 ≤ Nat.card (stab (Kb [3, 2, 1, 0, 23]) 4) := Nat.card_pos
  change 24 * Nat.card (Kb [23]) ≤ _ at l0
  change 23 * Nat.card (Kb [0, 23]) ≤ _ at l1
  change 22 * Nat.card (Kb [1, 0, 23]) ≤ _ at l2
  change 21 * Nat.card (Kb [2, 1, 0, 23]) ≤ _ at l3
  change 20 * Nat.card (Kb [3, 2, 1, 0, 23]) ≤ _ at l4
  show 81607680 ≤ Nat.card (Kb [])
  omega

/-! ### Commutative permutation groups on 24 points have order `≤ 3^8` -/

lemma cube_le (k : ℕ) : k ^ 3 ≤ 3 ^ k := by
  induction k with
  | zero => simp
  | succ n ih =>
    rcases (show n ≤ 2 ∨ 3 ≤ n by omega) with h | h
    · interval_cases n <;> norm_num
    · have : (n + 1) ^ 3 ≤ 3 * n ^ 3 := by nlinarith [Nat.mul_le_mul h h]
      calc (n + 1) ^ 3 ≤ 3 * n ^ 3 := this
        _ ≤ 3 * 3 ^ n := by omega
        _ = 3 ^ (n + 1) := by ring

theorem abelian_bound : ∀ (n : ℕ) (T : Finset (Fin 24)) (A : Subgroup (Perm (Fin 24))),
    T.card = n → (∀ g ∈ A, ∀ h ∈ A, g * h = h * g) → (∀ g ∈ A, ∀ x ∉ T, g x = x) →
    Nat.card A ^ 3 ≤ 3 ^ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro T A hT hcomm hfix
  classical
  rcases T.eq_empty_or_nonempty with h0 | ⟨x, hx⟩
  · have hA : A = ⊥ := by
      rw [eq_bot_iff]; intro g hg; rw [Subgroup.mem_bot]
      ext y; simp [hfix g hg y (by simp [h0])]
    rw [hA, Subgroup.card_bot, one_pow]; exact Nat.one_le_pow _ _ (by norm_num)
  · set O := Finset.univ.filter (fun y => ∃ g ∈ A, g x = y) with hO
    have hOT : O ⊆ T := by
      intro y hy
      obtain ⟨g, hg, rfl⟩ := (Finset.mem_filter.mp hy).2
      by_contra hy'
      have h1 := hfix g hg _ hy'
      rw [g.injective h1] at hy'
      exact hy' hx
    have hxO : x ∈ O := Finset.mem_filter.mpr ⟨Finset.mem_univ _, 1, A.one_mem, rfl⟩
    have hcard : (T \ O).card + O.card = T.card := Finset.card_sdiff_add_card_eq_card hOT
    have hpos : 0 < O.card := Finset.card_pos.mpr ⟨x, hxO⟩
    have hS := ih (T \ O).card (by omega) (T \ O) (stab A x) rfl
      (fun g hg h hh => hcomm g (Subgroup.mem_inf.mp hg).1 h (Subgroup.mem_inf.mp hh).1)
      (by
        intro s hs y hy
        have hsA := (Subgroup.mem_inf.mp hs).1
        have hsx : s x = x := (Subgroup.mem_inf.mp hs).2
        by_cases hyT : y ∈ T
        · have hyO : y ∈ O := by
            by_contra h; exact hy (Finset.mem_sdiff.mpr ⟨hyT, h⟩)
          obtain ⟨g, hg, rfl⟩ := (Finset.mem_filter.mp hyO).2
          have := congrArg (fun p : Perm (Fin 24) => p x) (hcomm s hsA g hg)
          simp only [Perm.mul_apply, hsx] at this
          exact this
        · exact hfix s hsA y hyT)
    have hAO : Nat.card A ≤ O.card * Nat.card (stab A x) := by
      have hrep : ∀ y ∈ O, ∃ g ∈ A, g x = y := fun y hy => (Finset.mem_filter.mp hy).2
      choose! r hrA hrx using hrep
      have hmem : ∀ h : A, (h : Perm (Fin 24)) x ∈ O := fun h =>
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.1, h.2, rfl⟩
      let F : A → O × stab A x := fun h => (⟨h.1 x, hmem h⟩,
        ⟨(r (h.1 x))⁻¹ * h.1, Subgroup.mem_inf.mpr ⟨A.mul_mem (A.inv_mem (hrA _ (hmem h))) h.2,
          by rw [MulAction.mem_stabilizer_iff, Perm.smul_def, Perm.mul_apply,
            Perm.inv_eq_iff_eq, hrx _ (hmem h)]⟩⟩)
      have hF : Function.Injective F := by
        intro h h' e
        simp only [F, Prod.mk.injEq, Subtype.mk.injEq] at e
        obtain ⟨e1, e2⟩ := e
        rw [e1] at e2
        exact Subtype.ext (mul_left_cancel e2)
      have := Nat.card_le_card_of_injective F hF
      rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := O), Fintype.card_coe] at this
    calc Nat.card A ^ 3 ≤ (O.card * Nat.card (stab A x)) ^ 3 := Nat.pow_le_pow_left hAO 3
      _ = O.card ^ 3 * Nat.card (stab A x) ^ 3 := mul_pow _ _ _
      _ ≤ 3 ^ O.card * 3 ^ (T \ O).card := Nat.mul_le_mul (cube_le _) hS
      _ = 3 ^ n := by rw [← pow_add]; congr 1; omega

/-- A commutative subgroup of `Perm (Fin 24)` has order at most `3^8 = 6561`. -/
theorem card_comm_le (A : Subgroup (Perm (Fin 24))) (hcomm : ∀ g ∈ A, ∀ h ∈ A, g * h = h * g) :
    Nat.card A ≤ 6561 := by
  have h := abelian_bound 24 Finset.univ A (by simp) hcomm (by simp)
  have : Nat.card A ^ 3 ≤ 6561 ^ 3 := by norm_num at h ⊢; exact h
  exact (Nat.pow_le_pow_iff_left (by norm_num)).mp this

/-- An injective homomorphism from a commutative group into `Aut W` has image of order `≤ 6561`. -/
lemma card_le_of_inj {A : Type*} [CommGroup A] (f : A →* Aut W) (hf : Function.Injective f) :
    Nat.card A ≤ 6561 := by
  let f' : A →* Perm (Fin 24) := (Aut W).subtype.comp f
  have hf' : Function.Injective f' := Subtype.val_injective.comp hf
  rw [Nat.card_congr (MonoidHom.ofInjective hf').toEquiv]
  apply card_comm_le
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  rw [← map_mul, ← map_mul, mul_comm]

/-! ### `|PSL(2,23)| ≤ |SL(2,23)| ≤ 12144` -/

instance : Fact (Nat.Prime 23) := ⟨by norm_num⟩

lemma card_SL_le : Nat.card (SL(2, ZMod 23)) ≤ 12144 := by
  have hGL : Nat.card (GL (Fin 2) (ZMod 23)) = 267168 := by
    rw [Matrix.card_GL_field, ZMod.card, Fin.prod_univ_two]; norm_num
  have hU : Nat.card (ZMod 23)ˣ = 22 := by rw [Nat.card_eq_fintype_card, ZMod.card_units]
  let D : (ZMod 23)ˣ → Matrix (Fin 2) (Fin 2) (ZMod 23) := fun u => diagonal ![(u : ZMod 23), 1]
  have hD : ∀ u, (D u).det = u := fun u => by simp [D, det_diagonal, Fin.prod_univ_two]
  let F : SL(2, ZMod 23) × (ZMod 23)ˣ → GL (Fin 2) (ZMod 23) := fun p =>
    GeneralLinearGroup.mkOfDetNeZero (D p.2 * p.1) (by
      rw [det_mul, hD, p.1.2, mul_one]; exact p.2.ne_zero)
  have hF : Function.Injective F := by
    rintro ⟨A, u⟩ ⟨A', u'⟩ h
    have hm : D u * A.1 = D u' * A'.1 := by
      have := congrArg (fun g : GL (Fin 2) (ZMod 23) => (g : Matrix (Fin 2) (Fin 2) (ZMod 23))) h
      simpa [F] using this
    have hu : u = u' := by
      have := congrArg det hm
      rw [det_mul, det_mul, hD, hD, A.2, A'.2, mul_one, mul_one] at this
      exact Units.ext this
    subst hu
    refine Prod.ext (Subtype.ext ?_) rfl
    ext i j
    have := congrFun (congrFun hm i) j
    simp only [D, diagonal_mul] at this
    exact mul_left_cancel₀ (by fin_cases i <;> simp [u.ne_zero]) this
  have := Nat.card_le_card_of_injective F hF
  rw [Nat.card_prod, hU, hGL] at this
  omega

lemma card_PSL_le : Nat.card (PSL(2, ZMod 23)) ≤ 12144 :=
  (Nat.card_le_card_of_surjective _ (QuotientGroup.mk_surjective)).trans card_SL_le

lemma card_PSL2_le : Nat.card (PSL(2, ZMod 2)) ≤ 12144 := by
  refine (Nat.card_le_card_of_surjective _ (QuotientGroup.mk_surjective)).trans ?_
  refine (Nat.card_le_card_of_injective (fun A : SL(2, ZMod 2) => (A : Matrix (Fin 2) (Fin 2)
    (ZMod 2))) Subtype.val_injective).trans ?_
  calc Nat.card (Matrix (Fin 2) (Fin 2) (ZMod 2)) = Nat.card (Fin 2 → Fin 2 → ZMod 2) := rfl
    _ ≤ 12144 := by rw [Nat.card_fun, Nat.card_fun]; simp

/-! ### Main results -/

/-- `Aut W` is not a semidirect product `N ⋊ A` (normal `N`) with `|N| ≤ 12144`, `A` commutative. -/
theorem not_semidirect_left {N A : Type*} [Group N] [CommGroup A] (φ : A →* MulAut N)
    (hN : Nat.card N ≤ 12144) : IsEmpty (Aut W ≃* N ⋊[φ] A) := by
  refine ⟨fun e => ?_⟩
  have hc : Nat.card (Aut W) = Nat.card N * Nat.card A := by
    rw [Nat.card_congr e.toEquiv, SemidirectProduct.card]
  have hA := card_le_of_inj (e.symm.toMonoidHom.comp SemidirectProduct.inr)
    (e.symm.injective.comp SemidirectProduct.inr_injective)
  have := card_aut_ge
  have := Nat.mul_le_mul hN hA
  omega

/-- `Aut W` is not a semidirect product `A ⋊ N` (normal commutative `A`) with `|N| ≤ 12144`. -/
theorem not_semidirect_right {N A : Type*} [Group N] [CommGroup A] (φ : N →* MulAut A)
    (hN : Nat.card N ≤ 12144) : IsEmpty (Aut W ≃* A ⋊[φ] N) := by
  refine ⟨fun e => ?_⟩
  have hc : Nat.card (Aut W) = Nat.card A * Nat.card N := by
    rw [Nat.card_congr e.toEquiv, SemidirectProduct.card]
  have hA := card_le_of_inj (e.symm.toMonoidHom.comp SemidirectProduct.inl)
    (e.symm.injective.comp SemidirectProduct.inl_injective)
  have := card_aut_ge
  have := Nat.mul_le_mul hN hA
  rw [mul_comm] at hc
  omega

/-- **Disproof of conjecture 00000001025.** For `q = 23` the automorphism group of the extended
binary quadratic-residue code `W` of length 24 is not a semidirect product (in either order)
of `PSL(2, 23)` with a commutative group; the same holds with `PSL(2, 2)` (the `q = 2` alphabet
reading). So `q = 7` is not the only exception. -/
theorem conjecture_1025_false :
    (∀ (A : Type) [CommGroup A] (φ : A →* MulAut (PSL(2, ZMod 23))),
      IsEmpty (Aut W ≃* PSL(2, ZMod 23) ⋊[φ] A)) ∧
    (∀ (A : Type) [CommGroup A] (φ : PSL(2, ZMod 23) →* MulAut A),
      IsEmpty (Aut W ≃* A ⋊[φ] PSL(2, ZMod 23))) ∧
    (∀ (A : Type) [CommGroup A] (φ : A →* MulAut (PSL(2, ZMod 2))),
      IsEmpty (Aut W ≃* PSL(2, ZMod 2) ⋊[φ] A)) ∧
    (∀ (A : Type) [CommGroup A] (φ : PSL(2, ZMod 2) →* MulAut A),
      IsEmpty (Aut W ≃* A ⋊[φ] PSL(2, ZMod 2))) :=
  ⟨fun _ _ φ => not_semidirect_left φ card_PSL_le, fun _ _ φ => not_semidirect_right φ card_PSL_le,
   fun _ _ φ => not_semidirect_left φ card_PSL2_le, fun _ _ φ => not_semidirect_right φ card_PSL2_le⟩

end C1025
