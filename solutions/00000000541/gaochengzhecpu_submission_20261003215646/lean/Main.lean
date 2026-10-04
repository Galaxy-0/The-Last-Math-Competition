import Std
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

namespace Conjecture541
instance finiteExists {n : Nat} (P : Fin n → Prop) [DecidablePred P] :
    Decidable (∃ x, P x) :=
  decidable_of_iff (¬ ∀ x, ¬ P x) (by
    classical
    constructor
    · intro h
      apply Classical.byContradiction
      intro hn
      exact h (fun x hx => hn ⟨x,hx⟩)
    · rintro ⟨x,hx⟩ hn
      exact hn x hx)
abbrev V := Fin 12
abbrev Mask := Fin 4096
abbrev Graph := V → V → Bool
def member (s : Mask) (x : V) : Bool := (s.val / 2^x.val) % 2 == 1
def cardinality (s : Mask) : Nat := ((List.finRange 12).filter (member s)).length
def Edge (G : Graph) (x y : V) : Prop := G x y = true
instance (G : Graph) (x y : V) : Decidable (Edge G x y) := by
  unfold Edge; infer_instance
def GraphLaws (G : Graph) : Prop :=
  (∀ x, G x x = false) ∧ ∀ x y, G x y = G y x
def Included (S T : V → Prop) : Prop := ∀ x, S x → T x
def Independent (G : Graph) (S : V → Prop) : Prop :=
  ∀ x y, S x → S y → ¬Edge G x y
def MaximalIndependent (G : Graph) (S : V → Prop) : Prop :=
  Independent G S ∧ ∀ T : V → Prop, Independent G T → Included S T → Included T S
def IsFacet (G : Graph) (s : Mask) : Prop :=
  Independent G (fun x => member s x = true) ∧
  ∀ v, member s v = false → ∃ u, member s u = true ∧ Edge G u v
instance (G : Graph) (s : Mask) : Decidable (IsFacet G s) := by
  unfold IsFacet Independent Edge; infer_instance

theorem facet_iff_maximal (G : Graph) (laws : GraphLaws G) (s : Mask) :
    IsFacet G s ↔ MaximalIndependent G (fun x => member s x = true) := by
  classical
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro T hT hST v hv
    cases he : member s v with
    | true => rfl
    | false =>
      obtain ⟨u,hu,huv⟩ := h.2 v he
      exact False.elim (hT u v (hST u hu) hv huv)
  · intro h
    refine ⟨h.1, ?_⟩
    intro v hv
    apply Classical.byContradiction
    intro hn
    have hnone : ∀ u, member s u = true → ¬Edge G u v := by
      intro u hu huv
      exact hn ⟨u,hu,huv⟩
    let T : V → Prop := fun x => member s x = true ∨ x = v
    have hT : Independent G T := by
      intro x y hx hy hxy
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · exact h.1 x y hx hy hxy
      · rw [hy] at hxy
        exact hnone x hx hxy
      · apply hnone y hy
        rw [hx] at hxy
        unfold Edge at *
        rw [laws.2 y v]
        exact hxy
      · have hir := laws.1 v
        rw [hx,hy] at hxy
        unfold Edge at hxy
        simp [hir] at hxy
    have hST : Included (fun x => member s x = true) T := by
      intro x hx; exact Or.inl hx
    have contra := h.2 T hT hST v (Or.inr rfl)
    simp [hv] at contra

def whiskeredCycle : Graph := fun x y => decide (
  (x.val < 6 ∧ y.val < 6 ∧
    ((x.val+1)%6=y.val ∨ (y.val+1)%6=x.val)) ∨
  (x.val < 6 ∧ y.val=x.val+6) ∨
  (y.val < 6 ∧ x.val=y.val+6))
theorem graph_laws : GraphLaws whiskeredCycle := by
  unfold GraphLaws; decide
def twoColor (x : V) : Bool :=
  if x.val < 6 then x.val % 2 == 0 else x.val % 2 == 1
def Bipartite (G : Graph) : Prop :=
  ∃ c : V → Bool, ∀ x y, Edge G x y → c x ≠ c y
theorem graph_bipartite : Bipartite whiskeredCycle := by
  refine ⟨twoColor, ?_⟩
  decide

def cycleEmbedding (i : Fin 6) : V := ⟨i.val, by omega⟩
def InducedCycle (G : Graph) (k : Nat) (f : Fin k → V) : Prop :=
  (∀ i j, f i = f j → i = j) ∧
  ∀ i j, G (f i) (f j) = decide ((i.val+1)%k=j.val ∨ (j.val+1)%k=i.val)
theorem induced_six_cycle : InducedCycle whiskeredCycle 6 cycleEmbedding := by
  unfold InducedCycle; decide
def Chordal (G : Graph) : Prop :=
  ∀ k, 4 ≤ k → ∀ f : Fin k → V, ¬InducedCycle G k f
def ChordalBipartite (G : Graph) : Prop :=
  Bipartite G ∧ ∀ k, 5 ≤ k → ∀ f : Fin k → V, ¬InducedCycle G k f
theorem not_chordal : ¬Chordal whiskeredCycle := by
  intro h; exact h 6 (by decide) cycleEmbedding induced_six_cycle
theorem not_chordal_bipartite : ¬ChordalBipartite whiskeredCycle := by
  intro h; exact h.2 6 (by decide) cycleEmbedding induced_six_cycle

def encodeBits (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 : Bool) : Mask :=
  ⟨((if b0 then 1 else 0) + (if b1 then 2 else 0) + (if b2 then 4 else 0) + (if b3 then 8 else 0) + (if b4 then 16 else 0) + (if b5 then 32 else 0) + (if b6 then 64 else 0) + (if b7 then 128 else 0) + (if b8 then 256 else 0) + (if b9 then 512 else 0) + (if b10 then 1024 else 0) + (if b11 then 2048 else 0)) % 4096, Nat.mod_lt _ (by decide)⟩
def bitTable (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 : Bool) (x : V) : Bool :=
  match x.val with
  | 0 => b0
  | 1 => b1
  | 2 => b2
  | 3 => b3
  | 4 => b4
  | 5 => b5
  | 6 => b6
  | 7 => b7
  | 8 => b8
  | 9 => b9
  | 10 => b10
  | _ => b11
theorem encodeBits_correct : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 : Bool, ∀ x : V,
    member (encodeBits b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11) x = bitTable b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 x := by decide
def encode (p : V → Bool) : Mask := encodeBits (p 0) (p 1) (p 2) (p 3) (p 4) (p 5) (p 6) (p 7) (p 8) (p 9) (p 10) (p 11)
theorem every_subset_encoded (p : V → Bool) : member (encode p) = p := by
  funext x
  unfold encode
  rw [encodeBits_correct]
  have all : ∀ x : V, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 ∨ x = 7 ∨ x = 8 ∨ x = 9 ∨ x = 10 ∨ x = 11 := by decide
  rcases all x with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
theorem every_prop_subset_encoded (p : V → Prop) :
    ∃ s : Mask, ∀ x, member s x = true ↔ p x := by
  classical
  refine ⟨encode (fun x => decide (p x)), ?_⟩
  intro x
  rw [every_subset_encoded]
  simp

def facets : Fin 18 → Mask := fun j =>
  match j.val with
  | 0 => 4032
  | 1 => 3969
  | 2 => 3906
  | 3 => 3780
  | 4 => 3528
  | 5 => 3024
  | 6 => 2016
  | 7 => 3717
  | 8 => 3465
  | 9 => 3402
  | 10 => 2961
  | 11 => 2898
  | 12 => 2772
  | 13 => 1890
  | 14 => 1764
  | 15 => 1512
  | 16 => 2709
  | _ => 1386


def blockMask (b r : Fin 64) : Mask := ⟨b.val * 64 + r.val, by omega⟩
theorem facet_block_0 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 0 r) ↔
    ∃ j : Fin 18, blockMask 0 r = facets j := by decide
theorem facet_block_1 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 1 r) ↔
    ∃ j : Fin 18, blockMask 1 r = facets j := by decide
theorem facet_block_2 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 2 r) ↔
    ∃ j : Fin 18, blockMask 2 r = facets j := by decide
theorem facet_block_3 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 3 r) ↔
    ∃ j : Fin 18, blockMask 3 r = facets j := by decide
theorem facet_block_4 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 4 r) ↔
    ∃ j : Fin 18, blockMask 4 r = facets j := by decide
theorem facet_block_5 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 5 r) ↔
    ∃ j : Fin 18, blockMask 5 r = facets j := by decide
theorem facet_block_6 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 6 r) ↔
    ∃ j : Fin 18, blockMask 6 r = facets j := by decide
theorem facet_block_7 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 7 r) ↔
    ∃ j : Fin 18, blockMask 7 r = facets j := by decide
theorem facet_block_8 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 8 r) ↔
    ∃ j : Fin 18, blockMask 8 r = facets j := by decide
theorem facet_block_9 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 9 r) ↔
    ∃ j : Fin 18, blockMask 9 r = facets j := by decide
theorem facet_block_10 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 10 r) ↔
    ∃ j : Fin 18, blockMask 10 r = facets j := by decide
theorem facet_block_11 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 11 r) ↔
    ∃ j : Fin 18, blockMask 11 r = facets j := by decide
theorem facet_block_12 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 12 r) ↔
    ∃ j : Fin 18, blockMask 12 r = facets j := by decide
theorem facet_block_13 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 13 r) ↔
    ∃ j : Fin 18, blockMask 13 r = facets j := by decide
theorem facet_block_14 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 14 r) ↔
    ∃ j : Fin 18, blockMask 14 r = facets j := by decide
theorem facet_block_15 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 15 r) ↔
    ∃ j : Fin 18, blockMask 15 r = facets j := by decide
theorem facet_block_16 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 16 r) ↔
    ∃ j : Fin 18, blockMask 16 r = facets j := by decide
theorem facet_block_17 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 17 r) ↔
    ∃ j : Fin 18, blockMask 17 r = facets j := by decide
theorem facet_block_18 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 18 r) ↔
    ∃ j : Fin 18, blockMask 18 r = facets j := by decide
theorem facet_block_19 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 19 r) ↔
    ∃ j : Fin 18, blockMask 19 r = facets j := by decide
theorem facet_block_20 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 20 r) ↔
    ∃ j : Fin 18, blockMask 20 r = facets j := by decide
theorem facet_block_21 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 21 r) ↔
    ∃ j : Fin 18, blockMask 21 r = facets j := by decide
theorem facet_block_22 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 22 r) ↔
    ∃ j : Fin 18, blockMask 22 r = facets j := by decide
theorem facet_block_23 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 23 r) ↔
    ∃ j : Fin 18, blockMask 23 r = facets j := by decide
theorem facet_block_24 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 24 r) ↔
    ∃ j : Fin 18, blockMask 24 r = facets j := by decide
theorem facet_block_25 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 25 r) ↔
    ∃ j : Fin 18, blockMask 25 r = facets j := by decide
theorem facet_block_26 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 26 r) ↔
    ∃ j : Fin 18, blockMask 26 r = facets j := by decide
theorem facet_block_27 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 27 r) ↔
    ∃ j : Fin 18, blockMask 27 r = facets j := by decide
theorem facet_block_28 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 28 r) ↔
    ∃ j : Fin 18, blockMask 28 r = facets j := by decide
theorem facet_block_29 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 29 r) ↔
    ∃ j : Fin 18, blockMask 29 r = facets j := by decide
theorem facet_block_30 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 30 r) ↔
    ∃ j : Fin 18, blockMask 30 r = facets j := by decide
theorem facet_block_31 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 31 r) ↔
    ∃ j : Fin 18, blockMask 31 r = facets j := by decide
theorem facet_block_32 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 32 r) ↔
    ∃ j : Fin 18, blockMask 32 r = facets j := by decide
theorem facet_block_33 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 33 r) ↔
    ∃ j : Fin 18, blockMask 33 r = facets j := by decide
theorem facet_block_34 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 34 r) ↔
    ∃ j : Fin 18, blockMask 34 r = facets j := by decide
theorem facet_block_35 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 35 r) ↔
    ∃ j : Fin 18, blockMask 35 r = facets j := by decide
theorem facet_block_36 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 36 r) ↔
    ∃ j : Fin 18, blockMask 36 r = facets j := by decide
theorem facet_block_37 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 37 r) ↔
    ∃ j : Fin 18, blockMask 37 r = facets j := by decide
theorem facet_block_38 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 38 r) ↔
    ∃ j : Fin 18, blockMask 38 r = facets j := by decide
theorem facet_block_39 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 39 r) ↔
    ∃ j : Fin 18, blockMask 39 r = facets j := by decide
theorem facet_block_40 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 40 r) ↔
    ∃ j : Fin 18, blockMask 40 r = facets j := by decide
theorem facet_block_41 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 41 r) ↔
    ∃ j : Fin 18, blockMask 41 r = facets j := by decide
theorem facet_block_42 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 42 r) ↔
    ∃ j : Fin 18, blockMask 42 r = facets j := by decide
theorem facet_block_43 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 43 r) ↔
    ∃ j : Fin 18, blockMask 43 r = facets j := by decide
theorem facet_block_44 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 44 r) ↔
    ∃ j : Fin 18, blockMask 44 r = facets j := by decide
theorem facet_block_45 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 45 r) ↔
    ∃ j : Fin 18, blockMask 45 r = facets j := by decide
theorem facet_block_46 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 46 r) ↔
    ∃ j : Fin 18, blockMask 46 r = facets j := by decide
theorem facet_block_47 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 47 r) ↔
    ∃ j : Fin 18, blockMask 47 r = facets j := by decide
theorem facet_block_48 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 48 r) ↔
    ∃ j : Fin 18, blockMask 48 r = facets j := by decide
theorem facet_block_49 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 49 r) ↔
    ∃ j : Fin 18, blockMask 49 r = facets j := by decide
theorem facet_block_50 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 50 r) ↔
    ∃ j : Fin 18, blockMask 50 r = facets j := by decide
theorem facet_block_51 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 51 r) ↔
    ∃ j : Fin 18, blockMask 51 r = facets j := by decide
theorem facet_block_52 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 52 r) ↔
    ∃ j : Fin 18, blockMask 52 r = facets j := by decide
theorem facet_block_53 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 53 r) ↔
    ∃ j : Fin 18, blockMask 53 r = facets j := by decide
theorem facet_block_54 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 54 r) ↔
    ∃ j : Fin 18, blockMask 54 r = facets j := by decide
theorem facet_block_55 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 55 r) ↔
    ∃ j : Fin 18, blockMask 55 r = facets j := by decide
theorem facet_block_56 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 56 r) ↔
    ∃ j : Fin 18, blockMask 56 r = facets j := by decide
theorem facet_block_57 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 57 r) ↔
    ∃ j : Fin 18, blockMask 57 r = facets j := by decide
theorem facet_block_58 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 58 r) ↔
    ∃ j : Fin 18, blockMask 58 r = facets j := by decide
theorem facet_block_59 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 59 r) ↔
    ∃ j : Fin 18, blockMask 59 r = facets j := by decide
theorem facet_block_60 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 60 r) ↔
    ∃ j : Fin 18, blockMask 60 r = facets j := by decide
theorem facet_block_61 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 61 r) ↔
    ∃ j : Fin 18, blockMask 61 r = facets j := by decide
theorem facet_block_62 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 62 r) ↔
    ∃ j : Fin 18, blockMask 62 r = facets j := by decide
theorem facet_block_63 : ∀ r : Fin 64,
    IsFacet whiskeredCycle (blockMask 63 r) ↔
    ∃ j : Fin 18, blockMask 63 r = facets j := by decide
theorem all_facet_blocks (b r : Fin 64) :
    IsFacet whiskeredCycle (blockMask b r) ↔
    ∃ j : Fin 18, blockMask b r = facets j := by
  have cases64 : ∀ b : Fin 64, b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6 ∨ b = 7 ∨ b = 8 ∨ b = 9 ∨ b = 10 ∨ b = 11 ∨ b = 12 ∨ b = 13 ∨ b = 14 ∨ b = 15 ∨ b = 16 ∨ b = 17 ∨ b = 18 ∨ b = 19 ∨ b = 20 ∨ b = 21 ∨ b = 22 ∨ b = 23 ∨ b = 24 ∨ b = 25 ∨ b = 26 ∨ b = 27 ∨ b = 28 ∨ b = 29 ∨ b = 30 ∨ b = 31 ∨ b = 32 ∨ b = 33 ∨ b = 34 ∨ b = 35 ∨ b = 36 ∨ b = 37 ∨ b = 38 ∨ b = 39 ∨ b = 40 ∨ b = 41 ∨ b = 42 ∨ b = 43 ∨ b = 44 ∨ b = 45 ∨ b = 46 ∨ b = 47 ∨ b = 48 ∨ b = 49 ∨ b = 50 ∨ b = 51 ∨ b = 52 ∨ b = 53 ∨ b = 54 ∨ b = 55 ∨ b = 56 ∨ b = 57 ∨ b = 58 ∨ b = 59 ∨ b = 60 ∨ b = 61 ∨ b = 62 ∨ b = 63 := by decide
  rcases cases64 b with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact facet_block_0 r
  · exact facet_block_1 r
  · exact facet_block_2 r
  · exact facet_block_3 r
  · exact facet_block_4 r
  · exact facet_block_5 r
  · exact facet_block_6 r
  · exact facet_block_7 r
  · exact facet_block_8 r
  · exact facet_block_9 r
  · exact facet_block_10 r
  · exact facet_block_11 r
  · exact facet_block_12 r
  · exact facet_block_13 r
  · exact facet_block_14 r
  · exact facet_block_15 r
  · exact facet_block_16 r
  · exact facet_block_17 r
  · exact facet_block_18 r
  · exact facet_block_19 r
  · exact facet_block_20 r
  · exact facet_block_21 r
  · exact facet_block_22 r
  · exact facet_block_23 r
  · exact facet_block_24 r
  · exact facet_block_25 r
  · exact facet_block_26 r
  · exact facet_block_27 r
  · exact facet_block_28 r
  · exact facet_block_29 r
  · exact facet_block_30 r
  · exact facet_block_31 r
  · exact facet_block_32 r
  · exact facet_block_33 r
  · exact facet_block_34 r
  · exact facet_block_35 r
  · exact facet_block_36 r
  · exact facet_block_37 r
  · exact facet_block_38 r
  · exact facet_block_39 r
  · exact facet_block_40 r
  · exact facet_block_41 r
  · exact facet_block_42 r
  · exact facet_block_43 r
  · exact facet_block_44 r
  · exact facet_block_45 r
  · exact facet_block_46 r
  · exact facet_block_47 r
  · exact facet_block_48 r
  · exact facet_block_49 r
  · exact facet_block_50 r
  · exact facet_block_51 r
  · exact facet_block_52 r
  · exact facet_block_53 r
  · exact facet_block_54 r
  · exact facet_block_55 r
  · exact facet_block_56 r
  · exact facet_block_57 r
  · exact facet_block_58 r
  · exact facet_block_59 r
  · exact facet_block_60 r
  · exact facet_block_61 r
  · exact facet_block_62 r
  · exact facet_block_63 r

theorem all_facets : ∀ s : Mask,
    IsFacet whiskeredCycle s ↔ ∃ j : Fin 18, s = facets j := by
  intro s
  let b : Fin 64 := ⟨s.val / 64, by omega⟩
  let r : Fin 64 := ⟨s.val % 64, by omega⟩
  have he : blockMask b r = s := by
    apply Fin.ext
    simp only [blockMask,b,r]
    omega
  rw [←he]
  exact all_facet_blocks b r

theorem distinct_facets : ∀ i j : Fin 18, facets i = facets j → i = j := by decide
theorem facets_cardinality : ∀ j : Fin 18, cardinality (facets j) = 6 := by decide

/-- Standard facet-difference shelling criterion, with completeness of facets. -/
def IsShelling (G : Graph) {n : Nat} (F : Fin n → Mask) : Prop :=
  (∀ s, IsFacet G s ↔ ∃ j, s = F j) ∧
  (∀ i j, F i = F j → i = j) ∧
  ∀ i j, i < j → ∃ l, l < j ∧ ∃ v,
    member (F j) v = true ∧ member (F i) v = false ∧
    ∀ w, (member (F j) w = true ∧ member (F l) w = false) ↔ w = v
def Shellable (G : Graph) : Prop := ∃ n, ∃ F : Fin n → Mask, IsShelling G F
theorem shelling_certificate :
    ∀ i j : Fin 18, i < j → ∃ l : Fin 18, l < j ∧ ∃ v : V,
    member (facets j) v = true ∧ member (facets i) v = false ∧
    ∀ w : V, (member (facets j) w = true ∧ member (facets l) w = false) ↔ w = v := by
  decide
theorem independence_complex_shellable : Shellable whiskeredCycle := by
  exact ⟨18, facets, all_facets, distinct_facets, shelling_certificate⟩

/-- Every genuine proposition-valued maximal independent set occurs. -/
theorem every_maximal_independent_set (S : V → Prop)
    (h : MaximalIndependent whiskeredCycle S) :
    ∃ j : Fin 18, ∀ x, S x ↔ member (facets j) x = true := by
  classical
  obtain ⟨s,hs⟩ := every_prop_subset_encoded S
  have heq : (fun x => member s x = true) = S := by
    funext x; exact propext (hs x)
  have hm : MaximalIndependent whiskeredCycle (fun x => member s x = true) := by
    rw [heq]; exact h
  have hf := (facet_iff_maximal whiskeredCycle graph_laws s).mpr hm
  obtain ⟨j,rfl⟩ := (all_facets s).mp hf
  exact ⟨j,fun x => (hs x).symm⟩

theorem conjecture541_counterexample :
    GraphLaws whiskeredCycle ∧ Bipartite whiskeredCycle ∧
    Shellable whiskeredCycle ∧ ¬Chordal whiskeredCycle ∧
    ¬ChordalBipartite whiskeredCycle :=
  ⟨graph_laws,graph_bipartite,independence_complex_shellable,
    not_chordal,not_chordal_bipartite⟩

theorem conjecture541_false :
    ¬(∀ G : Graph, GraphLaws G → Bipartite G → (Shellable G ↔ Chordal G)) := by
  intro h
  exact not_chordal ((h whiskeredCycle graph_laws graph_bipartite).mp independence_complex_shellable)

#print axioms every_prop_subset_encoded
#print axioms facet_iff_maximal
#print axioms every_maximal_independent_set
#print axioms independence_complex_shellable
#print axioms conjecture541_counterexample
#print axioms conjecture541_false
end Conjecture541
