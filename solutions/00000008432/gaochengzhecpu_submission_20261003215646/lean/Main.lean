import Std

namespace Conjecture8432
set_option maxRecDepth 100000
set_option maxHeartbeats 60000000

instance finiteExistsDecidable (n : Nat) (p : Fin n → Prop) [DecidablePred p] :
    Decidable (∃ i : Fin n, p i) :=
  decidable_of_iff (¬ ∀ i : Fin n, ¬ p i) (by classical simp)

abbrev Point := Fin 7
abbrev Message := Fin 8
abbrev Word := Fin 128
def bit (w : Word) (i : Point) : Bool := (w.val / 2^i.val) % 2 == 1
def mbit (u : Message) (j : Fin 3) : Bool := (u.val / 2^j.val) % 2 == 1
def wadd (u v : Word) : Word := ⟨(Nat.xor u.val v.val) % 128, Nat.mod_lt _ (by decide)⟩
def madd (u v : Message) : Message := ⟨(Nat.xor u.val v.val) % 8, Nat.mod_lt _ (by decide)⟩
def wscale (a : Bool) (w : Word) : Word := if a then w else 0
def weight (w : Word) : Nat := ((List.finRange 7).filter (bit w)).length

def encodeBits (b0 b1 b2 b3 b4 b5 b6 : Bool) : Word :=
  ⟨((if b0 then 1 else 0) + (if b1 then 2 else 0) + (if b2 then 4 else 0) +
    (if b3 then 8 else 0) + (if b4 then 16 else 0) + (if b5 then 32 else 0) +
    (if b6 then 64 else 0)) % 128, Nat.mod_lt _ (by decide)⟩
def table (b0 b1 b2 b3 b4 b5 b6 : Bool) (i : Point) : Bool :=
  match i.val with
  | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3 | 4 => b4 | 5 => b5 | _ => b6
theorem encodeBits_correct : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool, ∀ i : Point,
    bit (encodeBits b0 b1 b2 b3 b4 b5 b6) i = table b0 b1 b2 b3 b4 b5 b6 i := by decide
def encode (f : Point → Bool) : Word := encodeBits (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6)
theorem every_binary_word_encoded (f : Point → Bool) : bit (encode f) = f := by
  funext i
  unfold encode
  rw [encodeBits_correct]
  have all : ∀ i : Point, i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 := by decide
  rcases all i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
theorem bit_injective : ∀ u v : Word, (∀ i, bit u i = bit v i) → u=v := by decide
theorem every_prop_subset_encoded (S : Point → Prop) :
    ∃ w : Word, ∀ i, bit w i = true ↔ S i := by
  classical
  refine ⟨encode (fun i => decide (S i)), ?_⟩
  intro i
  rw [every_binary_word_encoded]
  simp

/-- These are exactly the coordinate operations of the binary vector space. -/
theorem vector_space_coordinate_bridge :
    (∀ u v : Word, ∀ i, bit (wadd u v) i = Bool.xor (bit u i) (bit v i)) ∧
    (∀ a w i, bit (wscale a w) i = (a && bit w i)) ∧
    (∀ u v : Message, ∀ j, mbit (madd u v) j = Bool.xor (mbit u j) (mbit v j)) := by decide

/-- The columns are precisely the seven nonzero binary triples. -/
def dot (u : Message) (i : Point) : Bool :=
  (((u.val % 2) * ((i.val+1) % 2) +
     ((u.val / 2) % 2) * (((i.val+1) / 2) % 2) +
     ((u.val / 4) % 2) * (((i.val+1) / 4) % 2)) % 2) == 1
def word (u : Message) : Word := encode (dot u)
def Code (w : Word) : Prop := ∃ u : Message, word u = w
instance (w : Word) : Decidable (Code w) := by unfold Code; infer_instance

theorem encoder_is_injective : ∀ u v : Message, word u = word v → u=v := by decide
theorem encoder_is_linear :
    word 0 = 0 ∧ (∀ u v : Message, word (madd u v) = wadd (word u) (word v)) := by decide
theorem code_is_linear : Code 0 ∧
    (∀ u v, Code u → Code v → Code (wadd u v)) ∧
    (∀ a w, Code w → Code (wscale a w)) := by
  have hz : Code 0 := ⟨0, encoder_is_linear.1⟩
  refine ⟨hz, ?_, ?_⟩
  · rintro u v ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨madd a b, encoder_is_linear.2 a b⟩
  · intro a w hw
    cases a
    · exact hz
    · exact hw
theorem codeword_weights : ∀ u : Message, weight (word u) = if u=0 then 0 else 4 := by decide
theorem number_of_codewords : ((List.finRange 128).filter (fun w => decide (Code w))).length = 8 := by decide

def MinimumSupport (w : Word) : Prop :=
  Code w ∧ 0 < weight w ∧ ∀ v : Word, Code v → 0 < weight v → weight w ≤ weight v
instance (w : Word) : Decidable (MinimumSupport w) := by unfold MinimumSupport; infer_instance
theorem complete_minimum_supports : ∀ w : Word,
    MinimumSupport w ↔ ∃ u : Message, u ≠ 0 ∧ word u = w := by decide
def blocks : List Word := ((List.finRange 8).filter (fun u => u != 0)).map word
theorem blocks_exactly_minimum_supports : ∀ w : Word, w ∈ blocks ↔ MinimumSupport w := by decide
theorem blocks_are_distinct : blocks.Nodup := by decide
theorem number_of_blocks : blocks.length = 7 := by decide
theorem block_size : ∀ w : Word, MinimumSupport w → weight w = 4 := by decide

def pairCount (i j : Point) : Nat :=
  (blocks.filter (fun w => bit w i && bit w j)).length
def tripleCount (i j k : Point) : Nat :=
  (blocks.filter (fun w => bit w i && bit w j && bit w k)).length
theorem all_pairs_have_lambda_two : ∀ i j : Point, i≠j → pairCount i j = 2 := by decide
theorem strength_is_not_three : tripleCount 0 1 2 = 0 ∧ tripleCount 0 1 3 = 1 := by decide

def SupportOfMinimumWord (S : Point → Prop) : Prop :=
  ∃ w : Word, MinimumSupport w ∧ ∀ i, S i ↔ bit w i = true
theorem all_genuine_supports (S : Point → Prop) :
    SupportOfMinimumWord S ↔ ∃ u : Message, u≠0 ∧ ∀ i, S i ↔ dot u i = true := by
  constructor
  · rintro ⟨w, hw, hs⟩
    obtain ⟨u, hu, rfl⟩ := (complete_minimum_supports w).mp hw
    exact ⟨u, hu, by simpa only [word, every_binary_word_encoded] using hs⟩
  · rintro ⟨u, hu, hs⟩
    refine ⟨word u, (complete_minimum_supports _).mpr ⟨u, hu, rfl⟩, ?_⟩
    simpa only [word, every_binary_word_encoded] using hs

/-- Standard hypergraph rank is the largest cardinality of an edge. -/
def HypergraphRank (r : Nat) : Prop :=
  (∀ w : Word, MinimumSupport w → weight w ≤ r) ∧
  ∃ w : Word, MinimumSupport w ∧ weight w = r
instance (r : Nat) : Decidable (HypergraphRank r) := by unfold HypergraphRank; infer_instance
theorem exact_rank : HypergraphRank 4 := by decide
theorem rank_is_not_t_plus_one : ¬ HypergraphRank (2+1) := by decide

/-- All hypotheses and the failed conclusion occur in the same concrete code. -/
theorem conjecture8432_counterexample :
    (Code 0 ∧ (∀ u v, Code u → Code v → Code (wadd u v)) ∧
      (∀ a w, Code w → Code (wscale a w))) ∧
    blocks.Nodup ∧ blocks.length=7 ∧
    (∀ w : Word, MinimumSupport w → weight w=4) ∧
    (∀ i j : Point, i≠j → pairCount i j=2) ∧
    HypergraphRank 4 ∧ ¬ HypergraphRank (2+1) :=
  ⟨code_is_linear, blocks_are_distinct, number_of_blocks, block_size,
    all_pairs_have_lambda_two, exact_rank, rank_is_not_t_plus_one⟩

end Conjecture8432
#print axioms Conjecture8432.conjecture8432_counterexample
#print axioms Conjecture8432.all_genuine_supports
