import Std

/-! The three-element chain has Boolean sublattice embedding dimension 2.
    It needs 3 generators using meet and join, or 1 when bounds are constants. -/
namespace Conjecture8558
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

abbrev E := Fin 3
abbrev Subset := Fin 8
def Below (x y : E) : Prop := x.val ≤ y.val
def meet (x y : E) : E := if x.val ≤ y.val then x else y
def join (x y : E) : E := if x.val ≤ y.val then y else x
instance (x y : E) : Decidable (Below x y) := by unfold Below; infer_instance

theorem chain_lattice_laws :
    (∀ x : E, Below x x) ∧
    (∀ x y : E, Below x y → Below y x → x = y) ∧
    (∀ x y z : E, Below x y → Below y z → Below x z) ∧
    (∀ x : E, Below 0 x ∧ Below x 2) ∧
    (∀ x y : E, Below (meet x y) x ∧ Below (meet x y) y) ∧
    (∀ x y z : E, Below z x → Below z y → Below z (meet x y)) ∧
    (∀ x y : E, Below x (join x y) ∧ Below y (join x y)) ∧
    (∀ x y z : E, Below x z → Below y z → Below (join x y) z) := by decide

theorem chain_distributive : ∀ x y z : E,
    meet x (join y z) = join (meet x y) (meet x z) ∧
    join x (meet y z) = meet (join x y) (join x z) := by decide

/-- The Boolean lattice of dimension n is the full power set of Fin n,
    represented by membership functions, with intersection and union. -/
abbrev BooleanLattice (n : Nat) := Fin n → Bool
def boolMeet {n : Nat} (s t : BooleanLattice n) : BooleanLattice n := fun i => s i && t i
def boolJoin {n : Nat} (s t : BooleanLattice n) : BooleanLattice n := fun i => s i || t i

theorem every_boolean_subset_encoded {n : Nat} (p : Fin n → Prop) :
    ∃ f : BooleanLattice n, ∀ i, f i = true ↔ p i := by
  classical
  exact ⟨fun i => decide (p i), fun i => by simp⟩

/-- An actual sublattice embedding: injective and preserving both operations.
    No preservation of bounds is assumed. -/
structure BooleanEmbedding (n : Nat) where
  map : E → BooleanLattice n
  injective : ∀ x y, map x = map y → x = y
  map_meet : ∀ x y, map (meet x y) = boolMeet (map x) (map y)
  map_join : ∀ x y, map (join x y) = boolJoin (map x) (map y)

def cut (x : E) (i : Fin 2) : Bool := decide (i.val < x.val)

def embeddingTwo : BooleanEmbedding 2 where
  map := cut
  injective := by
    intro x y h
    have sep : ∀ x y : E, (∀ i : Fin 2, cut x i = cut y i) → x = y := by decide
    exact sep x y (fun i => congrFun h i)
  map_meet := by
    intro x y
    funext i
    have h : ∀ x y : E, ∀ i : Fin 2,
        cut (meet x y) i = (cut x i && cut y i) := by decide
    exact h x y i
  map_join := by
    intro x y
    funext i
    have h : ∀ x y : E, ∀ i : Fin 2,
        cut (join x y) i = (cut x i || cut y i) := by decide
    exact h x y i

theorem embeddingTwo_preserves_bounds :
    embeddingTwo.map 0 = (fun _ => false) ∧ embeddingTwo.map 2 = (fun _ => true) := by
  have h : ∀ i : Fin 2, cut 0 i = false ∧ cut 2 i = true := by decide
  constructor
  · funext i; exact (h i).1
  · funext i; exact (h i).2

theorem no_embedding_zero : ¬ Nonempty (BooleanEmbedding 0) := by
  rintro ⟨f⟩
  have h : f.map 0 = f.map 1 := by funext i; exact Fin.elim0 i
  exact (by decide : (0 : E) ≠ 1) (f.injective 0 1 h)

theorem no_embedding_one : ¬ Nonempty (BooleanEmbedding 1) := by
  rintro ⟨f⟩
  have ext (x y : E) (h : f.map x 0 = f.map y 0) : f.map x = f.map y := by
    funext i
    have all : ∀ i : Fin 1, i = 0 := by decide
    rw [all i]
    exact h
  have dup : ∀ a b c : Bool, a = b ∨ a = c ∨ b = c := by decide
  rcases dup (f.map 0 0) (f.map 1 0) (f.map 2 0) with h | h | h
  · exact (by decide : (0 : E) ≠ 1) (f.injective 0 1 (ext 0 1 h))
  · exact (by decide : (0 : E) ≠ 2) (f.injective 0 2 (ext 0 2 h))
  · exact (by decide : (1 : E) ≠ 2) (f.injective 1 2 (ext 1 2 h))

def MinimumBooleanDimension (n : Nat) : Prop :=
  Nonempty (BooleanEmbedding n) ∧ ∀ m : Nat, m < n → ¬ Nonempty (BooleanEmbedding m)

theorem boolean_dimension_two : MinimumBooleanDimension 2 := by
  refine ⟨⟨embeddingTwo⟩, ?_⟩
  intro m hm
  have h : m = 0 ∨ m = 1 := by omega
  rcases h with rfl | rfl
  · exact no_embedding_zero
  · exact no_embedding_one

theorem boolean_dimension_unique (n : Nat) (h : MinimumBooleanDimension n) : n = 2 := by
  have hlo : ¬ n < 2 := fun hlt => boolean_dimension_two.2 n hlt h.1
  have hhi : ¬ 2 < n := fun hlt => h.2 2 hlt ⟨embeddingTwo⟩
  omega

def member (s : Subset) (x : E) : Bool := (s.val / 2^x.val) % 2 == 1
def cardinality (s : Subset) : Nat := ((List.finRange 3).filter (member s)).length
def encodeBits (b0 b1 b2 : Bool) : Subset :=
  ⟨((if b0 then 1 else 0) + (if b1 then 2 else 0) + (if b2 then 4 else 0)) % 8,
    Nat.mod_lt _ (by decide)⟩
def table (b0 b1 b2 : Bool) (x : E) : Bool :=
  match x.val with | 0 => b0 | 1 => b1 | _ => b2
theorem encodeBits_correct : ∀ b0 b1 b2 : Bool, ∀ x : E,
    member (encodeBits b0 b1 b2) x = table b0 b1 b2 x := by decide
def encode (p : E → Bool) : Subset := encodeBits (p 0) (p 1) (p 2)
theorem every_subset_encoded (p : E → Bool) : member (encode p) = p := by
  funext x
  unfold encode
  rw [encodeBits_correct]
  have all : ∀ x : E, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  rcases all x with rfl | rfl | rfl <;> rfl
theorem every_prop_subset_encoded (p : E → Prop) :
    ∃ s : Subset, ∀ x, member s x = true ↔ p x := by
  classical
  refine ⟨encode (fun x => decide (p x)), ?_⟩
  intro x
  rw [every_subset_encoded]
  simp

/-- Generation by lattice terms, with only the two binary operations. -/
inductive Generated (s : Subset) : E → Prop
  | basic {x : E} : member s x = true → Generated s x
  | inf {x y : E} : Generated s x → Generated s y → Generated s (meet x y)
  | sup {x y : E} : Generated s x → Generated s y → Generated s (join x y)

theorem generated_iff (s : Subset) (x : E) : Generated s x ↔ member s x = true := by
  constructor
  · intro h
    induction h with
    | basic hm => exact hm
    | inf h1 h2 ih1 ih2 => unfold meet; split <;> assumption
    | sup h1 h2 ih1 ih2 => unfold join; split <;> assumption
  · exact Generated.basic

/-- Term generation is the least closure under the two lattice operations. -/
theorem generated_universal (s : Subset) (p : E → Prop)
    (hbasic : ∀ x, member s x = true → p x)
    (hmeet : ∀ x y, p x → p y → p (meet x y))
    (hjoin : ∀ x y, p x → p y → p (join x y)) :
    ∀ x, Generated s x → p x := by
  intro x h
  induction h with
  | basic hm => exact hbasic _ hm
  | inf _ _ ih1 ih2 => exact hmeet _ _ ih1 ih2
  | sup _ _ ih1 ih2 => exact hjoin _ _ ih1 ih2

def Generates (s : Subset) : Prop := ∀ x : E, Generated s x
theorem generates_iff (s : Subset) : Generates s ↔ ∀ x : E, member s x = true := by
  constructor
  · intro h x; exact (generated_iff s x).mp (h x)
  · intro h x; exact (generated_iff s x).mpr (h x)

theorem generator_cardinality (s : Subset) (h : Generates s) : cardinality s = 3 := by
  have finite : ∀ s : Subset, (∀ x : E, member s x = true) → cardinality s = 3 := by decide
  exact finite s ((generates_iff s).mp h)

def MinimumGeneratorNumber (n : Nat) : Prop :=
  (∃ s : Subset, Generates s ∧ cardinality s = n) ∧
    ∀ s : Subset, Generates s → n ≤ cardinality s

theorem generator_number_three : MinimumGeneratorNumber 3 := by
  constructor
  · exact ⟨7, (generates_iff 7).mpr (by decide), by decide⟩
  · intro s hs
    rw [generator_cardinality s hs]
    decide

theorem generator_number_unique (n : Nat) (h : MinimumGeneratorNumber n) : n = 3 := by
  rcases h.1 with ⟨s, hs, hn⟩
  have hthree := generator_cardinality s hs
  omega

/-- The alternative bounded-lattice signature also allows bottom and top. -/
inductive BoundedGenerated (s : Subset) : E → Prop
  | basic {x : E} : member s x = true → BoundedGenerated s x
  | bottom : BoundedGenerated s 0
  | top : BoundedGenerated s 2
  | inf {x y : E} : BoundedGenerated s x → BoundedGenerated s y → BoundedGenerated s (meet x y)
  | sup {x y : E} : BoundedGenerated s x → BoundedGenerated s y → BoundedGenerated s (join x y)

theorem bounded_generated_iff (s : Subset) (x : E) :
    BoundedGenerated s x ↔ x = 0 ∨ x = 2 ∨ member s x = true := by
  constructor
  · intro h
    induction h with
    | basic hm => exact Or.inr (Or.inr hm)
    | bottom => exact Or.inl rfl
    | top => exact Or.inr (Or.inl rfl)
    | inf h1 h2 ih1 ih2 => unfold meet; split <;> assumption
    | sup h1 h2 ih1 ih2 => unfold join; split <;> assumption
  · rintro (rfl | rfl | hm)
    · exact BoundedGenerated.bottom
    · exact BoundedGenerated.top
    · exact BoundedGenerated.basic hm

def BoundedGenerates (s : Subset) : Prop := ∀ x : E, BoundedGenerated s x
theorem bounded_generates_iff (s : Subset) : BoundedGenerates s ↔ member s 1 = true := by
  constructor
  · intro h
    have hm := (bounded_generated_iff s 1).mp (h 1)
    simpa using hm
  · intro h x
    have all : ∀ x : E, x = 0 ∨ x = 1 ∨ x = 2 := by decide
    rcases all x with rfl | rfl | rfl
    · exact BoundedGenerated.bottom
    · exact BoundedGenerated.basic h
    · exact BoundedGenerated.top

def MinimumBoundedGeneratorNumber (n : Nat) : Prop :=
  (∃ s : Subset, BoundedGenerates s ∧ cardinality s = n) ∧
    ∀ s : Subset, BoundedGenerates s → n ≤ cardinality s

theorem bounded_generator_number_one : MinimumBoundedGeneratorNumber 1 := by
  constructor
  · exact ⟨2, (bounded_generates_iff 2).mpr (by decide), by decide⟩
  · intro s hs
    have finite : ∀ s : Subset, member s 1 = true → 1 ≤ cardinality s := by decide
    exact finite s ((bounded_generates_iff s).mp hs)

theorem bounded_generator_number_unique (n : Nat)
    (h : MinimumBoundedGeneratorNumber n) : n = 1 := by
  rcases h.1 with ⟨s, hs, hn⟩
  have hlo := bounded_generator_number_one.2 s hs
  have hhi := h.2 2 ((bounded_generates_iff 2).mpr (by decide))
  have hcard : cardinality (2 : Subset) = 1 := by decide
  omega

/-- The equality assertion would assign one common minimum to this chain. -/
def EmbeddingEqualsGenerators : Prop :=
  ∃ n : Nat, MinimumBooleanDimension n ∧ MinimumGeneratorNumber n
def EmbeddingEqualsBoundedGenerators : Prop :=
  ∃ n : Nat, MinimumBooleanDimension n ∧ MinimumBoundedGeneratorNumber n

theorem conjecture_8558_false : ¬ EmbeddingEqualsGenerators := by
  rintro ⟨n, hd, hg⟩
  have htwo := boolean_dimension_unique n hd
  have hthree := generator_number_unique n hg
  omega

theorem conjecture_8558_bounded_signature_false : ¬ EmbeddingEqualsBoundedGenerators := by
  rintro ⟨n, hd, hg⟩
  have htwo := boolean_dimension_unique n hd
  have hone := bounded_generator_number_unique n hg
  omega

#print axioms chain_lattice_laws
#print axioms every_boolean_subset_encoded
#print axioms every_prop_subset_encoded
#print axioms boolean_dimension_two
#print axioms embeddingTwo_preserves_bounds
#print axioms generator_number_three
#print axioms bounded_generator_number_one
#print axioms conjecture_8558_false
#print axioms conjecture_8558_bounded_signature_false
end Conjecture8558
