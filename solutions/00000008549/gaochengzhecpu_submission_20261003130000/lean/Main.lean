import Std

/-! The partition lattice on three points is the five-element diamond.
    Every maximal chain has three elements, hence length two. -/
namespace Conjecture8549
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

abbrev Point := Fin 3
abbrev RelationCode := Fin 512
abbrev E := Fin 5
abbrev Subset := Fin 32

def relation (r : RelationCode) (i j : Point) : Bool :=
  (r.val / 2^(3*i.val+j.val)) % 2 == 1

def IsEquivalence (r : RelationCode) : Prop :=
  (∀ i, relation r i i = true) ∧
  (∀ i j, relation r i j = true → relation r j i = true) ∧
  (∀ i j k, relation r i j = true → relation r j k = true → relation r i k = true)
instance (r : RelationCode) : Decidable (IsEquivalence r) := by
  unfold IsEquivalence; infer_instance

/-- A partition is represented by its same-block equivalence relation. -/
abbrev Partition := {r : RelationCode // IsEquivalence r}

def encodeRelationBits (b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool) : RelationCode :=
  ⟨((if b0 then 1 else 0) + (if b1 then 2 else 0) + (if b2 then 4 else 0) +
    (if b3 then 8 else 0) + (if b4 then 16 else 0) + (if b5 then 32 else 0) +
    (if b6 then 64 else 0) + (if b7 then 128 else 0) + (if b8 then 256 else 0)) % 512,
   Nat.mod_lt _ (by decide)⟩

def relationTable (b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool) (i j : Point) : Bool :=
  match 3*i.val+j.val with
  | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3 | 4 => b4 | 5 => b5
  | 6 => b6 | 7 => b7 | _ => b8

theorem encodeRelationBits_correct : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool,
    ∀ i j : Point,
    relation (encodeRelationBits b0 b1 b2 b3 b4 b5 b6 b7 b8) i j =
      relationTable b0 b1 b2 b3 b4 b5 b6 b7 b8 i j := by decide

def encodeRelation (r : Point → Point → Bool) : RelationCode :=
  encodeRelationBits (r 0 0) (r 0 1) (r 0 2) (r 1 0) (r 1 1)
    (r 1 2) (r 2 0) (r 2 1) (r 2 2)

theorem every_relation_encoded (r : Point → Point → Bool) :
    relation (encodeRelation r) = r := by
  funext i j
  unfold encodeRelation
  rw [encodeRelationBits_correct]
  have all : ∀ i : Point, i = 0 ∨ i = 1 ∨ i = 2 := by decide
  rcases all i with rfl | rfl | rfl <;>
    rcases all j with rfl | rfl | rfl <;> rfl

theorem every_prop_partition_encoded (r : Point → Point → Prop)
    (hrefl : ∀ i, r i i) (hsymm : ∀ i j, r i j → r j i)
    (htrans : ∀ i j k, r i j → r j k → r i k) :
    ∃ p : Partition, ∀ i j, relation p.val i j = true ↔ r i j := by
  classical
  let encoded := encodeRelation (fun i j => decide (r i j))
  have heq (i j : Point) : relation encoded i j = true ↔ r i j := by
    change relation (encodeRelation (fun i j => decide (r i j))) i j = true ↔ r i j
    rw [every_relation_encoded]
    simp
  have hv : IsEquivalence encoded := by
    refine ⟨?_, ?_, ?_⟩
    · intro i; exact (heq i i).mpr (hrefl i)
    · intro i j hij; exact (heq j i).mpr (hsymm i j ((heq i j).mp hij))
    · intro i j k hij hjk
      exact (heq i k).mpr (htrans i j k ((heq i j).mp hij) ((heq j k).mp hjk))
  exact ⟨⟨encoded, hv⟩, heq⟩

theorem all_equivalence_codes : ∀ r : RelationCode, IsEquivalence r →
    r = 273 ∨ r = 283 ∨ r = 341 ∨ r = 433 ∨ r = 511 := by decide

def codeOf (x : E) : RelationCode :=
  if x = 0 then 273 else if x = 1 then 283 else if x = 2 then 341
  else if x = 3 then 433 else 511
theorem codeOf_valid : ∀ x : E, IsEquivalence (codeOf x) := by decide
def partitionOf (x : E) : Partition := ⟨codeOf x, codeOf_valid x⟩
def label (p : Partition) : E :=
  if p.val = 273 then 0 else if p.val = 283 then 1 else if p.val = 341 then 2
  else if p.val = 433 then 3 else 4

theorem label_partitionOf : ∀ x : E, label (partitionOf x) = x := by decide

theorem partitionOf_label (p : Partition) : partitionOf (label p) = p := by
  rcases p with ⟨r, hr⟩
  rcases all_equivalence_codes r hr with h | h | h | h | h <;>
    subst r <;> rfl

def Below (x y : E) : Prop := x = 0 ∨ y = 4 ∨ x = y
instance (x y : E) : Decidable (Below x y) := by unfold Below; infer_instance

def Refines (p q : Partition) : Prop :=
  ∀ i j, relation p.val i j = true → relation q.val i j = true
instance (p q : Partition) : Decidable (Refines p q) := by unfold Refines; infer_instance

theorem partition_refinement_iff : ∀ x y : E,
    Refines (partitionOf x) (partitionOf y) ↔ Below x y := by decide

theorem arbitrary_partition_refinement (p q : Partition) :
    Refines p q ↔ Below (label p) (label q) := by
  have h := partition_refinement_iff (label p) (label q)
  simpa only [partitionOf_label] using h

def meet (x y : E) : E :=
  if x = 4 then y else if y = 4 then x else if x = y then x else 0
def join (x y : E) : E :=
  if x = 0 then y else if y = 0 then x else if x = y then x else 4

theorem diamond_lattice_laws :
    (∀ x : E, Below x x) ∧
    (∀ x y : E, Below x y → Below y x → x = y) ∧
    (∀ x y z : E, Below x y → Below y z → Below x z) ∧
    (∀ x : E, Below 0 x ∧ Below x 4) ∧
    (∀ x y : E, Below (meet x y) x ∧ Below (meet x y) y) ∧
    (∀ x y z : E, Below z x → Below z y → Below z (meet x y)) ∧
    (∀ x y : E, Below x (join x y) ∧ Below y (join x y)) ∧
    (∀ x y z : E, Below x z → Below y z → Below (join x y) z) := by decide

def member (s : Subset) (x : E) : Bool := (s.val / 2^x.val) % 2 == 1
def cardinality (s : Subset) : Nat := ((List.finRange 5).filter (member s)).length
def encodeBits (b0 b1 b2 b3 b4 : Bool) : Subset :=
  ⟨((if b0 then 1 else 0) + (if b1 then 2 else 0) + (if b2 then 4 else 0) +
    (if b3 then 8 else 0) + (if b4 then 16 else 0)) % 32, Nat.mod_lt _ (by decide)⟩
def table (b0 b1 b2 b3 b4 : Bool) (x : E) : Bool :=
  match x.val with
  | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3 | _ => b4
theorem encodeBits_correct : ∀ b0 b1 b2 b3 b4 : Bool, ∀ x : E,
    member (encodeBits b0 b1 b2 b3 b4) x = table b0 b1 b2 b3 b4 x := by decide
def encode (p : E → Bool) : Subset := encodeBits (p 0) (p 1) (p 2) (p 3) (p 4)
theorem every_subset_encoded (p : E → Bool) : member (encode p) = p := by
  funext x
  unfold encode
  rw [encodeBits_correct]
  have all : ∀ x : E, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 := by decide
  rcases all x with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem every_prop_subset_encoded (p : E → Prop) :
    ∃ s : Subset, ∀ x, member s x = true ↔ p x := by
  classical
  refine ⟨encode (fun x => decide (p x)), ?_⟩
  intro x
  rw [every_subset_encoded]
  simp

theorem subset_ext : ∀ a b : Subset, (∀ x : E, member a x = member b x) → a = b := by decide

def Included (s t : Subset) : Prop := ∀ x, member s x = true → member t x = true
def Chain (s : Subset) : Prop :=
  ∀ x y, member s x = true → member s y = true → Below x y ∨ Below y x
instance (s t : Subset) : Decidable (Included s t) := by unfold Included; infer_instance
instance (s : Subset) : Decidable (Chain s) := by unfold Chain; infer_instance
def MaximalChain (s : Subset) : Prop :=
  Chain s ∧ ∀ t : Subset, Chain t → Included s t → Included t s
instance (s : Subset) : Decidable (MaximalChain s) := by unfold MaximalChain; infer_instance

theorem all_maximal_chains : ∀ s : Subset,
    MaximalChain s ↔ s = 19 ∨ s = 21 ∨ s = 25 := by decide
theorem maximal_chain_cardinality : ∀ s : Subset,
    MaximalChain s → cardinality s = 3 := by decide

def PartitionChain (c : Partition → Prop) : Prop :=
  ∀ p q, c p → c q → Refines p q ∨ Refines q p
def MaximalPartitionChain (c : Partition → Prop) : Prop :=
  PartitionChain c ∧ ∀ d : Partition → Prop,
    PartitionChain d → (∀ p, c p → d p) → ∀ p, d p → c p
def Lift (s : Subset) (p : Partition) : Prop := member s (label p) = true
def Codes (s : Subset) (c : Partition → Prop) : Prop := ∀ p, Lift s p ↔ c p

theorem every_partition_family_encoded (c : Partition → Prop) :
    ∃ s : Subset, Codes s c := by
  rcases every_prop_subset_encoded (fun x => c (partitionOf x)) with ⟨s, hs⟩
  refine ⟨s, ?_⟩
  intro p
  have h := hs (label p)
  simpa only [partitionOf_label] using h

theorem codes_unique (s t : Subset) (c : Partition → Prop)
    (hs : Codes s c) (ht : Codes t c) : s = t := by
  apply subset_ext s t
  intro x
  have h := (hs (partitionOf x)).trans (ht (partitionOf x)).symm
  simp only [Lift, label_partitionOf] at h
  cases h1 : member s x <;> cases h2 : member t x <;> simp_all

theorem lift_chain (s : Subset) (h : Chain s) : PartitionChain (Lift s) := by
  intro p q hp hq
  rcases h (label p) (label q) hp hq with hpq | hqp
  · exact Or.inl ((arbitrary_partition_refinement p q).mpr hpq)
  · exact Or.inr ((arbitrary_partition_refinement q p).mpr hqp)

theorem chain_of_codes (s : Subset) (c : Partition → Prop) (hc : Codes s c)
    (h : PartitionChain c) : Chain s := by
  intro x y hx hy
  have hpx : c (partitionOf x) := (hc (partitionOf x)).mp (by simpa [Lift, label_partitionOf] using hx)
  have hpy : c (partitionOf y) := (hc (partitionOf y)).mp (by simpa [Lift, label_partitionOf] using hy)
  rcases h (partitionOf x) (partitionOf y) hpx hpy with hxy | hyx
  · exact Or.inl ((partition_refinement_iff x y).mp hxy)
  · exact Or.inr ((partition_refinement_iff y x).mp hyx)

theorem maximal_chain_of_codes (s : Subset) (c : Partition → Prop)
    (hc : Codes s c) (h : MaximalPartitionChain c) : MaximalChain s := by
  refine ⟨chain_of_codes s c hc h.1, ?_⟩
  intro t ht hst x hx
  have hext : ∀ p, Lift t p → c p := h.2 (Lift t) (lift_chain t ht) (by
    intro p hp
    exact hst (label p) ((hc p).mpr hp))
  have hcx : c (partitionOf x) := hext (partitionOf x) (by simpa [Lift, label_partitionOf] using hx)
  have hsx := (hc (partitionOf x)).mpr hcx
  simpa [Lift, label_partitionOf] using hsx

theorem maximal_lift (s : Subset) (h : MaximalChain s) :
    MaximalPartitionChain (Lift s) := by
  refine ⟨lift_chain s h.1, ?_⟩
  intro d hd hin p hp
  rcases every_partition_family_encoded d with ⟨t, ht⟩
  have hst : Included s t := by
    intro x hx
    have hx' : Lift s (partitionOf x) := by simpa [Lift, label_partitionOf] using hx
    have hdx := hin (partitionOf x) hx'
    have htx := (ht (partitionOf x)).mpr hdx
    simpa [Lift, label_partitionOf] using htx
  exact h.2 t (chain_of_codes t d ht hd) hst (label p) ((ht p).mpr hp)

theorem three_actual_maximal_chains :
    MaximalPartitionChain (Lift 19) ∧
    MaximalPartitionChain (Lift 21) ∧
    MaximalPartitionChain (Lift 25) :=
  ⟨maximal_lift 19 (by decide), maximal_lift 21 (by decide), maximal_lift 25 (by decide)⟩

theorem arbitrary_maximal_chains_cardinality (c : Partition → Prop)
    (h : MaximalPartitionChain c) :
    ∀ s : Subset, Codes s c → cardinality s = 3 := by
  intro s hs
  exact maximal_chain_cardinality s (maximal_chain_of_codes s c hs h)

/-- Length counts covering edges, one fewer than the number of elements. -/
def HasChainLength (c : Partition → Prop) (n : Nat) : Prop :=
  ∃ s : Subset, Codes s c ∧ cardinality s = n+1

theorem every_maximal_partition_chain_length_two (c : Partition → Prop)
    (h : MaximalPartitionChain c) : HasChainLength c 2 := by
  rcases every_partition_family_encoded c with ⟨s, hs⟩
  exact ⟨s, hs, arbitrary_maximal_chains_cardinality c h s hs⟩

theorem maximal_partition_chain_length_unique (c : Partition → Prop) (n : Nat)
    (h : MaximalPartitionChain c) (hn : HasChainLength c n) : n = 2 := by
  rcases hn with ⟨s, hs, hcard⟩
  have hthree := arbitrary_maximal_chains_cardinality c h s hs
  omega

def VariableMaximalChainLengths : Prop :=
  ∃ c d : Partition → Prop, ∃ m n : Nat,
    MaximalPartitionChain c ∧ MaximalPartitionChain d ∧
    HasChainLength c m ∧ HasChainLength d n ∧ m ≠ n

theorem conjecture_8549_diamond_claim_false : ¬ VariableMaximalChainLengths := by
  rintro ⟨c, d, m, n, hc, hd, hm, hn, hne⟩
  exact hne ((maximal_partition_chain_length_unique c m hc hm).trans
    (maximal_partition_chain_length_unique d n hd hn).symm)

#print axioms every_prop_partition_encoded
#print axioms partitionOf_label
#print axioms arbitrary_partition_refinement
#print axioms diamond_lattice_laws
#print axioms all_maximal_chains
#print axioms codes_unique
#print axioms three_actual_maximal_chains
#print axioms every_maximal_partition_chain_length_two
#print axioms conjecture_8549_diamond_claim_false
end Conjecture8549
