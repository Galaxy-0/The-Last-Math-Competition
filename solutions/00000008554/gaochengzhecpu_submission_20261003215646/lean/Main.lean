import Std

namespace Conjecture8554
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

abbrev E := Fin 4
abbrev Family := Fin 16
def below (x y : E) : Prop := x=0 ∨ y=3 ∨ x=y
instance (x y : E) : Decidable (below x y) := by unfold below; infer_instance
def meet (x y : E) : E := if x=3 then y else if y=3 then x else if x=y then x else 0
def join (x y : E) : E := if x=0 then y else if y=0 then x else if x=y then x else 3
theorem lattice_laws :
    (∀ x, below x x) ∧ (∀ x y, below x y → below y x → x=y) ∧
    (∀ x y z, below x y → below y z → below x z) ∧
    (∀ x y, below (meet x y) x ∧ below (meet x y) y) ∧
    (∀ x y z, below z x → below z y → below z (meet x y)) ∧
    (∀ x y, below x (join x y) ∧ below y (join x y)) ∧
    (∀ x y z, below x z → below y z → below (join x y) z) := by decide
def member (s : Family) (x : E) : Bool := (s.val / 2^x.val) % 2 == 1
def familySize (s : Family) : Nat := ((List.finRange 4).filter (member s)).length
def Chain (s : Family) : Prop := ∀ x y, member s x=true → member s y=true → below x y ∨ below y x
def Included (s t : Family) : Prop := ∀ x, member s x=true → member t x=true
def MaximalChain (s : Family) : Prop :=
  Chain s ∧ ∀ t, Chain t → Included s t → Included t s
instance (s : Family) : Decidable (Chain s) := by unfold Chain; infer_instance
instance (s t : Family) : Decidable (Included s t) := by unfold Included; infer_instance
instance (s : Family) : Decidable (MaximalChain s) := by unfold MaximalChain; infer_instance

def encodeBits (a b c d : Bool) : Family :=
  ⟨((if a then 1 else 0)+(if b then 2 else 0)+(if c then 4 else 0)+(if d then 8 else 0)) % 16,
    Nat.mod_lt _ (by decide)⟩
def table (a b c d : Bool) (x : E) : Bool :=
  match x.val with | 0 => a | 1 => b | 2 => c | _ => d
theorem bits_correct : ∀ a b c d : Bool, ∀ x : E,
    member (encodeBits a b c d) x = table a b c d x := by decide
def encode (f : E → Bool) : Family := encodeBits (f 0) (f 1) (f 2) (f 3)
theorem all_families (f : E → Bool) : member (encode f)=f := by
  funext x
  unfold encode
  rw [bits_correct]
  have all : ∀ x : E, x=0 ∨ x=1 ∨ x=2 ∨ x=3 := by decide
  rcases all x with rfl | rfl | rfl | rfl <;> rfl
theorem all_prop_families (S : E → Prop) :
    ∃ s : Family, ∀ x, member s x=true ↔ S x := by
  classical
  refine ⟨encode (fun x => decide (S x)), ?_⟩
  intro x
  rw [all_families]
  simp

/-- The actual lattice rank is two, i.e. maximum chain cardinality minus one. -/
theorem lattice_rank_two :
    (∀ s : Family, Chain s → familySize s ≤ 3) ∧
    Chain 11 ∧ familySize 11=3 ∧
    (∀ s : Family, MaximalChain s → familySize s=3) := by decide
def inCut (x : E) : Prop := x=1 ∨ x=2
instance (x : E) : Decidable (inCut x) := by unfold inCut; infer_instance
theorem genuine_crosscut :
    (∀ x, inCut x → x≠0 ∧ x≠3) ∧
    (∀ x y, inCut x → inCut y → below x y → x=y) ∧
    (∀ s : Family, MaximalChain s → member s 1=true ∨ member s 2=true) := by decide

def PropChain (S : E → Prop) : Prop := ∀ x y, S x → S y → below x y ∨ below y x
def PropMaximalChain (S : E → Prop) : Prop :=
  PropChain S ∧ ∀ T : E → Prop, PropChain T → (∀ x, S x → T x) → ∀ x, T x → S x
theorem every_actual_maximal_chain_meets_crosscut (S : E → Prop) (hS : PropMaximalChain S) :
    S 1 ∨ S 2 := by
  obtain ⟨s, hs⟩ := all_prop_families S
  have hc : Chain s := by
    intro x y hx hy
    exact hS.1 x y ((hs x).mp hx) ((hs y).mp hy)
  have hm : MaximalChain s := by
    refine ⟨hc, ?_⟩
    intro t ht hit x hx
    exact (hs x).mpr (hS.2 (fun y => member t y=true) ht
      (fun y hy => hit y ((hs y).mpr hy)) x hx)
  rcases genuine_crosscut.2.2 s hm with h | h
  · exact Or.inl ((hs 1).mp h)
  · exact Or.inr ((hs 2).mp h)

abbrev Vertex := Fin 2
abbrev FaceCode := Fin 4
def vertex (v : Vertex) : E := if v=0 then 1 else 2
def faceMember (s : FaceCode) (v : Vertex) : Bool := (s.val / 2^v.val) % 2 == 1
def faceSize (s : FaceCode) : Nat := ((List.finRange 2).filter (faceMember s)).length
def meetFace (s : FaceCode) : E := if s=0 then 3 else if s=1 then 1 else if s=2 then 2 else 0
def joinFace (s : FaceCode) : E := if s=0 then 0 else if s=1 then 1 else if s=2 then 2 else 3
theorem face_meet_and_join_are_genuine : ∀ s : FaceCode,
    (∀ x : E, below x (meetFace s) ↔ ∀ v, faceMember s v=true → below x (vertex v)) ∧
    (∀ x : E, below (joinFace s) x ↔ ∀ v, faceMember s v=true → below (vertex v) x) := by decide
def Face (s : FaceCode) : Prop := meetFace s ≠ 0 ∨ joinFace s ≠ 3
instance (s : FaceCode) : Decidable (Face s) := by unfold Face; infer_instance
theorem complete_face_list : ∀ s : FaceCode, Face s ↔ s=0 ∨ s=1 ∨ s=2 := by decide
theorem face_dimension_bound : ∀ s : FaceCode, Face s → faceSize s ≤ 1 := by decide
theorem downward_closed : ∀ s t : FaceCode, Face s →
    (∀ v, faceMember t v=true → faceMember s v=true) → Face t := by decide
theorem all_vertex_subsets_represented (S : Vertex → Prop) :
    ∃ s : FaceCode, ∀ v, faceMember s v=true ↔ S v := by
  classical
  have all : ∀ v : Vertex, v=0 ∨ v=1 := by decide
  by_cases h0 : S 0 <;> by_cases h1 : S 1
  · refine ⟨3, ?_⟩; intro v; rcases all v with rfl | rfl <;> simp [faceMember, h0, h1] <;> decide
  · refine ⟨1, ?_⟩; intro v; rcases all v with rfl | rfl <;> simp [faceMember, h0, h1] <;> decide
  · refine ⟨2, ?_⟩; intro v; rcases all v with rfl | rfl <;> simp [faceMember, h0, h1] <;> decide
  · refine ⟨0, ?_⟩; intro v; rcases all v with rfl | rfl <;> simp [faceMember, h0, h1] <;> decide

/-- All oriented simplices in dimension n, with the natural vertex order.
    Integral n-chains are arbitrary integer coefficient functions on them. -/
abbrev Simplex (n : Nat) := {s : FaceCode // Face s ∧ faceSize s=n+1}
abbrev ChainGroup (n : Nat) := Simplex n → Int
def zeroChain (n : Nat) : ChainGroup n := fun _ => 0
def leftVertex : Simplex 0 := ⟨1, by decide⟩
def rightVertex : Simplex 0 := ⟨2, by decide⟩
theorem all_zero_simplices (s : Simplex 0) : s=leftVertex ∨ s=rightVertex := by
  have all : ∀ s : FaceCode, Face s → faceSize s=1 → s=1 ∨ s=2 := by decide
  rcases all s.val s.property.1 s.property.2 with h | h
  · left; exact Subtype.ext h
  · right; exact Subtype.ext h
theorem no_positive_simplices (n : Nat) (s : Simplex (n+1)) : False := by
  have hb := face_dimension_bound s.val s.property.1
  have hc := s.property.2
  omega
theorem positive_chain_group_zero (n : Nat) (c : ChainGroup (n+1)) : c=zeroChain (n+1) := by
  funext s
  exact (no_positive_simplices n s).elim

/-- Every positive-degree simplicial boundary is the zero map because its
    entire domain group is zero, not because any incidence was omitted. -/
def boundary (n : Nat) (_ : ChainGroup (n+1)) : ChainGroup n := zeroChain n
theorem boundary_forced (n : Nat) (d : ChainGroup (n+1) → ChainGroup n)
    (hzero : d (zeroChain (n+1))=zeroChain n) (c : ChainGroup (n+1)) :
    d c=boundary n c := by
  rw [positive_chain_group_zero n c]
  exact hzero
def augmentation (c : ChainGroup 0) : Int := c leftVertex + c rightVertex
def IsBoundary (n : Nat) (c : ChainGroup n) : Prop :=
  ∃ b : ChainGroup (n+1), boundary n b=c
theorem boundary_iff_zero (n : Nat) (c : ChainGroup n) : IsBoundary n c ↔ c=zeroChain n := by
  constructor
  · rintro ⟨b, hb⟩; exact hb.symm
  · intro h; exact ⟨zeroChain (n+1), h.symm⟩

def IsCycle (reduced : Bool) : (n : Nat) → ChainGroup n → Prop
  | 0, c => if reduced then augmentation c=0 else True
  | n+1, c => boundary n c=zeroChain n
def NonzeroHomology (reduced : Bool) (n : Nat) : Prop :=
  ∃ c : ChainGroup n, IsCycle reduced n c ∧ ¬IsBoundary n c
def HomologyZero (reduced : Bool) (n : Nat) : Prop :=
  ∀ c : ChainGroup n, IsCycle reduced n c → IsBoundary n c

def ordinaryWitness : ChainGroup 0 := fun s => if s.val=1 then 1 else 0
def reducedWitness : ChainGroup 0 := fun s => if s.val=1 then 1 else -1
theorem ordinary_homology_nonzero : NonzeroHomology false 0 := by
  refine ⟨ordinaryWitness, True.intro, ?_⟩
  intro hb
  have h := congrFun ((boundary_iff_zero 0 ordinaryWitness).mp hb) leftVertex
  change (1 : Int)=0 at h
  contradiction
theorem reduced_homology_nonzero : NonzeroHomology true 0 := by
  refine ⟨reducedWitness, by change augmentation reducedWitness=0; decide, ?_⟩
  intro hb
  have h := congrFun ((boundary_iff_zero 0 reducedWitness).mp hb) leftVertex
  change (1 : Int)=0 at h
  contradiction
theorem higher_homology_zero (reduced : Bool) (n : Nat) : HomologyZero reduced (n+1) := by
  intro c _
  exact (boundary_iff_zero _ _).mpr (positive_chain_group_zero n c)
def HomologicalDimension (reduced : Bool) (d : Nat) : Prop :=
  NonzeroHomology reduced d ∧ ∀ n, d<n → HomologyZero reduced n
theorem dimension_zero (reduced : Bool) : HomologicalDimension reduced 0 := by
  constructor
  · cases reduced
    · exact ordinary_homology_nonzero
    · exact reduced_homology_nonzero
  · intro n hn
    cases n with
    | zero => omega
    | succ n => exact higher_homology_zero reduced n
theorem dimension_is_not_one (reduced : Bool) : ¬HomologicalDimension reduced 1 := by
  rintro ⟨⟨c, hc, hb⟩, _⟩
  exact hb (higher_homology_zero reduced 0 c hc)

def mobius (x : E) : Int := if x=0 then 1 else if x=3 then 1 else -1
def initialSum (f : E → Int) (x : E) : Int :=
  ((List.finRange 4).filter (fun y => decide (below y x))).foldl (fun a y => a+f y) 0
theorem actual_mobius_recurrence :
    mobius 0=1 ∧ ∀ x : E, x≠0 → initialSum mobius x=0 := by decide
theorem actual_mobius_unique (f : E → Int) (h0 : f 0=1)
    (h : ∀ x : E, x≠0 → initialSum f x=0) : f=mobius := by
  have h1 := h 1 (by decide)
  have h2 := h 2 (by decide)
  have h3 := h 3 (by decide)
  change (0+f 0)+f 1=0 at h1
  change (0+f 0)+f 2=0 at h2
  change (((0+f 0)+f 1)+f 2)+f 3=0 at h3
  funext x
  have all : ∀ x : E, x=0 ∨ x=1 ∨ x=2 ∨ x=3 := by decide
  rcases all x with rfl | rfl | rfl | rfl
  · exact h0
  · change f 1 = -1; omega
  · change f 2 = -1; omega
  · change f 3 = 1; omega

theorem euler_conventions :
    ((List.finRange 4).filter (fun s => decide (Face s ∧ faceSize s=1))).length=2 ∧
    ((List.finRange 4).filter (fun s => decide (Face s ∧ faceSize s=2))).length=0 ∧
    mobius 3=1 ∧ (2 : Int)≠mobius 3 ∧ (2 : Int)-1=mobius 3 := by decide

theorem conjecture8554_counterexample :
    HomologicalDimension false 0 ∧ HomologicalDimension true 0 ∧
    ¬HomologicalDimension false (2-1) ∧ ¬HomologicalDimension true (2-1) :=
  ⟨dimension_zero false, dimension_zero true, dimension_is_not_one false, dimension_is_not_one true⟩

end Conjecture8554
#print axioms Conjecture8554.conjecture8554_counterexample
#print axioms Conjecture8554.boundary_forced
#print axioms Conjecture8554.actual_mobius_unique
