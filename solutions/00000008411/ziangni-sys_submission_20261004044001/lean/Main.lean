import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Logic.Equiv.Fintype

namespace TransitiveDesigns8411

abbrev Point (n : ℕ) := Fin (n + 5)

def block (n : ℕ) (i : Point n) : Finset (Point n) := Finset.univ.erase i
def blocks (n : ℕ) : Finset (Finset (Point n)) := Finset.univ.image (block n)

theorem block_injective (n : ℕ) : Function.Injective (block n) := by
  intro i j h
  exact (Finset.erase_inj Finset.univ (Finset.mem_univ i)).mp h

theorem block_card (n : ℕ) (i : Point n) : (block n i).card = n + 4 := by
  simp [block, Point]

theorem number_of_blocks (n : ℕ) : (blocks n).card = n + 5 := by
  rw [blocks, Finset.card_image_of_injective _ (block_injective n)]
  simp [Point]

/-- Standard incidence definition of a simple 3-(v,k,lambda) design. -/
def IsThreeDesign (n : ℕ) : Prop :=
  (∀ B ∈ blocks n, B.card = n + 4) ∧
  ∀ T : Finset (Point n), T.card = 3 →
    ((blocks n).filter (fun B => T ⊆ B)).card = n + 2

theorem contains_iff (n : ℕ) (T : Finset (Point n)) (i : Point n) :
    T ⊆ block n i ↔ i ∉ T := by
  simp [block, Finset.subset_erase]

theorem incidence_count (n : ℕ) (T : Finset (Point n)) (hT : T.card = 3) :
    ((blocks n).filter (fun B => T ⊆ B)).card = n + 2 := by
  rw [blocks, Finset.filter_image]
  simp_rw [contains_iff]
  rw [Finset.card_image_of_injective _ (block_injective n)]
  have he : (Finset.univ.filter (fun i : Point n => i ∉ T)) = Tᶜ := by
    ext i
    simp
  rw [he, Finset.card_compl, hT]
  simp [Point]

theorem actual_design (n : ℕ) : IsThreeDesign n := by
  constructor
  · intro B hB
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hB
    exact block_card n i
  · exact incidence_count n

/-- A permutation is an automorphism precisely when it preserves the block family. -/
def IsAutomorphism (n : ℕ) (e : Equiv.Perm (Point n)) : Prop :=
  ∀ B : Finset (Point n), B ∈ blocks n ↔ B.image e ∈ blocks n

theorem image_block (n : ℕ) (e : Equiv.Perm (Point n)) (i : Point n) :
    (block n i).image e = block n (e i) := by
  unfold block
  rw [Finset.image_erase e.injective]
  simp

theorem permutation_preserves (n : ℕ) (e : Equiv.Perm (Point n)) : IsAutomorphism n e := by
  have hf : ∀ (f : Equiv.Perm (Point n)) B, B ∈ blocks n → B.image f ∈ blocks n := by
    intro f B hB
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hB
    rw [image_block]
    exact Finset.mem_image.mpr ⟨f i, Finset.mem_univ _, rfl⟩
  intro B
  constructor
  · exact hf e B
  · intro h
    have hi := hf e.symm (B.image e) h
    simpa [Finset.image_image, Function.comp_def] using hi

/-- Transitivity on ordered triples of distinct points, expressed as embeddings. -/
def IsThreeTransitive (n : ℕ) : Prop :=
  ∀ a b : Fin 3 ↪ Point n,
    ∃ e : Equiv.Perm (Point n), IsAutomorphism n e ∧ ∀ i, e (a i) = b i

theorem three_transitive (n : ℕ) : IsThreeTransitive n := by
  classical
  intro a b
  let e : Set.range a ≃ Set.range b := a.toEquivRange.symm.trans b.toEquivRange
  refine ⟨e.extendSubtype, permutation_preserves n _, ?_⟩
  intro i
  rw [Equiv.extendSubtype_apply_of_mem e (a i) ⟨i, rfl⟩]
  simp [e]

/-- Actual block-preserving point bijections define isomorphism. -/
def Isomorphic (n m : ℕ) : Prop :=
  ∃ e : Point n ≃ Point m,
    ∀ B : Finset (Point n), B ∈ blocks n ↔ B.image e ∈ blocks m

theorem isomorphic_iff (n m : ℕ) : Isomorphic n m ↔ n = m := by
  constructor
  · rintro ⟨e, _⟩
    have hc := Fintype.card_congr e
    simp only [Point, Fintype.card_fin] at hc
    omega
  · rintro rfl
    refine ⟨Equiv.refl _, ?_⟩
    intro B
    simp

def designSetoid : Setoid ℕ where
  r := Isomorphic
  iseqv := ⟨fun n => (isomorphic_iff n n).2 rfl,
    fun h => (isomorphic_iff _ _).2 ((isomorphic_iff _ _).1 h).symm,
    fun h₁ h₂ => (isomorphic_iff _ _).2 (((isomorphic_iff _ _).1 h₁).trans
      ((isomorphic_iff _ _).1 h₂))⟩

theorem infinitely_many_isomorphism_classes : Infinite (Quotient designSetoid) := by
  apply Infinite.of_injective (fun n : ℕ => Quotient.mk designSetoid n)
  intro n m h
  exact (isomorphic_iff n m).1 (Quotient.exact h)

theorem conjecture_00000008411 :
    (∀ n, IsThreeDesign n ∧ IsThreeTransitive n ∧ 3 < n + 4 ∧ n + 4 < n + 5) ∧
    Infinite (Quotient designSetoid) := by
  refine ⟨fun n => ⟨actual_design n, three_transitive n, ?_, ?_⟩,
    infinitely_many_isomorphism_classes⟩ <;> omega

end TransitiveDesigns8411

#print axioms TransitiveDesigns8411.actual_design
#print axioms TransitiveDesigns8411.three_transitive
#print axioms TransitiveDesigns8411.conjecture_00000008411
