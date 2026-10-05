import Mathlib.Data.Matroid.Rank.ENat
import Mathlib.Data.Matroid.Minor.Contract
import Mathlib.Tactic
import Conjecture574.FlatDefs

noncomputable section
open Set

namespace Conjecture574

/-- The usual uniform matroid, constructed from the actual independence axioms. -/
def uniform (α : Type*) [Finite α] (r : ℕ) : Matroid α :=
  (IndepMatroid.ofFinite (Set.toFinite (Set.univ : Set α))
    (fun I => I.ncard ≤ r)
    (by simp)
    (fun _ _ hJ hIJ => (Set.ncard_le_ncard hIJ).trans hJ)
    (by
      intro I J hI hJ hcard
      have hnsub : ¬ J ⊆ I := fun h => (Nat.not_lt_of_ge (Set.ncard_le_ncard h)) hcard
      obtain ⟨e, heJ, heI⟩ := Set.not_subset.mp hnsub
      refine ⟨e, heJ, heI, ?_⟩
      change (insert e I).ncard ≤ r
      rw [Set.ncard_insert_of_not_mem heI]
      omega)
    (fun _ _ => Set.subset_univ _)).matroid

@[simp] theorem uniform_ground (α : Type*) [Finite α] (r : ℕ) :
    (uniform α r).E = Set.univ := rfl

@[simp] theorem uniform_indep_iff {α : Type*} [Finite α] (r : ℕ) (I : Set α) :
    (uniform α r).Indep I ↔ I.ncard ≤ r := Iff.rfl

theorem uniform_isBase_of_ncard {α : Type*} [Finite α] (r : ℕ) (I : Set α)
    (hI : I.ncard = r) : (uniform α r).IsBase I := by
  apply Matroid.Indep.isBase_of_forall_insert (by simpa using hI.le)
  intro e he hind
  have heI : e ∉ I := he.2
  rw [uniform_indep_iff, Set.ncard_insert_of_not_mem heI, hI] at hind
  omega

theorem uniform_closure {α : Type*} [Finite α] (r : ℕ) (X : Set α) :
    (uniform α r).closure X = if X.ncard < r then X else Set.univ := by
  split_ifs with hX
  · apply Set.Subset.antisymm
    · intro e he
      by_contra heX
      have hI : (uniform α r).Indep X := hX.le
      have hinsert : (uniform α r).Indep (insert e X) := by
        rw [uniform_indep_iff, Set.ncard_insert_of_not_mem heX]
        omega
      exact heX ((hI.mem_closure_iff'.mp he).2 hinsert)
    · exact (uniform α r).subset_closure X (by simp)
  · obtain ⟨I, hIX, hI⟩ := Set.exists_subset_card_eq (Nat.le_of_not_gt hX)
    simpa using (uniform_isBase_of_ncard r I hI).closure_of_superset hIX

theorem uniform_isFlat_iff {α : Type*} [Finite α] (r : ℕ) (F : Set α) :
    (uniform α r).IsFlat F ↔ F.ncard < r ∨ F = Set.univ := by
  rw [Matroid.isFlat_iff_closure_eq, uniform_closure]
  split_ifs with hF <;> simp [hF, eq_comm]

theorem uniform_eRk {α : Type*} [Finite α] (r : ℕ) (X : Set α) :
    (uniform α r).eRk X = (min r X.ncard : ℕ) := by
  by_cases hX : X.ncard ≤ r
  · rw [(show (uniform α r).Indep X from hX).eRk_eq_encard, min_eq_right hX]
    exact (Set.toFinite X).cast_ncard_eq.symm
  · obtain ⟨I, hIX, hI⟩ := Set.exists_subset_card_eq (Nat.le_of_not_ge hX)
    have hB := (uniform_isBase_of_ncard r I hI).isBasis_of_subset (by simp) hIX
    rw [hB.eRk_eq_encard, ← (Set.toFinite I).cast_ncard_eq, hI,
      min_eq_left (Nat.le_of_not_ge hX)]

def uniform34 : Matroid (Fin 4) := uniform (Fin 4) 3

/-- Pullback along the class map adds one parallel copy of each original element. -/
def thickened34 : Matroid (Fin 4 × Fin 2) := uniform34.comap Prod.fst

@[simp] theorem thickened34_ground : thickened34.E = Set.univ := by
  simp [thickened34, uniform34]

theorem thickened34_indep_iff (I : Set (Fin 4 × Fin 2)) :
    thickened34.Indep I ↔ (Prod.fst '' I).ncard ≤ 3 ∧ Set.InjOn Prod.fst I := by
  simp [thickened34, uniform34]

theorem thickened34_eRk (X : Set (Fin 4 × Fin 2)) :
    thickened34.eRk X = (min 3 (Prod.fst '' X).ncard : ℕ) := by
  rw [thickened34, Matroid.eRk_comap_eq, uniform34, uniform_eRk]

theorem thickened34_closure (X : Set (Fin 4 × Fin 2)) :
    thickened34.closure X =
      if (Prod.fst '' X).ncard < 3 then Prod.fst ⁻¹' (Prod.fst '' X) else Set.univ := by
  rw [thickened34, Matroid.comap_closure_eq, uniform34, uniform_closure]
  split_ifs <;> simp

/-- Actual matroid flats, ordered by inclusion of their underlying sets. -/
abbrev ActualFlats {α : Type*} (M : Matroid α) := {F : Set α // M.IsFlat F}

theorem comap_preimage_isFlat {α β : Type*} (M : Matroid β) (f : α → β)
    (hf : Function.Surjective f) {F : Set β} (hF : M.IsFlat F) :
    (M.comap f).IsFlat (f ⁻¹' F) := by
  apply Matroid.isFlat_iff_closure_eq.mpr
  rw [Matroid.comap_closure_eq, hf.image_preimage, hF.closure]

theorem comap_image_isFlat {α β : Type*} (M : Matroid β) (f : α → β)
    (hf : Function.Surjective f) {F : Set α} (hF : (M.comap f).IsFlat F) :
    M.IsFlat (f '' F) := by
  apply Matroid.isFlat_iff_closure_eq.mpr
  have h := congrArg (Set.image f) hF.closure
  simpa only [Matroid.comap_closure_eq, hf.image_preimage] using h

theorem comap_preimage_image {α β : Type*} (M : Matroid β) (f : α → β)
    (hf : Function.Surjective f) {F : Set α} (hF : (M.comap f).IsFlat F) :
    f ⁻¹' (f '' F) = F := by
  have h := hF.closure
  rw [Matroid.comap_closure_eq, (comap_image_isFlat M f hf hF).closure] at h
  exact h

/-- A surjective parallel extension preserves the entire lattice of actual flats. -/
def comapFlatOrderIso {α β : Type*} (M : Matroid β) (f : α → β)
    (hf : Function.Surjective f) : ActualFlats M ≃o ActualFlats (M.comap f) where
  toFun F := ⟨f ⁻¹' F.val, comap_preimage_isFlat M f hf F.property⟩
  invFun F := ⟨f '' F.val, comap_image_isFlat M f hf F.property⟩
  left_inv F := Subtype.ext (hf.image_preimage _)
  right_inv F := Subtype.ext (comap_preimage_image M f hf F.property)
  map_rel_iff' := by
    intro F G
    exact hf.preimage_subset_preimage_iff

theorem comapFlatOrderIso_eRk {α β : Type*} (M : Matroid β) (f : α → β)
    (hf : Function.Surjective f) (F : ActualFlats M) :
    (M.comap f).eRk (comapFlatOrderIso M f hf F).val = M.eRk F.val := by
  change (M.comap f).eRk (f ⁻¹' F.val) = _
  rw [Matroid.eRk_comap_eq, hf.image_preimage]

/-- The explicit twelve-element finite poset is the actual flat lattice of U(3,4). -/
def uniformFlatOrderIso : Flat ≃o ActualFlats uniform34 where
  toFun F := ⟨(F.val : Set (Fin 4)), by
    simpa [uniform34, uniform_isFlat_iff] using F.property⟩
  invFun F := ⟨F.val.toFinite.toFinset, by
    simpa [uniform34, uniform_isFlat_iff, ← Set.ncard_eq_toFinset_card] using F.property⟩
  left_inv F := by apply Subtype.ext; simp
  right_inv F := by apply Subtype.ext; simp
  map_rel_iff' := by intro F G; exact Finset.coe_subset

theorem uniformFlatOrderIso_eRk (F : Flat) :
    uniform34.eRk (uniformFlatOrderIso F).val = (flatRank F : ℕ) := by
  change (uniform (Fin 4) 3).eRk (F.val : Set (Fin 4)) = _
  simp [uniform_eRk, flatRank]

theorem classMap_surjective : Function.Surjective (Prod.fst : Fin 4 × Fin 2 → Fin 4) :=
  fun i => ⟨(i, 0), rfl⟩

/-- The same poset describes the flats of the genuine two-copy parallel extension. -/
def thickenedFlatOrderIso : Flat ≃o ActualFlats thickened34 :=
  uniformFlatOrderIso.trans (comapFlatOrderIso uniform34 Prod.fst classMap_surjective)

@[simp] theorem thickenedFlatOrderIso_val (F : Flat) :
    (thickenedFlatOrderIso F).val = Prod.fst ⁻¹' (F.val : Set (Fin 4)) := rfl

theorem thickenedFlatOrderIso_eRk (F : Flat) :
    thickened34.eRk (thickenedFlatOrderIso F).val = (flatRank F : ℕ) := by
  exact (comapFlatOrderIso_eRk uniform34 Prod.fst classMap_surjective
    (uniformFlatOrderIso F)).trans (uniformFlatOrderIso_eRk F)

theorem thickened34_eRank : thickened34.eRank = 3 := by
  rw [← Matroid.eRk_univ_eq, thickened34_eRk]
  norm_num [Set.image_univ, classMap_surjective.range_eq, Set.ncard_univ]

/-- All actual ranks are finite, since the ground set has eight elements. -/
theorem thickened34_eRk_lt_top (X : Set (Fin 4 × Fin 2)) :
    thickened34.eRk X < ⊤ := thickened34.eRk_lt_top_of_finite (Set.toFinite X)

theorem thickenedFlatOrderIso_rank (F : Flat) :
    (thickened34.eRk (thickenedFlatOrderIso F).val).toNat = flatRank F := by
  rw [thickenedFlatOrderIso_eRk]
  simp

@[simp] theorem thickenedFlatOrderIso_empty :
    (thickenedFlatOrderIso ⟨∅, Or.inl (by decide)⟩).val = ∅ := by
  simp

@[simp] theorem thickenedFlatOrderIso_univ :
    (thickenedFlatOrderIso ⟨Finset.univ, Or.inr rfl⟩).val = thickened34.E := by
  simp

/-- No added element is a loop. -/
instance thickened34_loopless : thickened34.Loopless where
  loops_eq_empty := by
    change thickened34.closure ∅ = ∅
    simp [thickened34_closure]

/-- The closure of a point is precisely its two-element parallel class. -/
theorem thickened34_singleton_closure (x : Fin 4 × Fin 2) :
    thickened34.closure {x} = Prod.fst ⁻¹' {x.1} := by
  simp [thickened34_closure]

theorem thickened34_class_ncard (i : Fin 4) :
    (Prod.fst ⁻¹' ({i} : Set (Fin 4)) : Set (Fin 4 × Fin 2)).ncard = 2 := by
  have h : (Prod.fst ⁻¹' ({i} : Set (Fin 4)) : Set (Fin 4 × Fin 2)) =
      (fun j : Fin 2 => (i, j)) '' Set.univ := by
    ext ⟨a, b⟩
    simp [Prod.mk_inj, eq_comm]
  rw [h, Set.ncard_image_of_injective _ (fun _ _ h => (Prod.mk_inj.mp h).2)]
  norm_num [Set.ncard_univ]

/-- The two copies of each original point are distinct nonloops forming a circuit. -/
theorem thickened34_parallel_pair (i : Fin 4) :
    thickened34.IsCircuit {(i, 0), (i, 1)} := by
  have he := thickened34.isNonloop_of_loopless (e := (i, 0)) (by simp)
  apply (he.closure_eq_closure_iff_isCircuit_of_ne (f := (i, 1)) (by simp)).mp
  simp only [thickened34_singleton_closure]

end Conjecture574
