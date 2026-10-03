import Std

namespace Conjecture459

def EquivalenceLaws {n : Nat} (R : Fin n → Fin n → Prop) : Prop :=
  (∀ x, R x x) ∧ (∀ x y, R x y → R y x) ∧
  (∀ x y z, R x y → R y z → R x z)

/-- An actual set partition, represented by its equivalence relation. -/
structure Partition (n : Nat) where
  rel : Fin n → Fin n → Prop
  laws : EquivalenceLaws rel

theorem Partition.ext {n : Nat} (P Q : Partition n)
    (h : ∀ x y, P.rel x y ↔ Q.rel x y) : P = Q := by
  have hr : P.rel = Q.rel := funext (fun x => funext (fun y => propext (h x y)))
  cases P
  cases Q
  cases hr
  rfl

/-- No two distinct blocks have alternating endpoints in the linear/cyclic order. -/
def Noncrossing {n : Nat} (R : Fin n → Fin n → Prop) : Prop :=
  ∀ a b c d, a < b → b < c → c < d → R a c → R b d → R a b

def modelRel (b : Bool) (x y : Fin 2) : Prop := x = y ∨ b = true

def model (b : Bool) : Partition 2 where
  rel := modelRel b
  laws := (by simp only [EquivalenceLaws, modelRel]; decide : ∀ b, EquivalenceLaws (modelRel b)) b

/-- Every arbitrary Prop-valued equivalence relation on two points occurs. -/
theorem every_partition_encoded (P : Partition 2) : ∃ b, P = model b := by
  classical
  have cases2 : ∀ x : Fin 2, x = 0 ∨ x = 1 := by decide
  by_cases h : P.rel 0 1
  · refine ⟨true, Partition.ext P (model true) ?_⟩
    intro x y
    have h10 := P.laws.2.1 0 1 h
    rcases cases2 x with rfl | rfl <;> rcases cases2 y with rfl | rfl <;>
      simp [model, modelRel, P.laws.1, h, h10]
  · refine ⟨false, Partition.ext P (model false) ?_⟩
    intro x y
    have h10 : ¬ P.rel 1 0 := fun h10 => h (P.laws.2.1 1 0 h10)
    rcases cases2 x with rfl | rfl <;> rcases cases2 y with rfl | rfl <;>
      simp [model, modelRel, P.laws.1, h, h10]

theorem model_injective (b c : Bool) (h : model b = model c) : b = c := by
  have he := congrArg (fun P : Partition 2 => P.rel 0 1) h
  cases b <;> cases c <;> simp [model, modelRel] at he ⊢

theorem every_partition_noncrossing (P : Partition 2) : Noncrossing P.rel := by
  obtain ⟨b, rfl⟩ := every_partition_encoded P
  exact (by simp only [Noncrossing, modelRel]; decide : ∀ b, Noncrossing (modelRel b)) b

def halfIndex (x : Fin 4) : Fin 2 := ⟨x.val / 2, by omega⟩

/-- White positions 0,2 carry P; black positions 1,3 carry Q. -/
def interleave (P Q : Partition 2) (x y : Fin 4) : Prop :=
  x.val % 2 = y.val % 2 ∧
    (if x.val % 2 = 0 then P.rel (halfIndex x) (halfIndex y)
     else Q.rel (halfIndex x) (halfIndex y))

theorem interleave_is_partition (P Q : Partition 2) : EquivalenceLaws (interleave P Q) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    refine ⟨rfl, ?_⟩
    split <;> first | exact P.laws.1 _ | exact Q.laws.1 _
  · intro x y h
    refine ⟨h.1.symm, ?_⟩
    have hc := h.1
    have hr := h.2
    by_cases hx : x.val % 2 = 0
    · have hy : y.val % 2 = 0 := hc ▸ hx
      simp only [hx, hy, if_pos] at hr ⊢
      exact P.laws.2.1 _ _ hr
    · have hy : y.val % 2 ≠ 0 := fun hy => hx (hc.trans hy)
      simp only [hx, hy, if_neg] at hr ⊢
      exact Q.laws.2.1 _ _ hr
  · intro x y z hxy hyz
    refine ⟨hxy.1.trans hyz.1, ?_⟩
    have hr := hxy.2
    have hs := hyz.2
    by_cases hx : x.val % 2 = 0
    · have hy : y.val % 2 = 0 := hxy.1 ▸ hx
      simp only [hx, hy, if_pos] at hr hs ⊢
      exact P.laws.2.2 _ _ _ hr hs
    · have hy : y.val % 2 ≠ 0 := fun hy => hx (hxy.1.trans hy)
      simp only [hx, hy, if_neg] at hr hs ⊢
      exact Q.laws.2.2 _ _ _ hr hs

def Refines (P Q : Partition 2) : Prop := ∀ x y, P.rel x y → Q.rel x y

/-- The standard coarsest-partition definition of Kreweras complement. -/
def IsKrewerasComplement (P Q : Partition 2) : Prop :=
  Noncrossing P.rel ∧ Noncrossing Q.rel ∧ Noncrossing (interleave P Q) ∧
    ∀ R : Partition 2, Noncrossing R.rel → Noncrossing (interleave P R) → Refines R Q

theorem kreweras_models (b : Bool) : IsKrewerasComplement (model b) (model (!b)) := by
  refine ⟨every_partition_noncrossing _, every_partition_noncrossing _, ?_, ?_⟩
  · exact (by simp only [Noncrossing, interleave, model, modelRel, halfIndex]; decide : ∀ b, Noncrossing (interleave (model b) (model (!b)))) b
  · intro R _ hR
    obtain ⟨c, rfl⟩ := every_partition_encoded R
    exact (by
      intro b c
      cases b <;> cases c <;>
        simp only [Noncrossing, interleave, Refines, model, modelRel, halfIndex] <;> decide : ∀ b c,
      Noncrossing (interleave (model b) (model c)) → Refines (model c) (model (!b))) b c hR

theorem kreweras_unique (P Q R : Partition 2)
    (hQ : IsKrewerasComplement P Q) (hR : IsKrewerasComplement P R) : Q = R := by
  have hqr := hR.2.2.2 Q hQ.2.1 hQ.2.2.1
  have hrq := hQ.2.2.2 R hR.2.1 hR.2.2.1
  apply Partition.ext
  intro x y
  exact ⟨hqr x y, hrq x y⟩

theorem every_partition_has_complement (P : Partition 2) :
    ∃ Q, IsKrewerasComplement P Q := by
  obtain ⟨b, rfl⟩ := every_partition_encoded P
  exact ⟨model (!b), kreweras_models b⟩

/-- There are no fixed points on NC_2, against the actual maximality definition. -/
theorem no_fixed_points (P : Partition 2) : ¬ IsKrewerasComplement P P := by
  obtain ⟨b, rfl⟩ := every_partition_encoded P
  intro h
  have he := model_injective b (!b) (kreweras_unique _ _ _ h (kreweras_models b))
  cases b <;> contradiction

def NoSingletons {n : Nat} (P : Partition n) : Prop :=
  ∀ x, ∃ y, y ≠ x ∧ P.rel x y

def Arc {n : Nat} (P : Partition n) (a b : Fin n) : Prop :=
  a < b ∧ P.rel a b ∧ ∀ c, a < c → c < b → ¬ P.rel a c

/-- Three-crossing avoidance in the usual consecutive-block-element arc diagram. -/
def ThreeNoncrossing {n : Nat} (P : Partition n) : Prop :=
  ∀ a b c d e f : Fin n,
    a < b → b < c → c < d → d < e → e < f →
    ¬ (Arc P a d ∧ Arc P b e ∧ Arc P c f)

def FixedPoints := {P : Partition 2 // IsKrewerasComplement P P}
def TargetObjects := {P : Partition 2 // ThreeNoncrossing P ∧ NoSingletons P}

def targetWitness : TargetObjects := ⟨model true, by
  constructor
  · intro a b c d e f hab hbc hcd hde hef
    have ha := a.isLt
    have hb := b.isLt
    have hc := c.isLt
    omega
  · intro x
    have hx : x = 0 ∨ x = 1 := (by decide : ∀ x : Fin 2, x = 0 ∨ x = 1) x
    rcases hx with rfl | rfl
    · exact ⟨1, by decide, Or.inr rfl⟩
    · exact ⟨0, by decide, Or.inr rfl⟩⟩

theorem no_singletons_forces_one_block (P : Partition 2) (h : NoSingletons P) :
    P = model true := by
  obtain ⟨b, rfl⟩ := every_partition_encoded P
  cases b
  · obtain ⟨y, hy, hrel⟩ := h 0
    have he : (0 : Fin 2) = y := by simpa only [model, modelRel, Bool.false_eq_true, or_false] using hrel
    exact False.elim (hy he.symm)
  · rfl

theorem target_unique (P : TargetObjects) : P = targetWitness := by
  apply Subtype.ext
  exact no_singletons_forces_one_block P.val P.property.2

def Surjective {X Y : Type} (f : X → Y) : Prop := ∀ y, ∃ x, f x = y

/-- Even a surjection cannot exist, hence neither a bijection nor a
rank-preserving bijection can exist at n=2. -/
theorem conjecture459_refuted : ¬ ∃ f : FixedPoints → TargetObjects, Surjective f := by
  rintro ⟨f, hf⟩
  obtain ⟨x, _⟩ := hf targetWitness
  exact no_fixed_points x.val x.property

#print axioms every_partition_encoded
#print axioms interleave_is_partition
#print axioms kreweras_models
#print axioms kreweras_unique
#print axioms no_fixed_points
#print axioms target_unique
#print axioms conjecture459_refuted

end Conjecture459
