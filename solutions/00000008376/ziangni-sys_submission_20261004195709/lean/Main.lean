import Mathlib.Algebra.Tropical.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Finite.Card
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

open Set
open scoped Pointwise
noncomputable section
namespace TropicalStabilizer
abbrev I := Fin 3
abbrev G := Equiv.Perm I
abbrev E := I → ℝ
abbrev T := Tropical (WithTop ℝᵒᵈ)

-- X0 + X1 + X2 in the max-plus tropical semiring.
def polynomial : MvPolynomial I T := MvPolynomial.X 0 + MvPolynomial.X 1 + MvPolynomial.X 2
def tropicalCoordinates (x:E) (i:I) : T := Tropical.trop ((↑(show ℝᵒᵈ from x i)) : WithTop ℝᵒᵈ)
def height (x:E) : ℝ := max (max (x 0) (x 1)) (x 2)

theorem actual_polynomial_evaluation (x:E) :
    Tropical.untrop (MvPolynomial.eval (tropicalCoordinates x) polynomial) =
      ((↑(show ℝᵒᵈ from height x)) : WithTop ℝᵒᵈ) := by
  simp [polynomial,tropicalCoordinates,height,Tropical.untrop_add]
  rfl

def Corner : Set E := {x | ∃i j:I, i≠j ∧ x i=height x ∧ x j=height x}
-- A cell is specified by precisely the monomials attaining the maximum.
def Cell (S:Set I) : Set E := {x | ∀i, x i=height x ↔ i∈S}
def origin : E := fun _ => 0

instance coordinateAction : MulAction G E where
  smul σ x := fun i => x (σ.symm i)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp] theorem action_apply (σ:G) (x:E) (i:I) : (σ • x) i=x (σ.symm i) := rfl
@[simp] theorem action_at_image (σ:G) (x:E) (i:I) : (σ • x) (σ i)=x i := by simp
@[simp] theorem height_origin : height origin=0 := by norm_num [height,origin]
@[simp] theorem origin_fixed (σ:G) : σ • origin=origin := rfl

theorem coordinate_le_height (x:E) (i:I) : x i≤height x := by
  fin_cases i
  · exact (le_max_left _ _).trans (le_max_left _ _)
  · exact (le_max_right _ _).trans (le_max_left _ _)
  · exact le_max_right _ _

theorem height_le_iff (x:E) (a:ℝ) : height x≤a ↔ ∀i,x i≤a := by
  constructor
  · intro h i; exact (coordinate_le_height x i).trans h
  · intro h; exact max_le (max_le (h 0) (h 1)) (h 2)

theorem height_invariant (σ:G) (x:E) : height (σ • x)=height x := by
  apply le_antisymm
  · apply (height_le_iff _ _).mpr
    intro i; exact coordinate_le_height x (σ.symm i)
  · apply (height_le_iff _ _).mpr
    intro i; simpa using coordinate_le_height (σ • x) (σ i)

theorem corner_invariant (σ:G) (x:E) : σ • x∈Corner ↔ x∈Corner := by
  constructor
  · rintro ⟨i,j,hij,hi,hj⟩
    refine ⟨σ.symm i,σ.symm j,fun h => hij (σ.symm.injective h),?_,?_⟩
    · simpa [height_invariant] using hi
    · simpa [height_invariant] using hj
  · rintro ⟨i,j,hij,hi,hj⟩
    refine ⟨σ i,σ j,fun h => hij (σ.injective h),?_,?_⟩ <;> simpa [height_invariant]

theorem cell_action (σ:G) (S:Set I) (x:E) : σ • x∈Cell (σ '' S) ↔ x∈Cell S := by
  constructor
  · intro h i
    have hi:=h (σ i)
    simpa [height_invariant] using hi
  · intro h i
    rw [height_invariant,action_apply,h]
    constructor
    · intro hi; exact ⟨σ.symm i,hi,σ.apply_symm_apply i⟩
    · rintro ⟨j,hj,hji⟩; simpa [←hji] using hj

theorem central_cell_exact (x:E) : x∈Cell univ ↔ ∀i,x i=x 0 := by
  constructor
  · intro h i; exact (h i).mpr (mem_univ i) |>.trans ((h 0).mpr (mem_univ 0)).symm
  · intro h i
    have hh : height x=x 0 := by simp [height,h]
    simp [hh,h]

theorem central_cell_in_corner : Cell univ⊆Corner := by
  intro x hx
  exact ⟨0,1,by decide,(hx 0).mpr (mem_univ 0),(hx 1).mpr (mem_univ 1)⟩

theorem origin_in_cell : origin∈Cell univ := by
  apply (central_cell_exact _).mpr
  intro i; rfl

theorem origin_in_corner : origin∈Corner := central_cell_in_corner origin_in_cell

theorem central_cell_invariant (σ:G) (x:E) : σ • x∈Cell univ ↔ x∈Cell univ := by
  simpa using cell_action σ univ x

theorem cells_cover_corner (x:E) : x∈Corner ↔
    ∃S:Set I, (∃i∈S,∃j∈S,i≠j) ∧ x∈Cell S := by
  constructor
  · rintro ⟨i,j,hij,hi,hj⟩
    exact ⟨{k | x k=height x},⟨i,hi,j,hj,hij⟩,fun _ => Iff.rfl⟩
  · rintro ⟨S,⟨i,hi,j,hj,hij⟩,hx⟩
    exact ⟨i,j,hij,(hx i).mpr hi,(hx j).mpr hj⟩

theorem height_translate (x:E) (c:ℝ) : height (fun i => x i+c)=height x+c := by
  apply le_antisymm
  · apply (height_le_iff _ _).mpr
    intro i; exact add_le_add_right (coordinate_le_height x i) c
  · have h : height x≤height (fun i => x i+c)-c := by
      apply (height_le_iff _ _).mpr
      intro i
      have hi:=coordinate_le_height (fun j => x j+c) i
      linarith
    linarith

theorem corner_translation_invariant (x:E) (c:ℝ) : (fun i => x i+c)∈Corner ↔ x∈Corner := by
  simp [Corner,height_translate]

theorem central_cell_fixed (σ:G) : σ • Cell univ=Cell univ := by
  change (fun x:E => σ • x) '' Cell univ=Cell univ
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩; exact (central_cell_invariant σ y).mpr hy
  · intro hx
    refine ⟨σ⁻¹ • x,(central_cell_invariant σ⁻¹ x).mpr hx,?_⟩
    simp

theorem cell_stabilizer_top : MulAction.stabilizer G (Cell univ)=⊤ := by
  apply top_unique
  intro σ _
  exact central_cell_fixed σ

theorem point_stabilizer_top : MulAction.stabilizer G origin=⊤ := by
  apply top_unique
  intro σ _
  exact origin_fixed σ

noncomputable def stabilizerEquiv : MulAction.stabilizer G origin ≃ G where
  toFun := Subtype.val
  invFun σ := ⟨σ,origin_fixed σ⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem point_stabilizer_card : Nat.card (MulAction.stabilizer G origin)=6 := by
  rw [Nat.card_congr stabilizerEquiv,Nat.card_eq_fintype_card,Fintype.card_perm]
  norm_num [Nat.factorial]

theorem claimed_group_card : Nat.card (Equiv.Perm (Fin 2))=2 := by
  rw [Nat.card_eq_fintype_card,Fintype.card_perm]
  norm_num [Nat.factorial]

theorem stabilizer_exceeds_claim : Nat.card (Equiv.Perm (Fin 2)) <
    Nat.card (MulAction.stabilizer G origin) := by
  rw [point_stabilizer_card,claimed_group_card]; norm_num

theorem no_stabilizer_isomorphism : ¬Nonempty (MulAction.stabilizer G origin ≃* Equiv.Perm (Fin 2)) := by
  rintro ⟨e⟩
  have h:=Nat.card_congr e.toEquiv
  rw [point_stabilizer_card,claimed_group_card] at h
  norm_num at h

-- Tropical projective coordinates quotient out common additive translation.
def diagonalSetoid : Setoid E where
  r x y := ∃c:ℝ,∀i,y i=x i+c
  iseqv := {
    refl := fun x => ⟨0,by intro i; simp⟩
    symm := by rintro x y ⟨c,h⟩; exact ⟨-c,by intro i; rw [h]; ring⟩
    trans := by rintro x y z ⟨c,h⟩ ⟨d,k⟩; exact ⟨c+d,by intro i; rw [k,h]; ring⟩ }
abbrev Projective := Quotient diagonalSetoid
def project (x:E) : Projective := Quotient.mk diagonalSetoid x

def projectiveAction (σ:G) : Projective → Projective := Quotient.map (fun x:E => σ • x)
  (by rintro x y ⟨c,h⟩; exact ⟨c,fun i => h (σ.symm i)⟩)

instance : MulAction G Projective where
  smul := projectiveAction
  one_smul := by intro q; induction q using Quotient.inductionOn with | h x => rfl
  mul_smul := by intro σ τ q; induction q using Quotient.inductionOn with | h x => rfl

@[simp] theorem project_action (σ:G) (x:E) : σ • project x=project (σ • x) := rfl
@[simp] theorem projective_origin_fixed (σ:G) : σ • project origin=project origin := by simp

theorem central_cell_projects_to_one_point : project '' Cell univ={project origin} := by
  ext q
  constructor
  · rintro ⟨x,hx,rfl⟩
    apply mem_singleton_iff.mpr
    apply Quotient.sound
    refine ⟨-x 0,?_⟩
    intro i
    have h: x i=x 0 := (central_cell_exact x).mp hx i
    simp [origin,h]
  · rintro rfl; exact ⟨origin,origin_in_cell,rfl⟩

theorem projective_stabilizer_top : MulAction.stabilizer G (project origin)=⊤ := by
  apply top_unique
  intro σ _
  exact projective_origin_fixed σ

noncomputable def projectiveStabilizerEquiv : MulAction.stabilizer G (project origin) ≃ G where
  toFun := Subtype.val
  invFun σ := ⟨σ,projective_origin_fixed σ⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem projective_stabilizer_card : Nat.card (MulAction.stabilizer G (project origin))=6 := by
  rw [Nat.card_congr projectiveStabilizerEquiv,Nat.card_eq_fintype_card,Fintype.card_perm]
  norm_num [Nat.factorial]

theorem counterexample : origin∈Corner ∧ origin∈Cell univ ∧
    MulAction.stabilizer G origin=⊤ ∧
    Nat.card (Equiv.Perm (Fin 2)) < Nat.card (MulAction.stabilizer G origin) ∧
    Nat.card (Equiv.Perm (Fin 2)) < Nat.card (MulAction.stabilizer G (project origin)) := by
  refine ⟨origin_in_corner,origin_in_cell,point_stabilizer_top,stabilizer_exceeds_claim,?_⟩
  rw [claimed_group_card,projective_stabilizer_card]; norm_num

#print axioms actual_polynomial_evaluation
#print axioms corner_invariant
#print axioms cell_action
#print axioms central_cell_exact
#print axioms cells_cover_corner
#print axioms corner_translation_invariant
#print axioms cell_stabilizer_top
#print axioms point_stabilizer_card
#print axioms no_stabilizer_isomorphism
#print axioms central_cell_projects_to_one_point
#print axioms projective_stabilizer_card
#print axioms counterexample
end TropicalStabilizer
