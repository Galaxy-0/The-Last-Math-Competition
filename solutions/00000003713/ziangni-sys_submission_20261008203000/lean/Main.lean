import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace FilledTriangle
abbrev Vertex := Fin 3
abbrev C0 := Vertex → ℚ
abbrev C1 := Fin 3 → ℚ

/-- All subsets of the three vertices: the actual filled simplex. -/
def faces : Finset (Finset Vertex) := Finset.univ.powerset
lemma faces_downward {s t : Finset Vertex} (_ : s ∈ faces) (_ : t ⊆ s) : t ∈ faces := by
  simp [faces]
lemma face_counts : (faces.filter (fun s => s.card = 1)).card = 3 ∧
    (faces.filter (fun s => s.card = 2)).card = 3 ∧
    (faces.filter (fun s => s.card = 3)).card = 1 := by decide

def edgeStart : Fin 3 → Vertex := ![0,0,1]
def edgeEnd : Fin 3 → Vertex := ![1,2,2]
def edgeFaces (i : Fin 3) : Finset Vertex := {edgeStart i, edgeEnd i}
lemma edges_are_all : Set.range edgeFaces = {s : Finset Vertex | s ∈ faces ∧ s.card = 2} := by
  have h : ∀ s : Finset Vertex, (∃ i, edgeFaces i = s) ↔ s ∈ faces ∧ s.card = 2 := by decide
  ext s
  exact h s

/-- Removing vertices 0,1,2 from [0,1,2] gives edges 12,02,01. -/
def boundaryEdge : Fin 3 → Fin 3 := ![2,1,0]

def d0 : C0 →ₗ[ℚ] C1 where
  toFun f i := f (edgeEnd i) - f (edgeStart i)
  map_add' _ _ := by ext i; simp; ring
  map_smul' _ _ := by ext i; simp [smul_eq_mul]; ring

def d1 : C1 →ₗ[ℚ] ℚ where
  toFun x := ∑ i : Fin 3, (-1 : ℚ)^i.val * x (boundaryEdge i)
  map_add' _ _ := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' a x := by simp [smul_eq_mul, mul_left_comm, Finset.mul_sum]

lemma d1_formula (x : C1) : d1 x = x 0 - x 1 + x 2 := by
  simp [d1, boundaryEdge, Fin.sum_univ_succ]
  ring

lemma d0_formula (f : C0) : d0 f = ![f 1-f 0, f 2-f 0, f 2-f 1] := by
  ext i
  fin_cases i <;> simp [d0, edgeStart, edgeEnd]

lemma cochain_identity (f : C0) : d1 (d0 f) = 0 := by
  rw [d1_formula, d0_formula]
  simp

abbrev Cycles := LinearMap.ker d1

def d0Cycles : C0 →ₗ[ℚ] Cycles := d0.codRestrict Cycles cochain_identity

def Boundaries : Submodule ℚ Cycles := LinearMap.range d0Cycles
abbrev H1 := Cycles ⧸ Boundaries

lemma boundaries_top : Boundaries = ⊤ := by
  apply top_unique
  intro x _
  refine ⟨![0, x.val 0, x.val 1], ?_⟩
  apply Subtype.ext
  rw [d0Cycles, LinearMap.codRestrict_apply, d0_formula]
  have hx : x.val 0 - x.val 1 + x.val 2 = 0 := by
    have hx := x.property
    change d1 x.val = 0 at hx
    rwa [d1_formula] at hx
  ext i
  fin_cases i <;> simp <;> linarith

instance h1Subsingleton : Subsingleton H1 :=
  Submodule.subsingleton_quotient_iff_eq_top.mpr boundaries_top

/-- The actual face-edge coboundary incidence matrix. -/
def B : Matrix (Fin 1) (Fin 3) ℚ := ![![1,-1,1]]
lemma incidence_evaluation (x : C1) : (B.mulVec x) 0 = d1 x := by
  simp [B, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, d1_formula]
  ring

lemma transpose_is_adjoint (x : C1) (y : ℚ) :
    d1 x * y = ∑ i : Fin 3, x i * (B.transpose.mulVec (fun _ => y)) i := by
  simp [B, Matrix.mulVec, Matrix.transpose_apply, dotProduct, Fin.sum_univ_succ, d1_formula]
  ring

/-- Upper, rather than full, Hodge Laplacian: d1^* d1. -/
def upper : C1 →ₗ[ℚ] C1 := (B.transpose * B).mulVecLin

def witness : C1 := ![1,1,0]
lemma witness_nonzero : witness ≠ 0 := by
  intro h
  have := congrFun h 0
  norm_num [witness] at this

lemma witness_upper_zero : upper witness = 0 := by
  ext i
  fin_cases i <;>
    norm_num [upper, witness, B, Matrix.mulVecLin_apply, Matrix.mulVec, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]

theorem upper_kernel_not_cohomology :
    ¬ Nonempty (LinearMap.ker upper ≃ₗ[ℚ] H1) := by
  rintro ⟨φ⟩
  have h : φ ⟨witness, witness_upper_zero⟩ = φ 0 := Subsingleton.elim _ _
  have hh := φ.injective h
  apply witness_nonzero
  exact congrArg Subtype.val hh

end FilledTriangle
#print axioms FilledTriangle.face_counts
#print axioms FilledTriangle.edges_are_all
#print axioms FilledTriangle.cochain_identity
#print axioms FilledTriangle.boundaries_top
#print axioms FilledTriangle.transpose_is_adjoint
#print axioms FilledTriangle.witness_upper_zero
#print axioms FilledTriangle.upper_kernel_not_cohomology
