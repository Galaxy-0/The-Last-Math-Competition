import Mathlib.Analysis.Convex.Extreme
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Matrix.Notation
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open MeasureTheory Set
noncomputable section
namespace VertexVolume

def body : Set ℝ := Icc 0 2
def standardSimplex : Set ℝ := Icc 0 1
theorem body_convex : Convex ℝ body := convex_Icc 0 2
theorem body_compact : IsCompact body := isCompact_Icc
theorem body_interior : (1 : ℝ) ∈ interior body := by
  simp [body, interior_Icc]
theorem ambient_dimension : Module.finrank ℝ ℝ = 1 := Module.finrank_self ℝ

theorem zero_extreme : (0 : ℝ) ∈ body.extremePoints ℝ := by
  refine mem_extremePoints_iff_left.mpr ⟨by norm_num [body], ?_⟩
  intro x hx y hy hs
  rcases hs with ⟨a,b,ha,hb,hab,he⟩
  simp only [smul_eq_mul] at he
  have hax : 0 ≤ a*x := mul_nonneg ha.le hx.1
  have hby : 0 ≤ b*y := mul_nonneg hb.le hy.1
  have hz : a*x = 0 := by linarith
  exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt ha)

theorem two_extreme : (2 : ℝ) ∈ body.extremePoints ℝ := by
  refine mem_extremePoints_iff_left.mpr ⟨by norm_num [body], ?_⟩
  intro x hx y hy hs
  rcases hs with ⟨a,b,ha,hb,hab,he⟩
  simp only [smul_eq_mul] at he
  have hax : 0 ≤ a*(2-x) := mul_nonneg ha.le (by linarith [hx.2])
  have hby : 0 ≤ b*(2-y) := mul_nonneg hb.le (by linarith [hy.2])
  have hz : a*(2-x) = 0 := by nlinarith
  have hh := (mul_eq_zero.mp hz).resolve_left (ne_of_gt ha)
  linarith

theorem exact_vertices : body.extremePoints ℝ = ({0,2} : Set ℝ) := by
  ext x
  constructor
  · intro hx
    by_cases h0 : x = 0
    · simp [h0]
    by_cases h2 : x = 2
    · simp [h2]
    have hpos : 0 < x := lt_of_le_of_ne hx.1.1 (Ne.symm h0)
    have hlt : x < 2 := lt_of_le_of_ne hx.1.2 h2
    have hs : x ∈ openSegment ℝ (0 : ℝ) 2 := by
      rw [openSegment_eq_Ioo (by norm_num : (0 : ℝ) < 2)]
      exact ⟨hpos,hlt⟩
    have he := hx.2 (by norm_num [body] : (0 : ℝ) ∈ body)
      (by norm_num [body] : (2 : ℝ) ∈ body) hs
    exact False.elim (h0 he.1.symm)
  · simp only [mem_insert_iff, mem_singleton_iff]
    rintro (rfl | rfl)
    · exact zero_extreme
    · exact two_extreme

abbrev Vertex := Fin 2
def vertex : Vertex → ℝ := ![0,2]
theorem vertex_exhaustive : Set.range vertex = body.extremePoints ℝ := by
  rw [exact_vertices]
  ext x
  simp [vertex, Fin.exists_fin_two, or_comm]
theorem vertex_injective : Function.Injective vertex := by
  intro i j h
  fin_cases i <;> fin_cases j <;> norm_num [vertex] at h ⊢

def vertexPairs : Finset (Finset Vertex) := (Finset.univ : Finset Vertex).powersetCard 2
theorem all_vertex_pairs : vertexPairs = {Finset.univ} := by decide
def vertexSimplex (s : Finset Vertex) : Set ℝ := convexHull ℝ (vertex '' (s : Set Vertex))
theorem full_simplex : vertexSimplex Finset.univ = body := by
  unfold vertexSimplex
  have hi : vertex '' ((Finset.univ : Finset Vertex) : Set Vertex) = ({0,2} : Set ℝ) := by
    simpa [exact_vertices] using vertex_exhaustive
  rw [hi, convexHull_pair, segment_eq_Icc (by norm_num : (0 : ℝ) ≤ 2)]
  rfl

def simplexVolume (s : Finset Vertex) : ℝ := (volume (vertexSimplex s)).toReal
def meanVertexVolume : ℝ :=
  (∑ s ∈ vertexPairs, simplexVolume s)/(vertexPairs.card : ℝ)
def standardVolume : ℝ := (volume standardSimplex).toReal
def bodyVolume : ℝ := (volume body).toReal

theorem actual_volumes : bodyVolume = 2 ∧ standardVolume = 1 := by
  norm_num [bodyVolume, standardVolume, body, standardSimplex, Real.volume_Icc]
theorem actual_mean : meanVertexVolume = 2 := by
  simp [meanVertexVolume, all_vertex_pairs, simplexVolume, full_simplex, body, Real.volume_Icc]

def displayedConstant : ℝ :=
  ((Nat.factorial 1 : ℝ)/((Nat.factorial (1-1) : ℝ)*(Nat.factorial 1 : ℝ)))*
    standardVolume/bodyVolume
theorem actual_constant : displayedConstant = 1/2 := by
  norm_num [displayedConstant, actual_volumes.1, actual_volumes.2]

theorem displayed_bound_false :
    ¬ meanVertexVolume ≤ (Nat.choose 1 1 : ℝ)*standardVolume := by
  rw [actual_mean, actual_volumes.2]
  norm_num
theorem constant_bound_false : ¬ meanVertexVolume ≤ displayedConstant*bodyVolume := by
  rw [actual_mean, actual_constant, actual_volumes.1]
  norm_num

theorem counterexample :
    Convex ℝ body ∧ IsCompact body ∧ (1 : ℝ) ∈ interior body ∧
    Module.finrank ℝ ℝ = 1 ∧ body.extremePoints ℝ = ({0,2} : Set ℝ) ∧
    Set.range vertex = body.extremePoints ℝ ∧ Function.Injective vertex ∧
    vertexPairs = {Finset.univ} ∧ vertexSimplex Finset.univ = body ∧
    meanVertexVolume = 2 ∧ standardVolume = 1 ∧
    ¬ meanVertexVolume ≤ (Nat.choose 1 1 : ℝ)*standardVolume :=
  ⟨body_convex, body_compact, body_interior, ambient_dimension, exact_vertices,
    vertex_exhaustive, vertex_injective, all_vertex_pairs, full_simplex,
    actual_mean, actual_volumes.2, displayed_bound_false⟩

#print axioms exact_vertices
#print axioms vertex_exhaustive
#print axioms vertex_injective
#print axioms all_vertex_pairs
#print axioms full_simplex
#print axioms actual_volumes
#print axioms actual_mean
#print axioms actual_constant
#print axioms constant_bound_false
#print axioms counterexample
end VertexVolume
