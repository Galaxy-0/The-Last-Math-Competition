import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Tactic

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Filter
namespace MatchingSpectra
abbrev Vertex (m : ℕ) := Fin (m+1) × Fin 2
abbrev Functions (m : ℕ) := Vertex m → ℝ

def flip : Fin 2 → Fin 2 := ![1,0]
lemma unequal_iff_flip (i j : Fin 2) : i ≠ j ↔ j = flip i := by
  fin_cases i <;> fin_cases j <;> decide

def graph (m : ℕ) : SimpleGraph (Vertex m) where
  Adj v w := v.1 = w.1 ∧ v.2 ≠ w.2
  symm v w h := ⟨h.1.symm, Ne.symm h.2⟩
  loopless v h := h.2 rfl

instance graphDecidable (m : ℕ) : DecidableRel (graph m).Adj :=
  fun v w => inferInstanceAs (Decidable (v.1 = w.1 ∧ v.2 ≠ w.2))

lemma neighbors (m : ℕ) (v : Vertex m) :
    (graph m).neighborFinset v = {(v.1, flip v.2)} := by
  ext w
  simp only [SimpleGraph.mem_neighborFinset, graph, Finset.mem_singleton]
  rw [unequal_iff_flip]
  constructor
  · rintro ⟨hc, hi⟩
    exact Prod.ext hc.symm hi
  · intro h
    cases h
    exact ⟨rfl,rfl⟩

lemma degree_one (m : ℕ) (v : Vertex m) : (graph m).degree v = 1 := by
  simp [SimpleGraph.degree, neighbors]

lemma vertex_count (m : ℕ) : Fintype.card (Vertex m) = 2*(m+1) := by
  simp [Vertex, Nat.mul_comm]

lemma arbitrarily_many_vertices (N : ℕ) : N < Fintype.card (Vertex N) := by
  rw [vertex_count]
  omega

/-- I-D^{-1}A using genuine neighbor sums; D=I because every degree is 1. -/
def normalizedLap (m : ℕ) : Functions m →ₗ[ℝ] Functions m where
  toFun f v := f v - ∑ w ∈ (graph m).neighborFinset v, f w
  map_add' f h := by ext v; simp [Finset.sum_add_distrib]; ring
  map_smul' a f := by ext v; simp [neighbors, smul_eq_mul]; ring

lemma normalized_formula (m : ℕ) (f : Functions m) (v : Vertex m) :
    normalizedLap m f v = f v - f (v.1, flip v.2) := by
  simp [normalizedLap, neighbors]

/-- Invertible coordinates for the complete symmetric/antisymmetric basis. -/
def coordinates (m : ℕ) : Functions m ≃ₗ[ℝ] Functions m where
  toFun f v := if v.2 = 0 then (f (v.1,0)+f (v.1,1))/2
    else (f (v.1,0)-f (v.1,1))/2
  invFun c v := c (v.1,0) + (if v.2 = 0 then 1 else -1) * c (v.1,1)
  left_inv f := by
    ext ⟨c,i⟩
    fin_cases i <;> simp <;> ring
  right_inv f := by
    ext ⟨c,i⟩
    fin_cases i <;> simp <;> ring
  map_add' f h := by
    ext ⟨c,i⟩
    fin_cases i <;> simp <;> ring
  map_smul' a f := by
    ext ⟨c,i⟩
    fin_cases i <;> simp [smul_eq_mul] <;> ring

def eigenBasis (m : ℕ) : Basis (Vertex m) ℝ (Functions m) :=
  Basis.ofEquivFun (coordinates m)
def eigenvalue (m : ℕ) (v : Vertex m) : ℝ := if v.2 = 0 then 0 else 2

lemma diagonalization (m : ℕ) (f : Functions m) (v : Vertex m) :
    coordinates m (normalizedLap m f) v = eigenvalue m v * coordinates m f v := by
  rcases v with ⟨c,i⟩
  fin_cases i <;> simp [coordinates, normalized_formula, eigenvalue, flip] <;> ring

lemma basis_coordinates (m : ℕ) (v : Vertex m) :
    coordinates m (eigenBasis m v) = Pi.single v 1 := by
  simp [eigenBasis, Basis.coe_ofEquivFun]

lemma actual_eigenbasis (m : ℕ) (v : Vertex m) :
    normalizedLap m (eigenBasis m v) = eigenvalue m v • eigenBasis m v := by
  apply (coordinates m).injective
  ext w
  rw [diagonalization, map_smul]
  simp only [basis_coordinates, Pi.smul_apply, smul_eq_mul]
  by_cases h : v = w
  · subst w; simp
  · simp [Pi.single_apply, h]

lemma multiplicities (m : ℕ) :
    (Finset.univ.filter (fun v : Vertex m => eigenvalue m v = 0)).card = m+1 ∧
    (Finset.univ.filter (fun v : Vertex m => eigenvalue m v = 2)).card = m+1 := by
  have h0 : Finset.univ.filter (fun v : Vertex m => eigenvalue m v = 0) =
      Finset.univ ×ˢ ({0} : Finset (Fin 2)) := by
    ext ⟨c,i⟩
    fin_cases i <;> simp [eigenvalue]
  have h2 : Finset.univ.filter (fun v : Vertex m => eigenvalue m v = 2) =
      Finset.univ ×ˢ ({1} : Finset (Fin 2)) := by
    ext ⟨c,i⟩
    fin_cases i <;> simp [eigenvalue]
  simp [h0,h2]

def limitMeasure : Measure ℝ :=
  (1/2 : ℝ≥0∞) • Measure.dirac 0 + (1/2 : ℝ≥0∞) • Measure.dirac 2

/-- Average of the two genuine eigenvalues of each component, then over
all m+1 equal-sized components: the ordinary empirical spectral measure. -/
def empiricalMeasure (m : ℕ) : Measure ℝ :=
  ((m+1 : ℝ≥0∞)⁻¹) • ∑ c : Fin (m+1),
    ∑ i : Fin 2, (1/2 : ℝ≥0∞) • Measure.dirac (eigenvalue m (c,i))

lemma empirical_constant (m : ℕ) : empiricalMeasure m = limitMeasure := by
  have hs : (∑ c : Fin (m+1), ∑ i : Fin 2,
      (1/2 : ℝ≥0∞) • Measure.dirac (eigenvalue m (c,i))) =
      (m+1) • limitMeasure := by
    simp [eigenvalue, Fin.sum_univ_two, limitMeasure]
  unfold empiricalMeasure
  rw [hs, ← Nat.cast_smul_eq_nsmul ℝ≥0∞, smul_smul]
  rw [Nat.cast_add, Nat.cast_one]
  rw [ENNReal.inv_mul_cancel (by simp) (by simp), one_smul]

lemma limit_probability : IsProbabilityMeasure limitMeasure := by
  constructor
  simpa [limitMeasure, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply] using ENNReal.inv_two_add_inv_two

def limitProbability : ProbabilityMeasure ℝ := ⟨limitMeasure, limit_probability⟩
def empiricalProbability (m : ℕ) : ProbabilityMeasure ℝ :=
  ⟨empiricalMeasure m, by rw [empirical_constant]; exact limit_probability⟩

lemma probability_constant (m : ℕ) : empiricalProbability m = limitProbability := by
  apply Subtype.ext
  exact empirical_constant m

theorem actual_weak_limit : Tendsto empiricalProbability atTop (nhds limitProbability) := by
  exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => limitProbability) atTop (nhds limitProbability)).congr
    (fun m => (probability_constant m).symm)

/-- Standard topological measure support: every open neighborhood has
nonzero measure. This pin has no prepackaged Measure.support declaration. -/
def measureSupport (μ : Measure ℝ) : Set ℝ :=
  {x | ∀ U : Set ℝ, IsOpen U → x ∈ U → μ U ≠ 0}

lemma missing_neighborhood : limitMeasure (Set.Ioo (1/2 : ℝ) (3/2)) = 0 := by
  norm_num [limitMeasure, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply]

theorem support_not_full_interval : measureSupport limitMeasure ≠ Set.Icc (0 : ℝ) 2 := by
  intro h
  have h1 : (1 : ℝ) ∈ measureSupport limitMeasure := by rw [h]; norm_num
  exact h1 _ isOpen_Ioo (by norm_num) missing_neighborhood

end MatchingSpectra
#print axioms MatchingSpectra.degree_one
#print axioms MatchingSpectra.vertex_count
#print axioms MatchingSpectra.actual_eigenbasis
#print axioms MatchingSpectra.multiplicities
#print axioms MatchingSpectra.empirical_constant
#print axioms MatchingSpectra.actual_weak_limit
#print axioms MatchingSpectra.missing_neighborhood
#print axioms MatchingSpectra.support_not_full_interval
