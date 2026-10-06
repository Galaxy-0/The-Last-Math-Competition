import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Real.Sqrt
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Tactic

/-! A counterexample to conjecture 00000002161. -/
namespace Conjecture2161

/-- A finite simple signed graph, encoded by its ordinary underlying simple graph
and its real signed adjacency matrix. An edge has sign +1 or -1 and all other
entries, including the diagonal, are zero. -/
structure SignedGraph (V : Type*) where
  graph : SimpleGraph V
  adjacency : Matrix V V ℝ
  symmetric : ∀ i j, adjacency i j = adjacency j i
  edge_sign : ∀ i j, graph.Adj i j → adjacency i j = 1 ∨ adjacency i j = -1
  nonedge_zero : ∀ i j, ¬ graph.Adj i j → adjacency i j = 0

/-- The positive inertia index counts positive eigenvalues with their algebraic
multiplicity: `Polynomial.roots` is a multiset of roots, with multiplicity, of
the characteristic polynomial det(tI-A). For a real symmetric matrix all roots
are real. Thus this is the usual positive inertia index. -/
noncomputable def positiveInertiaIndex {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) : ℕ := by
  classical
  exact (A.charpoly.roots.filter (0 < ·)).card

/-- The ordinary path 0--1--2--3. -/
def pathGraph : SimpleGraph (Fin 4) where
  Adj i j := i.val + 1 = j.val ∨ j.val + 1 = i.val
  symm := by intro i j h; exact h.symm
  loopless := by intro i h; omega

instance pathAdjDecidable : DecidableRel pathGraph.Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- All three edges carry sign +1. -/
def pathAdjacency : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 1, 0, 0; 1, 0, 1, 0; 0, 1, 0, 1; 0, 0, 1, 0]

theorem pathAdjacency_symmetric : ∀ i j, pathAdjacency i j = pathAdjacency j i := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [pathAdjacency]

theorem pathAdjacency_edge_sign : ∀ i j, pathGraph.Adj i j →
    pathAdjacency i j = 1 ∨ pathAdjacency i j = -1 := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [pathGraph, pathAdjacency]

theorem pathAdjacency_nonedge_zero : ∀ i j, ¬ pathGraph.Adj i j →
    pathAdjacency i j = 0 := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [pathGraph, pathAdjacency]

def signedPath : SignedGraph (Fin 4) where
  graph := pathGraph
  adjacency := pathAdjacency
  symmetric := pathAdjacency_symmetric
  edge_sign := pathAdjacency_edge_sign
  nonedge_zero := pathAdjacency_nonedge_zero

theorem path_not_complete : pathGraph ≠ ⊤ := by
  intro h
  have ha : pathGraph.Adj 0 2 := by rw [h]; decide
  norm_num [pathGraph] at ha

/-- Independence means that no two distinct vertices in the set are adjacent. -/
def IsIndependent {V : Type*} (G : SimpleGraph V) (s : Finset V) : Prop :=
  ∀ u ∈ s, ∀ v ∈ s, u ≠ v → ¬ G.Adj u v

instance independentDecidable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) :
    Decidable (IsIndependent G s) := by
  unfold IsIndependent
  infer_instance

/-- The maximum cardinality among all independent subsets of a finite graph. -/
def independenceNumber {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  ((Finset.univ : Finset (Finset V)).filter (IsIndependent G)).sup Finset.card

/-- The maximum really bounds every independent set. -/
theorem independent_card_le_independenceNumber {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) (hs : IsIndependent G s) :
    s.card ≤ independenceNumber G := by
  exact Finset.le_sup (by simp [hs])

/-- Any common cardinality bound is a bound for the maximum. -/
theorem independenceNumber_le_iff {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    independenceNumber G ≤ k ↔ ∀ s : Finset V, IsIndependent G s → s.card ≤ k := by
  simp [independenceNumber, Finset.sup_le_iff]

theorem path_independent_witness : IsIndependent pathGraph ({0, 2} : Finset (Fin 4)) := by
  decide

theorem path_independent_upper : ∀ s : Finset (Fin 4),
    IsIndependent pathGraph s → s.card ≤ 2 := by
  decide

theorem path_independence_number : independenceNumber pathGraph = 2 := by
  apply Nat.le_antisymm
  · exact (independenceNumber_le_iff pathGraph 2).mpr path_independent_upper
  · have h := independent_card_le_independenceNumber pathGraph
      ({0, 2} : Finset (Fin 4)) path_independent_witness
    simpa using h

open Polynomial

theorem path_characteristic_polynomial :
    pathAdjacency.charpoly = X ^ 4 - 3 * X ^ 2 + (1 : ℝ[X]) := by
  simp [Matrix.charpoly, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Matrix.det_fin_three, Matrix.det_fin_two, Matrix.det_fin_one,
    Matrix.charmatrix_apply, Matrix.diagonal, Matrix.submatrix, pathAdjacency, Fin.succAbove]
  ring

noncomputable def positiveRootLarge : ℝ := (Real.sqrt 5 + 1) / 2
noncomputable def positiveRootSmall : ℝ := (Real.sqrt 5 - 1) / 2

theorem sqrt_five_gt_one : (1 : ℝ) < Real.sqrt 5 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hnonneg := Real.sqrt_nonneg (5 : ℝ)
  nlinarith

theorem positiveRootLarge_pos : 0 < positiveRootLarge := by
  unfold positiveRootLarge
  linarith [sqrt_five_gt_one]

theorem positiveRootSmall_pos : 0 < positiveRootSmall := by
  unfold positiveRootSmall
  linarith [sqrt_five_gt_one]

/-- The list repeats each eigenvalue according to its algebraic multiplicity. -/
noncomputable def pathEigenvalues : Multiset ℝ :=
  {positiveRootLarge, positiveRootSmall, -positiveRootLarge, -positiveRootSmall}

theorem path_charpoly_factorization : pathAdjacency.charpoly =
    (pathEigenvalues.map fun r => X - C r).prod := by
  rw [path_characteristic_polynomial]
  apply Polynomial.funext
  intro x
  simp [pathEigenvalues, positiveRootLarge, positiveRootSmall]
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  linear_combination -(1 / 16) * ((Real.sqrt 5)^2 - 8*x^2 + 3) * h

theorem path_roots : pathAdjacency.charpoly.roots = pathEigenvalues := by
  rw [path_charpoly_factorization, Polynomial.roots_multiset_prod_X_sub_C]

theorem path_positive_inertia : positiveInertiaIndex pathAdjacency = 2 := by
  unfold positiveInertiaIndex
  rw [path_roots]
  simp [Multiset.filter_singleton, pathEigenvalues, positiveRootLarge_pos, positiveRootSmall_pos,
    not_lt_of_ge (neg_nonpos.mpr (le_of_lt positiveRootLarge_pos)),
    not_lt_of_ge (neg_nonpos.mpr (le_of_lt positiveRootSmall_pos))]

/-- Connectedness is proved by the three edges of the path. -/
theorem path_connected : pathGraph.Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable pathGraph).mpr
  refine ⟨0, ?_⟩
  intro v
  have h01 : pathGraph.Adj 0 1 := by decide
  have h12 : pathGraph.Adj 1 2 := by decide
  have h23 : pathGraph.Adj 2 3 := by decide
  fin_cases v
  · exact SimpleGraph.Reachable.refl 0
  · exact h01.reachable
  · exact h01.reachable.trans h12.reachable
  · exact (h01.reachable.trans h12.reachable).trans h23.reachable

/-- Standard orientable rotation-system data on a finite connected graph with no
isolated vertex. Darts encode every ordered adjacent pair exactly once. `reverse`
is reversal of an edge, and `rotate` is one cyclic order on the darts at each
vertex. Faces are the cycles of `rotate * reverse`.

The standard topological interpretation is obtained by oriented vertex disks,
untwisted edge bands, then capping all boundary circles with disks. Conversely,
a cellular oriented embedding supplies precisely these cyclic orders. -/
structure RotationSystem {n : ℕ} (G : SimpleGraph (Fin n)) where
  dartCount : ℕ
  tail : Fin dartCount → Fin n
  reverse : Equiv.Perm (Fin dartCount)
  reverse_involution : ∀ d, reverse (reverse d) = d
  reverse_fixedpoint_free : ∀ d, reverse d ≠ d
  dart_adjacent : ∀ d, G.Adj (tail d) (tail (reverse d))
  dart_injective : Function.Injective (fun d => (tail d, tail (reverse d)))
  dart_surjective : ∀ u v, G.Adj u v → ∃ d, tail d = u ∧ tail (reverse d) = v
  connected : G.Connected
  vertex_nonempty : ∀ v, ∃ d, tail d = v
  rotate : Equiv.Perm (Fin dartCount)
  rotate_tail : ∀ d, tail (rotate d) = tail d
  vertex_cyclic : ∀ d e, tail d = tail e → rotate.SameCycle d e

/-- Face boundaries are permutation orbits, so fixed points count as faces too. -/
def RotationSystem.Face {n : ℕ} {G : SimpleGraph (Fin n)} (R : RotationSystem G) :=
  Quotient (Equiv.Perm.SameCycle.setoid (R.rotate * R.reverse))

/-- The orbit quotient of a finite dart set is finite. Its cardinal is never an
infinite-type fallback value. -/
instance RotationSystem.faceFinite {n : ℕ} {G : SimpleGraph (Fin n)}
    (R : RotationSystem G) : Finite R.Face := by
  unfold RotationSystem.Face
  infer_instance

noncomputable def RotationSystem.faceCount {n : ℕ} {G : SimpleGraph (Fin n)}
    (R : RotationSystem G) : ℕ := Nat.card R.Face

/-- A cellular orientable genus certificate, via V-E+F=2-2g. This is the
rotation-system formulation of genuine cellular embeddings; it does not presume
the value of g. The integer coercions prevent truncated natural subtraction. -/
def HasCellularGenus {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (g : ℕ) : Prop :=
  ∃ R : RotationSystem G,
    (n : ℤ) - (G.edgeFinset.card : ℤ) + (R.faceCount : ℤ) = 2 - 2 * (g : ℤ)

/-- The minimum over all orientable cellular embeddings. On the connected,
noncomplete domain used below, this is the ordinary minimum orientable genus. -/
def IsMinimumGenus {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (g : ℕ) : Prop :=
  HasCellularGenus G g ∧ ∀ h : ℕ, HasCellularGenus G h → g ≤ h

def pathTail : Fin 6 → Fin 4 := ![0, 1, 1, 2, 2, 3]

def pathReverse : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 3, 2, 5, 4]
  invFun := ![1, 0, 3, 2, 5, 4]
  left_inv := by decide
  right_inv := by decide

def pathRotate : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 1, 4, 3, 5]
  invFun := ![0, 2, 1, 4, 3, 5]
  left_inv := by decide
  right_inv := by decide

theorem path_vertex_cyclic : ∀ d e, pathTail d = pathTail e →
    pathRotate.SameCycle d e := by
  have h : ∀ d e, pathTail d = pathTail e →
      ∃ k : Fin 2, (pathRotate ^ k.val) d = e := by decide
  intro d e hde
  obtain ⟨k, hk⟩ := h d e hde
  exact ⟨(k.val : ℤ), by simpa using hk⟩

def pathRotationSystem : RotationSystem pathGraph where
  dartCount := 6
  tail := pathTail
  reverse := pathReverse
  reverse_involution := by decide
  reverse_fixedpoint_free := by decide
  dart_adjacent := by decide
  dart_injective := by decide
  dart_surjective := by decide
  connected := path_connected
  vertex_nonempty := by decide
  rotate := pathRotate
  rotate_tail := by decide
  vertex_cyclic := path_vertex_cyclic

/-- The single face follows the dart cycle (0,2,4,5,3,1). -/
theorem path_face_transitive : ∀ d : Fin 6,
    (pathRotate * pathReverse).SameCycle 0 d := by
  have h : ∀ d : Fin 6, ∃ k : Fin 6, ((pathRotate * pathReverse) ^ k.val) 0 = d := by
    decide
  intro d
  obtain ⟨k, hk⟩ := h d
  exact ⟨(k.val : ℤ), by simpa using hk⟩

theorem path_faces_one : pathRotationSystem.faceCount = 1 := by
  apply Nat.card_eq_one_iff_exists.mpr
  refine ⟨Quotient.mk _ (0 : Fin 6), ?_⟩
  intro face
  induction face using Quotient.inductionOn with
  | h d =>
    apply Quotient.sound
    exact (path_face_transitive d).symm

theorem path_edges_three : pathGraph.edgeFinset.card = 3 := by decide

theorem path_genus_zero : HasCellularGenus pathGraph 0 := by
  refine ⟨pathRotationSystem, ?_⟩
  rw [path_faces_one, path_edges_three]
  norm_num

theorem path_minimum_genus_zero : IsMinimumGenus pathGraph 0 :=
  ⟨path_genus_zero, fun _ _ => Nat.zero_le _⟩

/-- Equality is with the printed bound α ≤ i₊, without correcting that bound. -/
theorem path_attains_printed_bound :
    independenceNumber pathGraph ≤ positiveInertiaIndex pathAdjacency ∧
    independenceNumber pathGraph = positiveInertiaIndex pathAdjacency := by
  rw [path_independence_number, path_positive_inertia]
  exact ⟨le_rfl, rfl⟩

/-- All eligibility and numerical facts for one genuine signed graph. -/
theorem counterexample_certificate :
    signedPath.graph.Connected ∧ signedPath.graph ≠ ⊤ ∧
    independenceNumber pathGraph = positiveInertiaIndex signedPath.adjacency ∧
    IsMinimumGenus pathGraph 0 :=
  ⟨path_connected, path_not_complete, path_attains_printed_bound.2,
    path_minimum_genus_zero⟩

/-- The per-graph reading fails even in the connected, noncomplete subclass. -/
theorem not_per_graph_genus_one : ¬ (∀ (n : ℕ) (S : SignedGraph (Fin n))
    [DecidableRel S.graph.Adj], S.graph.Connected → S.graph ≠ ⊤ →
    independenceNumber S.graph = positiveInertiaIndex S.adjacency →
    IsMinimumGenus S.graph 1) := by
  intro h
  letI signedPathAdjDecidable : DecidableRel signedPath.graph.Adj := pathAdjDecidable
  have hm := h 4 signedPath path_connected path_not_complete path_attains_printed_bound.2
  have hz := hm.2 0 path_genus_zero
  omega

/-- The lower-bound clause independently necessary for a class minimum of 1:
every eligible graph's minimum genus must be at least 1. -/
def ClassMinimumOneLowerBound : Prop :=
  ∀ (n : ℕ) (S : SignedGraph (Fin n)) [DecidableRel S.graph.Adj] (g : ℕ),
    S.graph.Connected → S.graph ≠ ⊤ →
    independenceNumber S.graph = positiveInertiaIndex S.adjacency →
    IsMinimumGenus S.graph g → 1 ≤ g

/-- Hence the alternative reading "the minimum genus across tight graphs is 1"
also fails, using its independently asserted necessary lower bound. -/
theorem not_class_minimum_one : ¬ ClassMinimumOneLowerBound := by
  intro h
  letI signedPathAdjDecidable : DecidableRel signedPath.graph.Adj := pathAdjDecidable
  have hz := h 4 signedPath 0 path_connected path_not_complete
    path_attains_printed_bound.2 path_minimum_genus_zero
  omega

end Conjecture2161
