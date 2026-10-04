import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

noncomputable section
open Finset Matrix Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators
namespace RandomGraphGap
abbrev V (n : ℕ) := Fin (n+2)
abbrev Vec (n : ℕ) := V n → ℝ
abbrev Mat (n : ℕ) := Matrix (V n) (V n) ℝ

def order (n : ℕ) : ℝ := n+2
def degree (n : ℕ) : ℝ := n+1
def graph (n : ℕ) : SimpleGraph (V n) := ⊤
instance (n : ℕ) : DecidableRel (graph n).Adj := by unfold graph; infer_instance
def adjacency (n : ℕ) : Mat n := (graph n).adjMatrix ℝ

theorem degree_actual (n : ℕ) (i : V n) : (graph n).degree i = n+1 := by
  simp [graph, V]

theorem degree_pos (n : ℕ) : 0 < degree n := by dsimp [degree]; positivity

theorem adjacency_apply (n : ℕ) (x : Vec n) (i : V n) :
    (adjacency n *ᵥ x) i = (∑ j, x j) - x i := by
  classical
  calc
    _ = ∑ j, (x j - if i = j then x j else 0) := by
      change (∑ j, adjacency n i j * x j) = _
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : i = j
      · simp [adjacency, graph, SimpleGraph.adjMatrix_apply, h]
      · simp [adjacency, graph, SimpleGraph.adjMatrix_apply, h]
    _ = _ := by rw [Finset.sum_sub_distrib]; simp

/-- c=1 is the normalized Laplacian; c=1/2 is I minus the lazy transition. -/
def lap (n : ℕ) (c : ℝ) : Mat n := c • (1 - (degree n)⁻¹ • adjacency n)
def eigenvalue (n : ℕ) (c : ℝ) : ℝ := c * order n / degree n

theorem lap_apply (n : ℕ) (c : ℝ) (x : Vec n) (i : V n) :
    (lap n c *ᵥ x) i = eigenvalue n c * x i - c / degree n * ∑ j, x j := by
  simp only [lap, Matrix.smul_mulVec_assoc, Matrix.sub_mulVec, Matrix.one_mulVec,
    Pi.smul_apply, smul_eq_mul, Pi.sub_apply, adjacency_apply]
  dsimp [eigenvalue, order, degree]
  have hd : (n : ℝ)+1 ≠ 0 := by positivity
  field_simp
  ring

theorem lap_sum (n : ℕ) (c : ℝ) (x : Vec n) : ∑ i, (lap n c *ᵥ x) i = 0 := by
  simp only [lap_apply, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  dsimp [eigenvalue, order, degree]
  push_cast
  ring

def witness (n : ℕ) : Vec n := Pi.single 0 1 - Pi.single 1 1

theorem indices_ne (n : ℕ) : (0 : V n) ≠ 1 := by
  intro h
  have hh := congrArg Fin.val h
  simp [V] at hh

theorem witness_sum (n : ℕ) : ∑ i, witness n i = 0 := by
  classical
  simp [witness, Pi.sub_apply, Finset.sum_sub_distrib]

theorem witness_ne (n : ℕ) : witness n ≠ 0 := by
  intro h
  have hh := congrFun h 0
  simp [witness, Pi.single_apply, indices_ne n, Ne.symm (indices_ne n)] at hh

theorem witness_equation (n : ℕ) (c : ℝ) :
    lap n c *ᵥ witness n = eigenvalue n c • witness n := by
  ext i
  simp [lap_apply, witness_sum]

theorem nonzero_eigenvalue_unique (n : ℕ) (c r : ℝ) (hr : r ≠ 0)
    (x : Vec n) (hx : x ≠ 0) (he : lap n c *ᵥ x = r • x) : r = eigenvalue n c := by
  have hs := congrArg (fun y : Vec n => ∑ i, y i) he
  simp only [lap_sum, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum] at hs
  have hsum : ∑ i, x i = 0 := (mul_eq_zero.mp hs.symm).resolve_left hr
  obtain ⟨i,hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    apply hx
    ext i
    exact not_ne_iff.mp (fun hi => h ⟨i,hi⟩)
  have hh := congrFun he i
  simp only [lap_apply, hsum, mul_zero, sub_zero, Pi.smul_apply, smul_eq_mul] at hh
  exact (mul_right_cancel₀ hi hh).symm

def positiveEigenvalues (n : ℕ) (c : ℝ) : Set ℝ :=
  {r | 0 < r ∧ ∃ x : Vec n, x ≠ 0 ∧ lap n c *ᵥ x = r • x}
def gap (n : ℕ) (c : ℝ) : ℝ := sInf (positiveEigenvalues n c)

theorem eigenvalue_pos (n : ℕ) (c : ℝ) (hc : 0 < c) : 0 < eigenvalue n c := by
  unfold eigenvalue
  apply div_pos (mul_pos hc ?_) (degree_pos n)
  dsimp [order]; positivity

theorem positive_spectrum (n : ℕ) (c : ℝ) (hc : 0 < c) :
    positiveEigenvalues n c = {eigenvalue n c} := by
  ext r
  constructor
  · rintro ⟨hr,x,hx,he⟩
    exact nonzero_eigenvalue_unique n c r (ne_of_gt hr) x hx he
  · intro hr
    have he : r = eigenvalue n c := hr
    subst r
    exact ⟨eigenvalue_pos n c hc, witness n, witness_ne n, witness_equation n c⟩

theorem gap_formula (n : ℕ) (c : ℝ) (hc : 0 < c) : gap n c = c * order n / degree n := by
  rw [gap, positive_spectrum n c hc, csInf_singleton]
  rfl

theorem normalized_gap_bound (n : ℕ) : 0 < gap n 1 ∧ gap n 1 ≤ 2 := by
  rw [gap_formula n 1 zero_lt_one]
  constructor
  · apply div_pos
    · dsimp [order]; positivity
    · exact degree_pos n
  · apply (div_le_iff₀ (degree_pos n)).mpr
    dsimp [order, degree]
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

theorem lazy_gap_bound (n : ℕ) : 0 < gap n (1/2) ∧ gap n (1/2) ≤ 1 := by
  rw [gap_formula n (1/2) (by norm_num)]
  constructor
  · apply div_pos
    · dsimp [order]; positivity
    · exact degree_pos n
  · apply (div_le_iff₀ (degree_pos n)).mpr
    dsimp [order, degree]
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

def lazyWalk (n : ℕ) : Mat n := (1/2 : ℝ) • 1 + (1/(2*degree n)) • adjacency n

theorem actual_lazy_laplacian (n : ℕ) : 1 - lazyWalk n = lap n (1/2) := by
  ext i j
  simp [lazyWalk, lap, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply]
  ring

theorem constants_kernel (n : ℕ) (c : ℝ) : lap n c *ᵥ (fun _ => 1) = 0 := by
  ext i
  simp [lap_apply, eigenvalue, order, degree, V]
  ring

theorem lazy_stochastic (n : ℕ) :
    (∀ i j, 0 ≤ lazyWalk n i j) ∧ lazyWalk n *ᵥ (fun _ => 1) = (fun _ => 1) := by
  constructor
  · intro i j
    have he : lazyWalk n i j = if i = j then 1/2 else 1/(2*degree n) := by
      by_cases h : i = j <;>
        simp [lazyWalk, adjacency, graph, SimpleGraph.adjMatrix_apply, Matrix.one_apply, h]
    rw [he]
    split_ifs
    · norm_num
    · exact le_of_lt (one_div_pos.mpr (mul_pos (by norm_num) (degree_pos n)))
  · have h := constants_kernel n (1/2)
    rw [← actual_lazy_laplacian, Matrix.sub_mulVec, Matrix.one_mulVec] at h
    exact (sub_eq_zero.mp h).symm

/-- Every unordered possible edge has exactly one representative i<j. -/
abbrev Edge (n : ℕ) := {e : V n × V n // e.1 < e.2}
def μ : Measure Unit := Measure.dirac ()
instance : IsProbabilityMeasure μ := by unfold μ; infer_instance

def graphRV (n : ℕ) (_ : Unit) : SimpleGraph (V n) := graph n
instance (n : ℕ) (ω : Unit) : DecidableRel (graphRV n ω).Adj := by unfold graphRV; infer_instance
def edgeRV (n : ℕ) (e : Edge n) (ω : Unit) : Bool :=
  decide ((graphRV n ω).Adj e.val.1 e.val.2)

theorem edgeRV_true (n : ℕ) (e : Edge n) (ω : Unit) : edgeRV n e ω = true := by
  simp [edgeRV, graphRV, graph, ne_of_lt e.property]

theorem edge_independence (n : ℕ) : iIndepFun (edgeRV n) μ := by
  classical
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets _
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have hinter : (⋂ j ∈ insert i S, edgeRV n j ⁻¹' sets j) =
        (edgeRV n i ⁻¹' sets i) ∩ (⋂ j ∈ S, edgeRV n j ⁻¹' sets j) := by
      ext ω; simp
    rw [hinter, Finset.prod_insert hi]
    by_cases ht : true ∈ sets i
    · have hp : edgeRV n i ⁻¹' sets i = Set.univ := by
        ext ω; simp [edgeRV_true, ht]
      simpa [hp] using ih
    · have hp : edgeRV n i ⁻¹' sets i = ∅ := by
        ext ω; simp [edgeRV_true, ht]
      simp [hp]

theorem bernoulli_one : PMF.bernoulli 1 (by rfl) = PMF.pure true := by
  ext b; cases b <;> simp [PMF.bernoulli_apply, PMF.pure_apply]

theorem edge_marginal (n : ℕ) (e : Edge n) :
    Measure.map (edgeRV n e) μ = (PMF.bernoulli 1 (by rfl)).toMeasure := by
  rw [bernoulli_one, PMF.toMeasure_pure]
  have he : edgeRV n e = fun _ => true := funext (edgeRV_true n e)
  rw [he, Measure.map_const]
  simp

theorem graph_complete_almost_surely (n : ℕ) : ∀ᵐ ω ∂μ, graphRV n ω = ⊤ := by
  exact Filter.Eventually.of_forall (fun _ => rfl)

/-- p=1 is in the stipulated dense regime. -/
theorem dense_regime : Tendsto (fun n => Real.log (order n) / order n) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => ((n+2 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  have hq : Tendsto order atTop atTop := by simpa [order] using hn
  exact Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hq

/-- The source's displayed scale at p=1, for any second-eigenvalue sequence. -/
def claimedScale (ell : ℕ → ℝ) (n : ℕ) : ℝ :=
  max (1 - ell n / (order n * 1)) (order n * (1 : ℝ)⁻¹)

theorem scale_lower (ell : ℕ → ℝ) (n : ℕ) : order n ≤ claimedScale ell n := by
  simp [claimedScale]

theorem no_positive_lower_constant (g : ℕ → ℝ) (hg : ∀ n, g n ≤ 2)
    (ell : ℕ → ℝ) (c : ℝ) (hc : 0 < c) (N : ℕ) :
    ∃ n ≥ N, g n < c * claimedScale ell n := by
  obtain ⟨m,hm⟩ := exists_nat_gt (2/c)
  let n := max m N
  have hmn : (m : ℝ) ≤ n := by exact_mod_cast (le_max_left m N)
  have hq : 2/c < order n := by dsimp [order]; linarith
  have ht : 2 < c * order n := by
    have hh := (div_lt_iff₀ hc).mp hq
    nlinarith
  refine ⟨n, le_max_right m N, ?_⟩
  exact (lt_of_le_of_lt (hg n) ht).trans_le
    (mul_le_mul_of_nonneg_left (scale_lower ell n) hc.le)

theorem normalized_formula_fails (ell : ℕ → ℝ) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n ≥ N, c * claimedScale ell n ≤ gap n 1 := by
  rintro ⟨c,hc,N,h⟩
  obtain ⟨n,hn,hbad⟩ := no_positive_lower_constant (fun n => gap n 1)
    (fun n => (normalized_gap_bound n).2) ell c hc N
  exact (not_lt_of_ge (h n hn)) hbad

theorem lazy_formula_fails (ell : ℕ → ℝ) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n ≥ N, c * claimedScale ell n ≤ gap n (1/2) := by
  rintro ⟨c,hc,N,h⟩
  obtain ⟨n,hn,hbad⟩ := no_positive_lower_constant (fun n => gap n (1/2))
    (fun n => (lazy_gap_bound n).2.trans (by norm_num)) ell c hc N
  exact (not_lt_of_ge (h n hn)) hbad

#print axioms degree_actual
#print axioms adjacency_apply
#print axioms positive_spectrum
#print axioms gap_formula
#print axioms actual_lazy_laplacian
#print axioms constants_kernel
#print axioms lazy_stochastic
#print axioms edge_independence
#print axioms edge_marginal
#print axioms graph_complete_almost_surely
#print axioms dense_regime
#print axioms normalized_formula_fails
#print axioms lazy_formula_fails
end RandomGraphGap
