import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Semicontinuous
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Set
open scoped InnerProductSpace
noncomputable section
namespace SelfDualCounterexample
abbrev Pair := ℝ × ℝ
def T : ℝ →L[ℝ] ℝ := ContinuousLinearMap.id ℝ ℝ
def graphT : Set Pair := {z | z.2 = T z.1}
def L (z : Pair) : ℝ := (z.1^2 + z.2^2) / 2

theorem continuous_L : Continuous L :=
  ((continuous_fst.pow 2).add (continuous_snd.pow 2)).div_const 2

theorem lowerSemicontinuous_L : LowerSemicontinuous L := continuous_L.lowerSemicontinuous

theorem convex_L : ConvexOn ℝ Set.univ L := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hb' : b = 1-a := by linarith
  have he : a*L x + b*L y - L (a • x + b • y) =
      a*b/2*((x.1-y.1)^2+(x.2-y.2)^2) := by
    rw [hb']
    change a*((x.1^2+x.2^2)/2)+(1-a)*((y.1^2+y.2^2)/2) -
      (((a*x.1+(1-a)*y.1)^2+(a*x.2+(1-a)*y.2)^2)/2) =
      a*(1-a)/2*((x.1-y.1)^2+(x.2-y.2)^2)
    ring
  have hn : 0 ≤ a*b/2*((x.1-y.1)^2+(x.2-y.2)^2) :=
    mul_nonneg (div_nonneg (mul_nonneg ha hb) (by norm_num))
      (add_nonneg (sq_nonneg _) (sq_nonneg _))
  change L (a • x + b • y) ≤ a*L x+b*L y
  linarith

theorem finite_proper : L (0,0) = 0 ∧ ∀ z, 0 ≤ L z := by
  constructor
  · norm_num [L]
  · intro z
    exact div_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (by norm_num)

def pairing (p : Pair) : Pair →L[ℝ] ℝ :=
  p.1 • ContinuousLinearMap.fst ℝ ℝ ℝ + p.2 • ContinuousLinearMap.snd ℝ ℝ ℝ

def conjugate (f : Pair →L[ℝ] ℝ) : ℝ := sSup (Set.range fun z => f z - L z)

theorem dual_coordinates (f : Pair →L[ℝ] ℝ) (z : Pair) :
    f z = f (1,0)*z.1 + f (0,1)*z.2 := by
  have hz : z = z.1 • (1,0) + z.2 • (0,1) := by ext <;> simp
  conv_lhs => rw [hz, map_add, map_smul, map_smul]
  simp only [smul_eq_mul]
  ring

theorem conjugate_formula (f : Pair →L[ℝ] ℝ) :
    conjugate f = L (f (1,0), f (0,1)) := by
  apply IsGreatest.csSup_eq
  constructor
  · refine ⟨(f (1,0), f (0,1)), ?_⟩
    dsimp only
    rw [dual_coordinates f (f (1,0), f (0,1))]
    simp only [L]
    ring
  · rintro v ⟨z, rfl⟩
    dsimp only
    rw [dual_coordinates f z]
    dsimp [L]
    nlinarith [sq_nonneg (z.1-f (1,0)), sq_nonneg (z.2-f (0,1))]

theorem selfdual_L (x p : ℝ) : conjugate (pairing (p,x)) = L (x,p) := by
  rw [conjugate_formula]
  simp [pairing, L, add_comm]

def generatedGraph : Set Pair := {z | L z = z.1*z.2}

theorem generated_graph : generatedGraph = graphT := by
  ext z
  change L z = z.1*z.2 ↔ z.2 = z.1
  constructor
  · intro h
    have hs : (z.1-z.2)^2 = 0 := by dsimp [L] at h; nlinarith
    exact (sub_eq_zero.mp (pow_eq_zero hs)).symm
  · intro h
    rw [L, h]
    ring

theorem adjoint_selfdual : ContinuousLinearMap.adjoint T = T :=
  ContinuousLinearMap.adjoint_id

theorem inverse_graph : {z : Pair | (z.2,z.1) ∈ graphT} = graphT := by
  ext z
  simp [graphT, T, eq_comm]

def MonotoneRelation (G : Set Pair) : Prop := ∀ z ∈ G, ∀ w ∈ G,
  0 ≤ ⟪z.1-w.1, z.2-w.2⟫_ℝ
def MaximalMonotone (G : Set Pair) : Prop := MonotoneRelation G ∧
  ∀ H, MonotoneRelation H → G ⊆ H → H ⊆ G

theorem graph_monotone : MonotoneRelation graphT := by
  intro z hz w hw
  change z.2 = z.1 at hz
  change w.2 = w.1 at hw
  rw [hz, hw]
  exact real_inner_self_nonneg

theorem graph_maximal : MaximalMonotone graphT := by
  refine ⟨graph_monotone, ?_⟩
  intro H hH hsub z hz
  let a := (z.1+z.2)/2
  have ha : (a,a) ∈ H := hsub (by simp [graphT, T])
  have h := hH z hz (a,a) ha
  change 0 ≤ (z.2-a)*(z.1-a) at h
  have hs : (z.1-z.2)^2 = 0 := by dsimp [a] at h; nlinarith [sq_nonneg (z.1-z.2)]
  change z.2 = z.1
  exact (sub_eq_zero.mp (pow_eq_zero hs)).symm

def AntisymmetricRelation (G : Set Pair) : Prop := ∀ z ∈ G, ∀ w ∈ G,
  ⟪z.2, w.1⟫_ℝ = -⟪z.1, w.2⟫_ℝ

theorem no_antisymmetric_extension : ¬ ∃ H, graphT ⊆ H ∧ AntisymmetricRelation H := by
  rintro ⟨H, hsub, hH⟩
  have h1 : ((1,1) : Pair) ∈ H := hsub (by simp [graphT, T])
  have h := hH (1,1) h1 (1,1) h1
  norm_num at h

theorem antisymmetric_restriction_domain (H : Set Pair) (hH : AntisymmetricRelation H)
    (hsub : H ⊆ graphT) : Prod.fst '' H ⊆ ({0} : Set ℝ) := by
  rintro x ⟨z, hz, rfl⟩
  have he : z.2 = z.1 := hsub hz
  have h := hH z hz z hz
  rw [he] at h
  change z.1*z.1 = -(z.1*z.1) at h
  have hs : z.1^2 = 0 := by nlinarith
  exact mem_singleton_iff.mpr (pow_eq_zero hs)

theorem no_dense_antisymmetric_restriction : ¬ ∃ H, AntisymmetricRelation H ∧
    H ⊆ graphT ∧ Dense (Prod.fst '' H) := by
  rintro ⟨H, hH, hsub, hd⟩
  have hc : closure (Prod.fst '' H) ⊆ ({0} : Set ℝ) :=
    closure_minimal (antisymmetric_restriction_domain H hH hsub) isClosed_singleton
  have h1 : (1 : ℝ) ∈ closure (Prod.fst '' H) := by rw [hd.closure_eq]; trivial
  have h := hc h1
  norm_num at h

#print axioms convex_L
#print axioms lowerSemicontinuous_L
#print axioms finite_proper
#print axioms dual_coordinates
#print axioms conjugate_formula
#print axioms selfdual_L
#print axioms generated_graph
#print axioms adjoint_selfdual
#print axioms inverse_graph
#print axioms graph_maximal
#print axioms no_antisymmetric_extension
#print axioms no_dense_antisymmetric_restriction
end SelfDualCounterexample
