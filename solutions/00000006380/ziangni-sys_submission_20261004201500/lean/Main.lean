import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
namespace MixedEnrichment
abbrev E := EuclideanSpace ℝ (Fin 2)
def e (j : Fin 2) (s : ℝ) : E := EuclideanSpace.single j s
def Q1 : Submodule ℝ E := LinearMap.ker (EuclideanSpace.projₗ (1 : Fin 2) : E →ₗ[ℝ] ℝ)
def Q2 : Submodule ℝ E := ⊤
def a (u v : E) : ℝ := @inner ℝ E _ u v
def b (v q : E) : ℝ := @inner ℝ E _ v q

theorem mem_Q1 (q : E) : q ∈ Q1 ↔ q 1 = 0 := by simp [Q1,LinearMap.mem_ker]
theorem axis_in_Q1 (s : ℝ) : e 0 s ∈ Q1 := by simp [mem_Q1,e]
theorem enrichment_strict : Q1 < Q2 := by
  apply lt_top_iff_ne_top.mpr
  intro h
  have hm : e 1 1 ∈ Q1 := by rw [h]; trivial
  simpa [mem_Q1,e] using hm

def scalarPressure : ℝ ≃ₗ[ℝ] Q1 where
  toFun s := ⟨e 0 s,axis_in_Q1 s⟩
  invFun q := (q : E) 0
  left_inv s := by simp [e]
  right_inv q := by
    apply Subtype.ext
    ext j
    fin_cases j
    · simp [e]
    · simpa [e] using (mem_Q1 _).mp q.property |>.symm
  map_add' s t := by apply Subtype.ext; ext j; simp [e,EuclideanSpace.single_apply]; split_ifs <;> simp
  map_smul' s t := by apply Subtype.ext; ext j; simp [e,EuclideanSpace.single_apply]

theorem actual_dimensions : Module.finrank ℝ Q1 = 1 ∧ Module.finrank ℝ Q2 = 2 := by
  constructor
  · have h := scalarPressure.finrank_eq
    simpa using h.symm
  · simp [Q2, E, finrank_euclideanSpace_fin]

theorem genuine_bilinearity :
    (∀ u v q, b (u+v) q = b u q + b v q) ∧
    (∀ s v q, b (s • v) q = s*b v q) ∧
    (∀ v p q, b v (p+q) = b v p + b v q) ∧
    (∀ s v q, b v (s • q) = s*b v q) := by
  refine ⟨?_,?_,?_,?_⟩
  all_goals intro x y z; simp only [b, inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
theorem actual_coercivity (v : E) : a v v = ‖v‖^2 := real_inner_self_eq_norm_sq v

def ratios (q : E) : Set ℝ := {r | ∃ v : E, v ≠ 0 ∧ r = b v q / (‖v‖*‖q‖)}
def pressureSup (q : E) : ℝ := sSup (ratios q)
def stability (Q : Submodule ℝ E) : ℝ :=
  sInf (pressureSup '' {q : E | q ∈ Q ∧ q ≠ 0})

theorem actual_velocity_supremum (q : E) (hq : q ≠ 0) : pressureSup q = 1 := by
  have hnorm : 0 < ‖q‖ := norm_pos_iff.mpr hq
  have hw : (1 : ℝ) ∈ ratios q := by
    refine ⟨q,hq,?_⟩
    rw [b, real_inner_self_eq_norm_sq, pow_two, div_self]
    exact mul_ne_zero (ne_of_gt hnorm) (ne_of_gt hnorm)
  have hle : ∀ r ∈ ratios q, r ≤ 1 := by
    rintro r ⟨v,hv,rfl⟩
    apply (div_le_iff₀ (mul_pos (norm_pos_iff.mpr hv) hnorm)).mpr
    simpa [b] using real_inner_le_norm v q
  have hb : BddAbove (ratios q) := ⟨1,hle⟩
  exact le_antisymm (csSup_le ⟨1,hw⟩ hle) (le_csSup hb hw)

theorem actual_infimum (Q : Submodule ℝ E) (hQ : ∃ q ∈ Q, q ≠ (0 : E)) :
    stability Q = 1 := by
  have he : pressureSup '' {q : E | q ∈ Q ∧ q ≠ 0} = {1} := by
    ext r
    constructor
    · rintro ⟨q,⟨hq,hq0⟩,rfl⟩
      simpa using actual_velocity_supremum q hq0
    · intro hr
      have hr1 : r = 1 := Set.mem_singleton_iff.mp hr
      obtain ⟨q,hq,hq0⟩ := hQ
      exact ⟨q,⟨hq,hq0⟩,(actual_velocity_supremum q hq0).trans hr1.symm⟩
  rw [stability,he,csInf_singleton]

theorem common_stability : stability Q1 = 1 ∧ stability Q2 = 1 := by
  have hn : e 0 1 ≠ (0 : E) := by
    intro h
    have hh := congrArg (fun z : E => z 0) h
    simpa [e] using hh
  exact ⟨actual_infimum Q1 ⟨e 0 1,axis_in_Q1 1,hn⟩,
    actual_infimum Q2 ⟨e 0 1,by trivial,hn⟩⟩

-- Both schemes restrict this SAME underlying mixed weak problem to their pressure space.
def System (Q : Submodule ℝ E) (f g u p : E) : Prop :=
  p ∈ Q ∧ (∀ v : E, a u v + b v p = a f v) ∧
    (∀ q ∈ Q, b u q = b g q)

theorem first_equation (f u p : E) :
    (∀ v : E, a u v + b v p = a f v) ↔ u+p=f := by
  constructor
  · intro h
    ext j
    fin_cases j
    · have hh := h (e 0 1)
      simpa [a,b,e,real_inner_comm,EuclideanSpace.inner_single_right] using hh
    · have hh := h (e 1 1)
      simpa [a,b,e,real_inner_comm,EuclideanSpace.inner_single_right] using hh
  · intro h v
    rw [b, real_inner_comm]
    change @inner ℝ E _ u v + @inner ℝ E _ p v = @inner ℝ E _ f v
    rw [← inner_add_left,h]

theorem second_Q1 (g u : E) : (∀ q ∈ Q1, b u q = b g q) ↔ u 0 = g 0 := by
  constructor
  · intro h
    simpa [b,e,EuclideanSpace.inner_single_right] using h (e 0 1) (axis_in_Q1 1)
  · intro h q hq
    have hz := (mem_Q1 q).mp hq
    simp [b, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two,hz,h]

theorem second_Q2 (g u : E) : (∀ q ∈ Q2, b u q = b g q) ↔ u = g := by
  constructor
  · intro h
    ext j
    fin_cases j
    · simpa [b,e,EuclideanSpace.inner_single_right] using h (e 0 1) (by trivial)
    · simpa [b,e,EuclideanSpace.inner_single_right] using h (e 1 1) (by trivial)
  · intro h; subst u; simp

def u1 (f g : E) : E := e 0 (g 0) + e 1 (f 1)
def p1 (f g : E) : E := e 0 (f 0-g 0)
theorem solution_Q1 (f g : E) : System Q1 f g (u1 f g) (p1 f g) := by
  refine ⟨axis_in_Q1 _, (first_equation _ _ _).mpr ?_, (second_Q1 _ _).mpr ?_⟩
  · ext j
    fin_cases j <;> simp [u1,p1,e,EuclideanSpace.single_apply] <;> ring
  · simp [u1,e]

theorem unique_Q1 (f g u p : E) (h : System Q1 f g u p) : u = u1 f g ∧ p = p1 f g := by
  have hp1 := (mem_Q1 p).mp h.1
  have he := (first_equation _ _ _).mp h.2.1
  have hu0 := (second_Q1 _ _).mp h.2.2
  have he0 := congrArg (fun z : E => z 0) he
  have he1 := congrArg (fun z : E => z 1) he
  constructor
  · ext j
    fin_cases j <;> simp [u1,e,EuclideanSpace.single_apply] <;> simp_all
  · ext j
    fin_cases j
    · simp [p1,e]
      change u 0 + p 0 = f 0 at he0
      linarith
    · simpa [p1,e] using hp1

theorem solution_Q2 (f g : E) : System Q2 f g g (f-g) := by
  refine ⟨by trivial, (first_equation _ _ _).mpr ?_, (second_Q2 _ _).mpr rfl⟩
  abel
theorem unique_Q2 (f g u p : E) (h : System Q2 f g u p) : u=g ∧ p=f-g := by
  have hu := (second_Q2 _ _).mp h.2.2
  have he := (first_equation _ _ _).mp h.2.1
  subst u
  exact ⟨rfl, eq_sub_of_add_eq' he⟩

theorem wellposed_Q1 (f g : E) : ∃! z : E × E, System Q1 f g z.1 z.2 := by
  refine ⟨(u1 f g,p1 f g),solution_Q1 f g,?_⟩
  intro z hz
  exact Prod.ext (unique_Q1 _ _ _ _ hz).1 (unique_Q1 _ _ _ _ hz).2
theorem wellposed_Q2 (f g : E) : ∃! z : E × E, System Q2 f g z.1 z.2 := by
  refine ⟨(g,f-g),solution_Q2 f g,?_⟩
  intro z hz
  exact Prod.ext (unique_Q2 _ _ _ _ hz).1 (unique_Q2 _ _ _ _ hz).2

theorem separation : Q1 < Q2 ∧ stability Q1 = stability Q2 ∧
    Module.finrank ℝ Q1 = 1 ∧ Module.finrank ℝ Q2 = 2 ∧
    (∀ f g, ∃! z : E × E, System Q1 f g z.1 z.2) ∧
    (∀ f g, ∃! z : E × E, System Q2 f g z.1 z.2) :=
  ⟨enrichment_strict,common_stability.1.trans common_stability.2.symm,
    actual_dimensions.1,actual_dimensions.2,wellposed_Q1,wellposed_Q2⟩

#print axioms enrichment_strict
#print axioms actual_dimensions
#print axioms genuine_bilinearity
#print axioms actual_coercivity
#print axioms actual_velocity_supremum
#print axioms actual_infimum
#print axioms common_stability
#print axioms wellposed_Q1
#print axioms wellposed_Q2
#print axioms separation
end MixedEnrichment
