import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Basic

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000

namespace FiedlerCounterexample
abbrev Vertex := Fin 10

def adjacent (u v : Vertex) : Prop := (u = 0 ∧ v ≠ 0) ∨ (v = 0 ∧ u ≠ 0)
instance (u v : Vertex) : Decidable (adjacent u v) := inferInstanceAs (Decidable ((_ ∧ _) ∨ (_ ∧ _)))

def Cycle (k : Nat) := ∃ f : Fin k → Vertex, Function.Injective f ∧
  ∀ i : Fin k, adjacent (f i) (f ⟨(i.val + 1) % k, Nat.mod_lt _ i.pos⟩)

theorem middle_center {a b c : Vertex} (hab : adjacent a b)
    (hbc : adjacent b c) (hne : a ≠ c) : b = 0 := by
  rcases hab with ⟨ha,hb⟩ | ⟨hb,ha⟩
  · rcases hbc with ⟨hb',hc⟩ | ⟨hc,hb'⟩
    · exact hb'
    · exact False.elim (hne (ha.trans hc.symm))
  · exact hb

theorem no_triangles : ¬ Cycle 3 := by
  rintro ⟨f,hi,he⟩
  have h01 := he (0 : Fin 3)
  have h12 := he (1 : Fin 3)
  have h20 := he (2 : Fin 3)
  change adjacent (f 0) (f 1) at h01
  change adjacent (f 1) (f 2) at h12
  change adjacent (f 2) (f 0) at h20
  have hn02 : f 0 ≠ f 2 := fun h => (by decide : (0 : Fin 3) ≠ 2) (hi h)
  have hb := middle_center h01 h12 hn02
  rcases h20 with ⟨h2,h0⟩ | ⟨h0,h2⟩
  · exact (by decide : (2 : Fin 3) ≠ 1) (hi (h2.trans hb.symm))
  · exact (by decide : (0 : Fin 3) ≠ 1) (hi (h0.trans hb.symm))

theorem no_quadrilaterals : ¬ Cycle 4 := by
  rintro ⟨f,hi,he⟩
  have h01 := he (0 : Fin 4)
  have h12 := he (1 : Fin 4)
  have h23 := he (2 : Fin 4)
  change adjacent (f 0) (f 1) at h01
  change adjacent (f 1) (f 2) at h12
  change adjacent (f 2) (f 3) at h23
  have hn02 : f 0 ≠ f 2 := fun h => (by decide : (0 : Fin 4) ≠ 2) (hi h)
  have hn13 : f 1 ≠ f 3 := fun h => (by decide : (1 : Fin 4) ≠ 3) (hi h)
  have hb := middle_center h01 h12 hn02
  have hc := middle_center h12 h23 hn13
  exact (by decide : (1 : Fin 4) ≠ 2) (hi (hb.trans hc.symm))

def sumLeaves (x : Vertex → ℝ) : ℝ := x 1+x 2+x 3+x 4+x 5+x 6+x 7+x 8+x 9
-- D-A for the star: center degree9, each leaf degree1.
def laplacian (x : Vertex → ℝ) (i : Vertex) : ℝ :=
  if i = 0 then 9*x 0-sumLeaves x else x i-x 0

def vertices : List Vertex := [0,1,2,3,4,5,6,7,8,9]
def neighbors (i : Vertex) : List Vertex := vertices.filter (fun j => decide (adjacent i j))
def graphLaplacian (x : Vertex → ℝ) (i : Vertex) : ℝ :=
  (neighbors i).length * x i - ((neighbors i).map x).sum

theorem vertices_complete (i : Vertex) : i ∈ vertices := by
  fin_cases i <;> norm_num [vertices, Fin.ext_iff, Fin.val_natCast, Fin.coe_ofNat_eq_mod]

theorem vertices_nodup : vertices.Nodup := by decide

theorem neighbors_center : neighbors 0 = [1,2,3,4,5,6,7,8,9] := by decide

theorem neighbors_leaf (i : Vertex) (hi : i ≠ 0) : neighbors i = [0] := by
  fin_cases i <;> first | exact False.elim (hi rfl) | decide

theorem laplacian_is_D_minus_A (x : Vertex → ℝ) (i : Vertex) :
    laplacian x i = graphLaplacian x i := by
  by_cases hi : i = 0
  · subst i
    simp only [laplacian,graphLaplacian,neighbors_center,if_pos rfl,
      List.length_cons,List.length_nil,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    norm_num
    dsimp [sumLeaves]
    ring
  · simp [laplacian,graphLaplacian,neighbors_leaf i hi,hi]

def Eigenvector (t : ℝ) (x : Vertex → ℝ) : Prop :=
  (∃ i, x i ≠ 0) ∧ ∀ i, laplacian x i = t*x i

def witness (i : Vertex) : ℝ := if i = 0 then 0 else if i = 9 then -8 else 1

theorem witness_eigenvector : Eigenvector 1 witness := by
  constructor
  · exact ⟨1, by norm_num [witness, Fin.ext_iff, Fin.val_natCast, Fin.coe_ofNat_eq_mod]⟩
  · intro i; fin_cases i <;> norm_num [laplacian, witness, sumLeaves, Fin.ext_iff, Fin.val_natCast, Fin.coe_ofNat_eq_mod]

theorem zero_kernel (x : Vertex → ℝ) (h : ∀ i, laplacian x i = 0) :
    ∀ i, x i = x 0 := by
  intro i
  by_cases hi : i = 0
  · subst i; rfl
  · have he := h i
    simp only [laplacian, if_neg hi] at he
    linarith

theorem spectrum (t : ℝ) (x : Vertex → ℝ) (h : Eigenvector t x) :
    t = 0 ∨ t = 1 ∨ t = 10 := by
  by_contra hn
  have ht0 : t ≠ 0 := by tauto
  have ht1 : t ≠ 1 := by tauto
  have ht10 : t ≠ 10 := by tauto
  have hc := h.2 0
  have h1 := h.2 1
  have h2 := h.2 2
  have h3 := h.2 3
  have h4 := h.2 4
  have h5 := h.2 5
  have h6 := h.2 6
  have h7 := h.2 7
  have h8 := h.2 8
  have h9 := h.2 9
  simp only [laplacian, sumLeaves] at hc h1 h2 h3 h4 h5 h6 h7 h8 h9
  norm_num [Fin.ext_iff, Fin.val_natCast, Fin.coe_ofNat_eq_mod] at hc h1 h2 h3 h4 h5 h6 h7 h8 h9
  have hmul := congrArg (fun z : ℝ => (t-1)*z) hc
  dsimp at hmul
  have he : t * (t-10) * x 0 = 0 := by nlinarith only [h1,h2,h3,h4,h5,h6,h7,h8,h9,hmul]
  have hz : x 0 = 0 := (mul_eq_zero.mp he).resolve_left (mul_ne_zero ht0 (sub_ne_zero.mpr ht10))
  obtain ⟨i,hi⟩ := h.1
  have hh := h.2 i
  by_cases hio : i = 0
  · exact hi (hio ▸ hz)
  · simp only [laplacian, if_neg hio, hz, sub_zero] at hh
    have heq : (t-1)*x i=0 := by nlinarith
    exact hi ((mul_eq_zero.mp heq).resolve_left (sub_ne_zero.mpr ht1))

-- For a connected Laplacian, its first eigenvalue is0; the next is the
-- least strictly positive eigenvalue (its zero eigenspace is one-dimensional).
def Fiedler (x : Vertex → ℝ) : Prop := Eigenvector 1 x ∧
  ∀ t y, Eigenvector t y → 0 < t → 1 ≤ t

theorem witness_fiedler : Fiedler witness := by
  refine ⟨witness_eigenvector, ?_⟩
  intro t y h ht
  rcases spectrum t y h with h0 | h1 | h10 <;> subst t <;> norm_num at *

def sameSign (x : Vertex → ℝ) (u v : Vertex) : Prop :=
  (0 < x u ∧ 0 < x v) ∨ (x u < 0 ∧ x v < 0)

theorem no_sign_edges : ∀ u v, adjacent u v → ¬ sameSign witness u v := by
  intro u v h
  rcases h with ⟨rfl,h⟩ | ⟨rfl,h⟩ <;> simp [sameSign,witness]

-- Paths in the induced nonzero sign graphs; the empty path is allowed.
inductive SignReach (x : Vertex → ℝ) : Vertex → Vertex → Prop
  | refl (u) : SignReach x u u
  | step {u v w} : adjacent u v → sameSign x u v →
      SignReach x v w → SignReach x u w

theorem reach_iff (u v : Vertex) : SignReach witness u v ↔ u = v := by
  constructor
  · intro h
    cases h with
    | refl => rfl
    | step ha hs hr => exact False.elim (no_sign_edges _ _ ha hs)
  · rintro rfl; exact SignReach.refl _

-- A representative list has exactly one vertex from each strong component.
def DomainRepresentatives (x : Vertex → ℝ) (rs : List Vertex) : Prop :=
  rs.Nodup ∧ (∀ r ∈ rs, x r ≠ 0) ∧
  (∀ v, x v ≠ 0 → ∃ r ∈ rs, SignReach x r v) ∧
  ∀ r ∈ rs, ∀ s ∈ rs, SignReach x r s → r = s

def representatives : List Vertex := [1,2,3,4,5,6,7,8,9]

theorem nine_domains : DomainRepresentatives witness representatives ∧
    representatives.length = 9 := by
  constructor
  · refine ⟨by decide, ?_, ?_, ?_⟩
    · intro r hr
      fin_cases r <;> norm_num [representatives,witness, Fin.ext_iff, Fin.val_natCast, Fin.coe_ofNat_eq_mod] at *
    · intro v hv
      refine ⟨v, ?_, SignReach.refl _⟩
      fin_cases v <;> norm_num [representatives,witness, Fin.ext_iff, Fin.val_natCast, Fin.coe_ofNat_eq_mod] at *
    · intro r hr s hs h; exact (reach_iff r s).mp h
  · rfl

theorem bound_violated : ¬ ((9 : ℝ) ≤ 2 * Real.sqrt 10) := by
  intro h
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 10 by norm_num)
  have hp := Real.sqrt_nonneg (10:ℝ)
  nlinarith

theorem conjecture_00000002153_false :
    ¬ Cycle 3 ∧ ¬ Cycle 4 ∧ Fiedler witness ∧
    DomainRepresentatives witness representatives ∧
    ¬ ((representatives.length : ℝ) ≤ 2 * Real.sqrt 10) := by
  exact ⟨no_triangles,no_quadrilaterals,witness_fiedler,nine_domains.1,
    by simpa [representatives] using bound_violated⟩

def HighGirthBoundOnStar : Prop := ∀ x rs, Fiedler x →
    DomainRepresentatives x rs → (rs.length : ℝ) ≤ 2 * Real.sqrt 10

theorem universal_bound_false : ¬ HighGirthBoundOnStar := by
  intro h
  exact conjecture_00000002153_false.2.2.2.2
    (h witness representatives witness_fiedler nine_domains.1)

#print axioms laplacian_is_D_minus_A
#print axioms spectrum
#print axioms zero_kernel
#print axioms universal_bound_false
#print axioms conjecture_00000002153_false
end FiedlerCounterexample
