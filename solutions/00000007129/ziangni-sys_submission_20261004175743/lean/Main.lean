import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

open Set
namespace SimplexCounterexample
@[simp] lemma fin2_val_0 : (0:Fin 2).val=0 := rfl
@[simp] lemma fin2_ne_0_1 : (0:Fin 2)≠1 := by decide
@[simp] lemma fin2_val_1 : (1:Fin 2).val=1 := rfl
@[simp] lemma fin2_ne_1_0 : (1:Fin 2)≠0 := by decide
@[simp] lemma fin3_val_0 : (0:Fin 3).val=0 := rfl
@[simp] lemma fin3_ne_0_1 : (0:Fin 3)≠1 := by decide
@[simp] lemma fin3_ne_0_2 : (0:Fin 3)≠2 := by decide
@[simp] lemma fin3_val_1 : (1:Fin 3).val=1 := rfl
@[simp] lemma fin3_ne_1_0 : (1:Fin 3)≠0 := by decide
@[simp] lemma fin3_ne_1_2 : (1:Fin 3)≠2 := by decide
@[simp] lemma fin3_val_2 : (2:Fin 3).val=2 := rfl
@[simp] lemma fin3_ne_2_0 : (2:Fin 3)≠0 := by decide
@[simp] lemma fin3_ne_2_1 : (2:Fin 3)≠1 := by decide
@[simp] lemma fin4_val_0 : (0:Fin 4).val=0 := rfl
@[simp] lemma fin4_ne_0_1 : (0:Fin 4)≠1 := by decide
@[simp] lemma fin4_ne_0_2 : (0:Fin 4)≠2 := by decide
@[simp] lemma fin4_ne_0_3 : (0:Fin 4)≠3 := by decide
@[simp] lemma fin4_val_1 : (1:Fin 4).val=1 := rfl
@[simp] lemma fin4_ne_1_0 : (1:Fin 4)≠0 := by decide
@[simp] lemma fin4_ne_1_2 : (1:Fin 4)≠2 := by decide
@[simp] lemma fin4_ne_1_3 : (1:Fin 4)≠3 := by decide
@[simp] lemma fin4_val_2 : (2:Fin 4).val=2 := rfl
@[simp] lemma fin4_ne_2_0 : (2:Fin 4)≠0 := by decide
@[simp] lemma fin4_ne_2_1 : (2:Fin 4)≠1 := by decide
@[simp] lemma fin4_ne_2_3 : (2:Fin 4)≠3 := by decide
@[simp] lemma fin4_val_3 : (3:Fin 4).val=3 := rfl
@[simp] lemma fin4_ne_3_0 : (3:Fin 4)≠0 := by decide
@[simp] lemma fin4_ne_3_1 : (3:Fin 4)≠1 := by decide
@[simp] lemma fin4_ne_3_2 : (3:Fin 4)≠2 := by decide

abbrev E := ℝ × ℝ
def P : Set E := {p | 0 ≤ p.1 ∧ p.1 ≤ 5 ∧ 0 ≤ p.2 ∧ 4*p.1+p.2 ≤ 25}
def v (i : Fin 4) : E := if i.val=0 then (0,0) else if i.val=1 then (5,0) else if i.val=2 then (5,5) else (0,25)
def objective (p:E) : ℝ := 2*p.1+p.2

theorem feasible_vertices (i:Fin 4) : v i ∈ P := by
  fin_cases i <;> norm_num [v,P]
theorem bounded_coordinates {p:E} (h:p∈P) : p.1∈Icc (0:ℝ) 5 ∧ p.2∈Icc (0:ℝ) 25 := by
  rcases h with ⟨hx,hX,hy,hY⟩
  exact ⟨⟨hx,hX⟩,hy,by linarith⟩
theorem convex_P : Convex ℝ P := by
  intro p hp q hq a b ha hb hab
  rcases hp with ⟨hpx,hpX,hpy,hpY⟩
  rcases hq with ⟨hqx,hqX,hqy,hqY⟩
  change 0≤a*p.1+b*q.1 ∧ a*p.1+b*q.1≤5 ∧ 0≤a*p.2+b*q.2 ∧ _
  refine ⟨by positivity, ?_, by positivity, ?_⟩
  · nlinarith [mul_nonneg ha (sub_nonneg.mpr hpX),mul_nonneg hb (sub_nonneg.mpr hqX)]
  · change 4*(a*p.1+b*q.1)+(a*p.2+b*q.2)≤25
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hpY),mul_nonneg hb (sub_nonneg.mpr hqY)]

lemma weighted_lower {a b x y:ℝ} (ha:0<a) (hb:0≤b) (hx:0≤x) (hy:0≤y)
    (h:a*x+b*y=0) : x=0 := by
  nlinarith [mul_nonneg hb hy]
lemma weighted_upper {a b x y c:ℝ} (ha:0<a) (hb:0≤b) (hab:a+b=1)
    (hx:x≤c) (hy:y≤c) (h:a*x+b*y=c) : x=c := by
  have hc : (a+b)*c=c := by rw [hab,one_mul]
  nlinarith [mul_nonneg hb (sub_nonneg.mpr hy)]

theorem vertices_extreme (i:Fin 4) : v i ∈ P.extremePoints ℝ := by
  apply mem_extremePoints_iff_left.mpr
  refine ⟨feasible_vertices i, ?_⟩
  intro p hp q hq hseg
  rcases hseg with ⟨a,b,ha,hb,hab,he⟩
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  change a*p.1+b*q.1=(v i).1 at hx
  change a*p.2+b*q.2=(v i).2 at hy
  rcases hp with ⟨hpx,hpX,hpy,hpY⟩
  rcases hq with ⟨hqx,hqX,hqy,hqY⟩
  fin_cases i <;> norm_num [v] at hx hy ⊢
  · exact Prod.ext (weighted_lower ha hb.le hpx hqx hx) (weighted_lower ha hb.le hpy hqy hy)
  · exact Prod.ext (weighted_upper ha hb.le hab hpX hqX hx) (weighted_lower ha hb.le hpy hqy hy)
  · have hpx5 := weighted_upper ha hb.le hab hpX hqX hx
    have htotal : 4*p.1+p.2=25 := weighted_upper ha hb.le hab hpY hqY (by linarith)
    exact Prod.ext hpx5 (by change p.2=5; linarith)
  · have hpx0 := weighted_lower ha hb.le hpx hqx hx
    have htotal : 4*p.1+p.2=25 := weighted_upper ha hb.le hab hpY hqY (by linarith)
    exact Prod.ext hpx0 (by (try dsimp); linarith)

theorem extreme_classification {p:E} (he:p∈P.extremePoints ℝ) : ∃i, p=v i := by
  have hp := he.1
  rcases hp with ⟨hx,hX,hy,hY⟩
  have htop : 0<25-4*p.1 := by linarith
  have boundary : p.2=0 ∨ p.2=25-4*p.1 := by
    by_contra hn
    push_neg at hn
    have hy0 : 0<p.2 := lt_of_le_of_ne hy (Ne.symm hn.1)
    have hyT : p.2<25-4*p.1 := lt_of_le_of_ne (by linarith) hn.2
    have hs : p∈openSegment ℝ (p.1,0) (p.1,25-4*p.1) := by
      refine ⟨(25-4*p.1-p.2)/(25-4*p.1),p.2/(25-4*p.1),
        div_pos (by linarith) htop,div_pos hy0 htop,?_,?_⟩
      · field_simp
      · apply Prod.ext <;> dsimp
        all_goals field_simp <;> ring
    have h := (he.2 (show (p.1,0)∈P by exact ⟨hx,hX,le_rfl,by (try dsimp); linarith⟩)
      (show (p.1,25-4*p.1)∈P by exact ⟨hx,hX,htop.le,by ring_nf; norm_num⟩) hs).1
    have := congrArg Prod.snd h
    exact hn.1 this.symm
  have xend : p.1=0 ∨ p.1=5 := by
    by_cases hz : p.1=0
    · exact Or.inl hz
    by_cases hf : p.1=5
    · exact Or.inr hf
    exfalso
    have hx0 : 0<p.1 := lt_of_le_of_ne hx (Ne.symm hz)
    have hx5 : p.1<5 := lt_of_le_of_ne hX hf
    rcases boundary with hy0 | hyT
    · have hs : p∈openSegment ℝ (v 0) (v 1) := by
        refine ⟨1-p.1/5,p.1/5,by linarith,by positivity,by ring,?_⟩
        apply Prod.ext <;> norm_num [v] <;> linarith
      have h := (he.2 (feasible_vertices 0) (feasible_vertices 1) hs).1
      have := congrArg Prod.fst h
      exact hz this.symm
    · have hs : p∈openSegment ℝ (v 3) (v 2) := by
        refine ⟨1-p.1/5,p.1/5,by linarith,by positivity,by ring,?_⟩
        apply Prod.ext <;> norm_num [v] <;> linarith
      have h := (he.2 (feasible_vertices 3) (feasible_vertices 2) hs).1
      have := congrArg Prod.fst h
      exact hz this.symm
  rcases xend with hx0 | hx5 <;> rcases boundary with hy0 | hyT
  · exact ⟨0,Prod.ext hx0 hy0⟩
  · exact ⟨3,Prod.ext hx0 (by norm_num [v]; linarith)⟩
  · exact ⟨1,Prod.ext hx5 hy0⟩
  · exact ⟨2,Prod.ext hx5 (by norm_num [v]; linarith)⟩

theorem full_vertex_set : P.extremePoints ℝ = range v := by
  ext p; constructor
  · intro h; obtain ⟨i,rfl⟩ := extreme_classification h; exact mem_range_self i
  · rintro ⟨i,rfl⟩; exact vertices_extreme i

-- Distinct vertices share an edge exactly when a nonzero linear functional
-- supports P at both. In a full-dimensional planar polytope this is the
-- usual one-dimensional exposed-face definition of an edge.
def Supports (a b:ℝ) (i:Fin 4) : Prop :=
  (a≠0 ∨ b≠0) ∧ ∀p∈P, a*p.1+b*p.2 ≤ a*(v i).1+b*(v i).2
def Edge (i j:Fin 4) : Prop := i≠j ∧ ∃a b:ℝ,
  Supports a b i ∧ a*(v j).1+b*(v j).2=a*(v i).1+b*(v i).2

def cycle : SimpleGraph (Fin 4) where
  Adj i j := i.val%2 ≠ j.val%2
  symm := fun _ _ h => Ne.symm h
  loopless := fun _ h => h rfl
instance : DecidableRel cycle.Adj := fun i j => inferInstanceAs (Decidable (i.val%2≠j.val%2))





theorem edges_exact (i j:Fin 4) : Edge i j ↔ cycle.Adj i j := by
  constructor
  · rintro ⟨hne,a,b,hs,he⟩
    have h0 := hs.2 (v 0) (feasible_vertices 0)
    have h1 := hs.2 (v 1) (feasible_vertices 1)
    have h2 := hs.2 (v 2) (feasible_vertices 2)
    have h3 := hs.2 (v 3) (feasible_vertices 3)
    have hn := hs.1
    clear hs
    fin_cases i <;> fin_cases j <;> norm_num [v,cycle] at *
    all_goals rcases hn with ha | hb
    all_goals exfalso
    all_goals first | apply ha | apply hb
    all_goals linarith
  · intro h
    fin_cases i <;> fin_cases j <;> norm_num [cycle] at h
    · refine ⟨by decide,0,-1,⟨by norm_num,?_⟩,by norm_num [v]⟩
      rintro p ⟨hx,hX,hy,hY⟩; dsimp [v]; linarith
    · refine ⟨by decide,-1,0,⟨by norm_num,?_⟩,by norm_num [v]⟩
      rintro p ⟨hx,hX,hy,hY⟩; dsimp [v]; linarith
    · refine ⟨by decide,0,-1,⟨by norm_num,?_⟩,by norm_num [v]⟩
      rintro p ⟨hx,hX,hy,hY⟩; dsimp [v]; linarith
    · refine ⟨by decide,1,0,⟨by norm_num,?_⟩,by norm_num [v]⟩
      rintro p ⟨hx,hX,hy,hY⟩; dsimp [v]; linarith
    · refine ⟨by decide,1,0,⟨by norm_num,?_⟩,by norm_num [v]⟩
      rintro p ⟨hx,hX,hy,hY⟩; dsimp [v]; linarith
    · refine ⟨by decide,4,1,⟨by norm_num,?_⟩,by norm_num [v]⟩
      rintro p ⟨hx,hX,hy,hY⟩; dsimp [v]; linarith
    · refine ⟨by decide,-1,0,⟨by norm_num,?_⟩,by norm_num [v]⟩
      rintro p ⟨hx,hX,hy,hY⟩; dsimp [v]; linarith
    · refine ⟨by decide,4,1,⟨by norm_num,?_⟩,by norm_num [v]⟩
      rintro p ⟨hx,hX,hy,hY⟩; dsimp [v]; linarith

lemma edist_le_two (i j:Fin 4) : cycle.edist i j ≤ 2 := by
  by_cases he:i=j
  · subst j; simp
  by_cases ha:cycle.Adj i j
  · rw [SimpleGraph.edist_eq_one_iff_adj.mpr ha]; norm_num
  have hm : ∃k, cycle.Adj i k ∧ cycle.Adj k j := by
    fin_cases i <;> fin_cases j <;> norm_num [cycle] at he ha ⊢
    all_goals first | exact ⟨0,by decide,by decide⟩ | exact ⟨1,by decide,by decide⟩
  obtain ⟨k,hk,hK⟩ := hm
  calc cycle.edist i j ≤ cycle.edist i k + cycle.edist k j := cycle.edist_triangle
       _ = 2 := by rw [SimpleGraph.edist_eq_one_iff_adj.mpr hk,SimpleGraph.edist_eq_one_iff_adj.mpr hK]; norm_num

theorem diameter_two : cycle.diam=2 := by
  have hub : cycle.ediam ≤ 2 := SimpleGraph.ediam_le_of_edist_le edist_le_two
  have hfin : cycle.ediam ≠ ⊤ := ne_top_of_le_ne_top (by simp) hub
  have hpos : cycle.diam≠0 := SimpleGraph.diam_ne_zero_of_ediam_ne_top hfin
  have hne : cycle.diam≠1 := by
    intro h
    have ht := SimpleGraph.diam_eq_one.mp h
    have ha : cycle.Adj 0 2 := by rw [ht]; decide
    exact (by decide : ¬cycle.Adj 0 2) ha
  have hle : cycle.diam≤2 := by
    obtain ⟨i,j,hij⟩ := SimpleGraph.exists_dist_eq_diam (G:=cycle)
    rw [←hij,SimpleGraph.dist]
    exact ENat.toNat_le_toNat (edist_le_two i j) (by simp)
  omega




theorem full_dimensional (a b c:ℝ) (h:∀p∈P,a*p.1+b*p.2=c) : a=0 ∧ b=0 := by
  have h0:=h (v 0) (feasible_vertices 0)
  have h1:=h (v 1) (feasible_vertices 1)
  have h3:=h (v 3) (feasible_vertices 3)
  norm_num [v] at h0 h1 h3
  constructor <;> linarith

abbrev Z := Fin 4 → ℝ
def Eqns (z:Z) : Prop := z 0+z 2=5 ∧ 4*z 0+z 1+z 3=25
def Feasible (z:Z) : Prop := Eqns z ∧ ∀i,0≤z i
def lift (p:E) : Z := fun i => if i.val=0 then p.1 else if i.val=1 then p.2 else if i.val=2 then 5-p.1 else 25-4*p.1-p.2
theorem feasible_equivalence (p:E) : Feasible (lift p) ↔ p∈P := by
  simp [Feasible,Eqns,lift,Fin.forall_fin_succ,P]
  intro hx
  constructor <;> rintro ⟨h0,h1,h2⟩
  · exact ⟨h1,h0,by linarith⟩
  · exact ⟨h1,h0,by linarith⟩

def dictionary (k:Fin 4) (u:E) : Z :=
  if k.val=0 then lift u else if k.val=1 then lift (5-u.1,u.2)
  else if k.val=2 then lift (5-u.1,5+4*u.1-u.2)
  else lift (u.1,25-4*u.1-u.2)
def nonbasic (k:Fin 4) (j:Fin 2) : Fin 4 :=
  if k.val=0 then (if j.val=0 then 0 else 1) else if k.val=1 then (if j.val=0 then 2 else 1)
  else if k.val=2 then (if j.val=0 then 2 else 3) else (if j.val=0 then 0 else 3)
def basic (k:Fin 4) (j:Fin 2) : Fin 4 :=
  if k.val=0 then (if j.val=0 then 2 else 3) else if k.val=1 then (if j.val=0 then 0 else 3)
  else if k.val=2 then (if j.val=0 then 0 else 1) else (if j.val=0 then 2 else 1)
def reduced (k:Fin 4) (j:Fin 2) : ℝ :=
  if k.val=0 then (if j.val=0 then 2 else 1) else if k.val=1 then (if j.val=0 then -2 else 1)
  else if k.val=2 then (if j.val=0 then 2 else -1) else (if j.val=0 then -2 else -1)
def value (k:Fin 4) : ℝ := if k.val=0 then 0 else if k.val=1 then 10 else if k.val=2 then 15 else 25
def zObjective (z:Z) : ℝ := 2*z 0+z 1

theorem dictionary_eqns (k:Fin 4) (u:E) : Eqns (dictionary k u) := by
  fin_cases k <;> dsimp [dictionary,lift,Eqns] <;> constructor <;> ring

theorem dictionary_nonbasic (k:Fin 4) (u:E) :
    dictionary k u (nonbasic k 0)=u.1 ∧ dictionary k u (nonbasic k 1)=u.2 := by
  fin_cases k <;> norm_num [dictionary,lift,nonbasic] <;> ring

theorem dictionary_complete (k:Fin 4) (z:Z) (hz:Eqns z) :
    dictionary k (z (nonbasic k 0),z (nonbasic k 1))=z := by
  rcases hz with ⟨h0,h1⟩
  fin_cases k <;> ext i <;> fin_cases i <;> dsimp [dictionary,lift,nonbasic] <;> linarith

theorem dictionary_objective (k:Fin 4) (u:E) :
    zObjective (dictionary k u)=value k+reduced k 0*u.1+reduced k 1*u.2 := by
  fin_cases k <;> dsimp [dictionary,lift,zObjective,value,reduced] <;> ring

theorem basis_partition (k:Fin 4) :
    Function.Bijective (fun j:Fin 4 => ![nonbasic k 0,nonbasic k 1,basic k 0,basic k 1] j) := by
  fin_cases k <;> decide

theorem nondegenerate (k:Fin 4) (j:Fin 2) : 0<dictionary k (0,0) (basic k j) := by
  fin_cases k <;> fin_cases j <;> norm_num [dictionary,lift,basic]

theorem basic_points (k:Fin 4) : dictionary k (0,0)=lift (v k) := by
  fin_cases k <;> ext i <;> fin_cases i <;> norm_num [dictionary,lift,lift,v]

def entering (k:Fin 3) : Fin 2 := if k.val=1 then 1 else 0
def ray (k:Fin 3) (t:ℝ) : E := if entering k=0 then (t,0) else (0,t)
def old (k:Fin 3) : Fin 4 := k.castSucc
def next (k:Fin 3) : Fin 4 := k.succ

theorem unique_entering (k:Fin 3) : 0<reduced (old k) (entering k) ∧
    ∀j:Fin 2,j≠entering k → reduced (old k) j<reduced (old k) (entering k) := by
  fin_cases k <;> norm_num [entering,old,reduced] <;> intro j hj <;> fin_cases j <;> norm_num at *

theorem dictionary_ray (k:Fin 3) (t:ℝ) :
    dictionary (old k) (ray k t)=
      if k.val=0 then lift (t,0) else if k.val=1 then lift (5,t) else lift (5-t,5+4*t) := by
  fin_cases k <;> ext i <;> fin_cases i <;> norm_num [dictionary,lift,old,ray,entering]

theorem exact_ratio_test (k:Fin 3) (t:ℝ) :
    Feasible (dictionary (old k) (ray k t)) ↔ 0≤t ∧ t≤5 := by
  rw [dictionary_ray]
  fin_cases k <;> norm_num only [Fin.val_mk,ite_true,ite_false] <;> rw [feasible_equivalence]
  · change (0≤t ∧ t≤5 ∧ 0≤(0:ℝ) ∧ 4*t+0≤25) ↔ _
    constructor
    · rintro ⟨h0,h1,_,_⟩; exact ⟨h0,h1⟩
    · rintro ⟨h0,h1⟩; exact ⟨h0,h1,le_rfl,by linarith⟩
  · change (0≤(5:ℝ) ∧ (5:ℝ)≤5 ∧ 0≤t ∧ 4*5+t≤25) ↔ _
    constructor
    · rintro ⟨_,_,h0,h1⟩; exact ⟨h0,by linarith⟩
    · rintro ⟨h0,h1⟩; exact ⟨by norm_num,le_rfl,h0,by linarith⟩
  · change (0≤5-t ∧ 5-t≤5 ∧ 0≤5+4*t ∧ 4*(5-t)+(5+4*t)≤25) ↔ _
    constructor
    · rintro ⟨h0,h1,_,_⟩; exact ⟨by linarith,by linarith⟩
    · rintro ⟨h0,h1⟩; exact ⟨by linarith,by linarith,by linarith,by linarith⟩

theorem pivot_endpoint (k:Fin 3) : dictionary (old k) (ray k 5)=dictionary (next k) (0,0) := by
  fin_cases k <;> ext i <;> fin_cases i <;> norm_num [dictionary,lift,old,next,ray,entering]

-- Exactly one old basic variable vanishes at the ratio-test endpoint.
def leaving (k:Fin 3) : Fin 2 := if k.val=1 then 1 else 0
theorem unique_leaving (k:Fin 3) :
    dictionary (old k) (ray k 5) (basic (old k) (leaving k))=0 ∧
    ∀j:Fin 2,j≠leaving k → 0<dictionary (old k) (ray k 5) (basic (old k) j) := by
  fin_cases k <;> norm_num [dictionary,lift,old,ray,entering,basic,leaving] <;>
    intro j hj <;> fin_cases j <;> norm_num at *

theorem terminal_reduced_costs : ∀j:Fin 2,reduced 3 j<0 := by
  intro j; fin_cases j <;> norm_num [reduced]

theorem terminal_unique_optimum (p:E) (hp:p∈P) :
    objective p≤25 ∧ (objective p=25 ↔ p=v 3) := by
  rcases hp with ⟨hx,hX,hy,hY⟩
  norm_num [objective,v]
  refine ⟨by linarith,?_⟩
  constructor
  · intro h; apply Prod.ext <;> dsimp <;> linarith
  · intro h; rw [h]; norm_num

def simplexWalk : cycle.Walk 0 3 :=
  .cons (by decide : cycle.Adj 0 1)
    (.cons (by decide : cycle.Adj 1 2) (.cons (by decide : cycle.Adj 2 3) .nil))

theorem longer_than_diameter : simplexWalk.length=3 ∧ cycle.diam=2 ∧
    cycle.diam<simplexWalk.length := by
  rw [diameter_two]; norm_num [simplexWalk]

theorem vertices_distinct : Function.Injective v := by
  intro i j h
  fin_cases i <;> fin_cases j <;> norm_num [v] at h ⊢
  all_goals have hx:=congrArg Prod.fst h; have hy:=congrArg Prod.snd h; norm_num at hx hy

/-- A Dantzig step: unique largest positive reduced cost, complete maximal
feasible step interval, a unique limiting basic variable, and the next basis. -/
def DantzigPivot (k:Fin 3) : Prop :=
  (0<reduced (old k) (entering k) ∧ ∀j:Fin 2,j≠entering k →
      reduced (old k) j<reduced (old k) (entering k)) ∧
  (∀t:ℝ, Feasible (dictionary (old k) (ray k t)) ↔ 0≤t ∧ t≤5) ∧
  (dictionary (old k) (ray k 5) (basic (old k) (leaving k))=0 ∧
    ∀j:Fin 2,j≠leaving k → 0<dictionary (old k) (ray k 5) (basic (old k) j)) ∧
  dictionary (old k) (ray k 5)=dictionary (next k) (0,0)

theorem all_three_pivots (k:Fin 3) : DantzigPivot k :=
  ⟨unique_entering k,exact_ratio_test k,unique_leaving k,pivot_endpoint k⟩

theorem actual_pivot_edges (k:Fin 3) : Edge (old k) (next k) := by
  rw [edges_exact]
  fin_cases k <;> decide

theorem simplex_counterexample :
    (∀k:Fin 3,DantzigPivot k) ∧ (∀j:Fin 2,reduced 3 j<0) ∧
    simplexWalk.length=Fintype.card (Fin 3) ∧ cycle.diam<simplexWalk.length := by
  exact ⟨all_three_pivots,terminal_reduced_costs,rfl,longer_than_diameter.2.2⟩

#print axioms full_vertex_set
#print axioms edges_exact
#print axioms diameter_two
#print axioms dictionary_complete
#print axioms dictionary_objective
#print axioms unique_entering
#print axioms exact_ratio_test
#print axioms pivot_endpoint
#print axioms unique_leaving
#print axioms terminal_unique_optimum
#print axioms simplex_counterexample
end SimplexCounterexample
