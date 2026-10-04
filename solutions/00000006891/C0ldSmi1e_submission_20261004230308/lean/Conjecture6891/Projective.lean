import Conjecture6891.Rank
import Mathlib.LinearAlgebra.Projectivization.Subspace
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.MvPolynomial.Homogeneous

set_option synthInstance.maxHeartbeats 80000

noncomputable section
open scoped LinearAlgebra.Projectivization
open Projectivization
namespace Conjecture6891

abbrev ProjectiveTensor := Projectivization ℂ Tensor

/-- Homogeneous evaluation transforms by the expected power under scaling. -/
theorem homogeneous_eval_smul {p : MvPolynomial Coordinate ℂ} {d : ℕ}
    (hp : p.IsHomogeneous d) (c : ℂ) (z : Coordinate → ℂ) :
    MvPolynomial.eval (c • z) p = c ^ d * MvPolynomial.eval z p := by
  classical
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hd : (∑ i ∈ m.support, m i) = d := by
    have := hp (MvPolynomial.mem_support_iff.mp hm)
    simpa only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one, Finsupp.sum] using this
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hd]
  ring

/-- A polynomial vanishes on a projective point when it vanishes on every nonzero
representative. The homogeneous polynomials used below have scale-independent zero sets. -/
def ProjectiveVanishes (p : MvPolynomial Coordinate ℂ) (x : ProjectiveTensor) : Prop :=
  ∀ (v : Tensor) (hv : v ≠ 0), Projectivization.mk ℂ v hv = x →
    MvPolynomial.eval (coords v) p = 0

theorem projectiveVanishes_mk_iff {p : MvPolynomial Coordinate ℂ} {d : ℕ}
    (hp : p.IsHomogeneous d) (v : Tensor) (hv : v ≠ 0) :
    ProjectiveVanishes p (Projectivization.mk ℂ v hv) ↔
      MvPolynomial.eval (coords v) p = 0 := by
  constructor
  · exact fun h => h v hv rfl
  · intro h w hw he
    obtain ⟨c, rfl⟩ := (Projectivization.mk_eq_mk_iff' ℂ w v hw hv).mp he
    simp only [map_smul, homogeneous_eval_smul hp, h, mul_zero]

/-- Common projective zero locus; algebraic sets below use only homogeneous equations. -/
def projectiveZeroLocus (P : Set (MvPolynomial Coordinate ℂ)) : Set ProjectiveTensor :=
  {x | ∀ p ∈ P, ProjectiveVanishes p x}

/-- The usual homogeneous-equation definition of a projective algebraic set. -/
def IsProjectiveAlgebraic (Z : Set ProjectiveTensor) : Prop :=
  ∃ P : Set (MvPolynomial Coordinate ℂ),
    (∀ p ∈ P, ∃ d : ℕ, p.IsHomogeneous d) ∧ Z = projectiveZeroLocus P

/-- Projective Zariski closure, defined using all homogeneous equations vanishing on S. -/
def projectiveZariskiClosure (S : Set ProjectiveTensor) : Set ProjectiveTensor :=
  {x | ∀ (d : ℕ) (p : MvPolynomial Coordinate ℂ), p.IsHomogeneous d →
    (∀ y ∈ S, ProjectiveVanishes p y) → ProjectiveVanishes p x}

theorem subset_projectiveZariskiClosure (S : Set ProjectiveTensor) :
    S ⊆ projectiveZariskiClosure S := by
  intro x hx d p _ hp
  exact hp x hx

theorem projectiveZariskiClosure_mono {S T : Set ProjectiveTensor} (h : S ⊆ T) :
    projectiveZariskiClosure S ⊆ projectiveZariskiClosure T := by
  intro x hx d p hp hT
  exact hx d p hp (fun y hy => hT y (h hy))

theorem projectiveZariskiClosure_algebraic (S : Set ProjectiveTensor) :
    IsProjectiveAlgebraic (projectiveZariskiClosure S) := by
  refine ⟨{p | ∃ d, p.IsHomogeneous d ∧ ∀ y ∈ S, ProjectiveVanishes p y}, ?_, ?_⟩
  · rintro p ⟨d, hd, _⟩
    exact ⟨d, hd⟩
  · ext x
    constructor
    · intro hx p hp
      obtain ⟨d, hd, hS⟩ := hp
      exact hx d p hd hS
    · intro hx d p hd hS
      exact hx p ⟨d, hd, hS⟩

theorem projectiveZariskiClosure_least {S Z : Set ProjectiveTensor}
    (hZ : IsProjectiveAlgebraic Z) (hSZ : S ⊆ Z) :
    projectiveZariskiClosure S ⊆ Z := by
  obtain ⟨P, hP, rfl⟩ := hZ
  intro x hx p hp
  obtain ⟨d, hd⟩ := hP p hp
  exact hx d p hd (fun y hy => hSZ hy p hp)

theorem projectiveZariskiClosure_idem (S : Set ProjectiveTensor) :
    projectiveZariskiClosure (projectiveZariskiClosure S) = projectiveZariskiClosure S := by
  exact Set.Subset.antisymm
    (projectiveZariskiClosure_least (projectiveZariskiClosure_algebraic S) Set.Subset.rfl)
    (subset_projectiveZariskiClosure _)

/-- The projective Segre locus consists of actual nonzero simple tensors. -/
def segre : Set ProjectiveTensor :=
  {x | ∃ a b c : Vector, ∃ h : pure a b c ≠ 0,
    Projectivization.mk ℂ (pure a b c) h = x}

/-- Union of the actual projective spans of r Segre points, allowing repetitions. -/
def secantSpanLocus (r : ℕ) : Set ProjectiveTensor :=
  {x | ∃ q : Fin r → ProjectiveTensor, (∀ i, q i ∈ segre) ∧
    x ∈ Projectivization.Subspace.span (Set.range q)}

/-- The projective secant variety is the projective Zariski closure of the span locus. -/
def secantVariety (r : ℕ) : Set ProjectiveTensor :=
  projectiveZariskiClosure (secantSpanLocus r)

/-- A singleton projective point is itself a projective subspace. -/
def pointSubspace (x : ProjectiveTensor) : Projectivization.Subspace ℂ Tensor where
  carrier := {x}
  mem_add' v w hv hw hvw h₁ h₂ := by
    have hv' : Projectivization.mk ℂ v hv = Projectivization.mk ℂ x.rep x.rep_nonzero := by
      simpa only [Projectivization.mk_rep, Set.mem_singleton_iff] using h₁
    have hw' : Projectivization.mk ℂ w hw = Projectivization.mk ℂ x.rep x.rep_nonzero := by
      simpa only [Projectivization.mk_rep, Set.mem_singleton_iff] using h₂
    obtain ⟨a, rfl⟩ := (Projectivization.mk_eq_mk_iff' ℂ v x.rep hv x.rep_nonzero).mp hv'
    obtain ⟨b, rfl⟩ := (Projectivization.mk_eq_mk_iff' ℂ w x.rep hw x.rep_nonzero).mp hw'
    change Projectivization.mk ℂ (a • x.rep + b • x.rep) hvw = x
    exact ((Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
      ⟨a + b, add_smul a b x.rep⟩).trans (Projectivization.mk_rep x)

@[simp] theorem mem_pointSubspace (x y : ProjectiveTensor) :
    y ∈ pointSubspace x ↔ y = x := Iff.rfl

theorem projective_span_singleton (x : ProjectiveTensor) :
    Projectivization.Subspace.span {x} = pointSubspace x := by
  apply Projectivization.Subspace.span_eq_of_le
  · exact Set.Subset.rfl
  · exact Projectivization.Subspace.subset_span {x}

theorem secantSpanLocus_one : secantSpanLocus 1 = segre := by
  ext x
  constructor
  · rintro ⟨q, hq, hx⟩
    have hr : Set.range q = {q 0} := by
      ext y
      simp only [Set.mem_range, Set.mem_singleton_iff]
      constructor
      · rintro ⟨i, rfl⟩
        congr
        exact Subsingleton.elim _ _
      · intro hy
        exact ⟨0, hy.symm⟩
    rw [hr, projective_span_singleton, mem_pointSubspace] at hx
    exact hx ▸ hq 0
  · intro hx
    refine ⟨fun _ => x, fun _ => hx, ?_⟩
    apply Projectivization.Subspace.subset_span
    exact ⟨0, rfl⟩

/-- Projectivization of a genuine vector submodule. -/
def projectivizeSubmodule (L : Submodule ℂ Tensor) : Projectivization.Subspace ℂ Tensor where
  carrier := {x | x.submodule ≤ L}
  mem_add' v w hv hw hvw h₁ h₂ := by
    change (ℂ ∙ (v + w)) ≤ L
    rw [Submodule.span_singleton_le_iff_mem]
    exact L.add_mem ((Submodule.span_singleton_le_iff_mem _ _).mp h₁)
      ((Submodule.span_singleton_le_iff_mem _ _).mp h₂)

@[simp] theorem mk_mem_projectivizeSubmodule (L : Submodule ℂ Tensor)
    (v : Tensor) (hv : v ≠ 0) :
    Projectivization.mk ℂ v hv ∈ projectivizeSubmodule L ↔ v ∈ L :=
  Submodule.span_singleton_le_iff_mem _ _

/-- Adjoin the zero vector to all representatives of a projective subspace. -/
def vectorSubmodule (P : Projectivization.Subspace ℂ Tensor) : Submodule ℂ Tensor where
  carrier := {v | ∀ hv : v ≠ 0, Projectivization.mk ℂ v hv ∈ P}
  zero_mem' h := False.elim (h rfl)
  add_mem' {v w} h₁ h₂ hvw := by
    by_cases hv : v = 0
    · subst v
      simpa only [zero_add] using h₂ (by simpa only [zero_add] using hvw)
    by_cases hw : w = 0
    · subst w
      simpa only [add_zero] using h₁ (by simpa only [add_zero] using hvw)
    exact P.mem_add v w hv hw hvw (h₁ hv) (h₂ hw)
  smul_mem' c v h hcv := by
    have hv : v ≠ 0 := by
      intro hv
      exact hcv (by simp [hv])
    have he : Projectivization.mk ℂ (c • v) hcv = Projectivization.mk ℂ v hv :=
      (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨c, rfl⟩
    exact he ▸ h hv

@[simp] theorem mem_vectorSubmodule (P : Projectivization.Subspace ℂ Tensor)
    (v : Tensor) (hv : v ≠ 0) :
    v ∈ vectorSubmodule P ↔ Projectivization.mk ℂ v hv ∈ P := by
  exact ⟨fun h => h hv, fun h _ => h⟩

/-- Actual projective spans agree with the vector spans of any chosen nonzero representatives. -/
theorem projective_span_mk_iff {ι : Type*} (v : ι → Tensor) (hv : ∀ i, v i ≠ 0)
    (x : Tensor) (hx : x ≠ 0) :
    Projectivization.mk ℂ x hx ∈
        Projectivization.Subspace.span (Set.range (fun i => Projectivization.mk ℂ (v i) (hv i))) ↔
      x ∈ Submodule.span ℂ (Set.range v) := by
  let P := Projectivization.Subspace.span
    (Set.range (fun i => Projectivization.mk ℂ (v i) (hv i)))
  constructor
  · intro h
    have hle : P ≤ projectivizeSubmodule (Submodule.span ℂ (Set.range v)) := by
      apply Projectivization.Subspace.span_le_subspace_iff.mpr
      rintro p ⟨i, rfl⟩
      exact (mk_mem_projectivizeSubmodule _ _ _).mpr (Submodule.subset_span ⟨i, rfl⟩)
    exact (mk_mem_projectivizeSubmodule _ _ _).mp (hle h)
  · intro h
    have hle : Submodule.span ℂ (Set.range v) ≤ vectorSubmodule P := by
      apply Submodule.span_le.mpr
      rintro y ⟨i, rfl⟩
      apply (mem_vectorSubmodule _ _ (hv i)).mpr
      exact Projectivization.Subspace.subset_span _ ⟨i, rfl⟩
    exact (mem_vectorSubmodule _ _ hx).mp (hle h)

/-- The zero vector subspace has no projective points. -/
theorem projectivize_bot_empty :
    (projectivizeSubmodule (⊥ : Submodule ℂ Tensor) : Set ProjectiveTensor) = ∅ := by
  ext x
  constructor
  · intro hx
    have : x.rep ∈ (⊥ : Submodule ℂ Tensor) := by
      apply (mk_mem_projectivizeSubmodule _ _ x.rep_nonzero).mp
      simpa only [Projectivization.mk_rep] using hx
    exact x.rep_nonzero this
  · exact False.elim

theorem secantSpanLocus_zero : secantSpanLocus 0 = ∅ := by
  ext x
  constructor
  · rintro ⟨q, _, hx⟩
    have hle : Projectivization.Subspace.span (Set.range q) ≤
        projectivizeSubmodule (⊥ : Submodule ℂ Tensor) := by
      apply Projectivization.Subspace.span_le_subspace_iff.mpr
      rintro y ⟨i, _⟩
      exact Fin.elim0 i
    have := hle hx
    rw [← SetLike.mem_coe, projectivize_bot_empty] at this
    exact this
  · exact False.elim

theorem projectiveZariskiClosure_empty : projectiveZariskiClosure ∅ = ∅ := by
  ext x
  constructor
  · intro hx
    have h := hx 0 (MvPolynomial.C (1 : ℂ)) (MvPolynomial.isHomogeneous_C Coordinate (1 : ℂ))
      (by simp)
    have he := h x.rep x.rep_nonzero (Projectivization.mk_rep x)
    simp only [MvPolynomial.eval_C, one_ne_zero] at he
  · exact False.elim

theorem secantVariety_zero : secantVariety 0 = ∅ := by
  rw [secantVariety, secantSpanLocus_zero, projectiveZariskiClosure_empty]

/-- A fixed nonzero simple tensor used to replace zero terms in a decomposition. -/
theorem pure_e0_ne_zero : pure e0 e0 e0 ≠ 0 := by
  intro h
  have h₀ := congrArg (fun v => coords v (0, (0, 0))) h
  simp only [coords_pure, map_zero, Pi.zero_apply, e0, Matrix.cons_val_zero, mul_one] at h₀
  exact one_ne_zero h₀

/-- The unclosed projective span locus records actual decompositions with at most r
simple summands. Closure, rather than the span operation, is the source of border rank. -/
theorem mk_mem_secantSpanLocus_iff_rankLE (r : ℕ) (t : Tensor) (ht : t ≠ 0) :
    Projectivization.mk ℂ t ht ∈ secantSpanLocus r ↔ RankLE r t := by
  classical
  constructor
  · rintro ⟨q, hq, hmem⟩
    choose a b c hne heq using hq
    have hqeq : q = fun i => Projectivization.mk ℂ (pure (a i) (b i) (c i)) (hne i) := by
      funext i
      exact (heq i).symm
    rw [hqeq] at hmem
    have hs := (projective_span_mk_iff (fun i => pure (a i) (b i) (c i)) hne t ht).mp hmem
    obtain ⟨s, hs⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hs
    refine ⟨fun i => s i • a i, b, c, ?_⟩
    simpa only [pure_smul_left] using hs.symm
  · rintro ⟨a, b, c, hsum⟩
    let v : Fin r → Tensor := fun i =>
      if pure (a i) (b i) (c i) = 0 then pure e0 e0 e0 else pure (a i) (b i) (c i)
    have hv : ∀ i, v i ≠ 0 := by
      intro i
      dsimp [v]
      split_ifs with hi
      · exact pure_e0_ne_zero
      · exact hi
    refine ⟨fun i => Projectivization.mk ℂ (v i) (hv i), ?_, ?_⟩
    · intro i
      by_cases hi : pure (a i) (b i) (c i) = 0
      · refine ⟨e0, e0, e0, pure_e0_ne_zero, ?_⟩
        simp [v, hi]
      · refine ⟨a i, b i, c i, hi, ?_⟩
        simp [v, hi]
    · apply (projective_span_mk_iff v hv t ht).mpr
      rw [hsum]
      apply Submodule.sum_mem
      intro i _
      by_cases hi : pure (a i) (b i) (c i) = 0
      · simp only [hi, Submodule.zero_mem]
      · apply Submodule.subset_span
        exact ⟨i, by simp [v, hi]⟩

theorem mk_mem_secantSpanLocus_iff_tensorRank_le (r : ℕ) (t : Tensor) (ht : t ≠ 0) :
    Projectivization.mk ℂ t ht ∈ secantSpanLocus r ↔ tensorRank t ≤ r := by
  rw [mk_mem_secantSpanLocus_iff_rankLE, tensorRank_le_iff]

end Conjecture6891
