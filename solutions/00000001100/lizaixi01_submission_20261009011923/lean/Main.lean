import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
import Mathlib.GroupTheory.GroupAction.Primitive
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Prime.Infinite

/-!
# Refutation of source 00000001100

The affine group is the actual group of affine equivalences of the field line.
Its natural action is evaluation. Orbit count means cardinality of the actual
orbit-relation quotient. The final family refutes even an eventual uniform
q + O(1) bound, with q equal to the field cardinality.
-/

namespace Affine1100

variable (K : Type) [Field K]

abbrev AffineGroup := K ≃ᵃ[K] K

instance naturalAction : MulAction (AffineGroup K) K where
  smul f x := f x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

instance finiteAffineGroup [Finite K] : Finite (AffineGroup K) :=
  Finite.of_injective (fun f : AffineGroup K => (f : K → K)) DFunLike.coe_injective

def zeroStabilizer : Subgroup (AffineGroup K) :=
  MulAction.stabilizer (AffineGroup K) (0 : K)

@[simp] theorem mem_zeroStabilizer (f : AffineGroup K) :
    f ∈ zeroStabilizer K ↔ f 0 = 0 := Iff.rfl

def scaling (u : Kˣ) : AffineGroup K :=
  (LinearEquiv.smulOfUnit (M := K) u).toAffineEquiv

@[simp] theorem scaling_apply (u : Kˣ) (x : K) :
    scaling K u x = (u : K) * x := rfl

theorem move_nonzero {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ h : zeroStabilizer K, h • x = y := by
  let u : Kˣ := Units.mk0 (y / x) (div_ne_zero hy hx)
  refine ⟨⟨scaling K u, ?_⟩, ?_⟩
  · change scaling K u (0 : K) = 0
    rw [scaling_apply, mul_zero]
  · change scaling K u x = y
    rw [scaling_apply]
    exact div_mul_cancel₀ y hx

theorem zeroStabilizer_ne_top : zeroStabilizer K ≠ ⊤ := by
  intro htop
  have hmem : AffineEquiv.constVAdd K K (1 : K) ∈ zeroStabilizer K := by
    rw [htop]
    trivial
  have hfix := (mem_zeroStabilizer K _).mp hmem
  simp at hfix

/-- The point stabilizer is a genuine maximal proper subgroup. -/
theorem zeroStabilizer_isCoatom : IsCoatom (zeroStabilizer K) := by
  rw [SetLike.isCoatom_iff]
  refine ⟨zeroStabilizer_ne_top K, ?_⟩
  intro J f hHJ hfH hfJ
  apply top_unique
  intro g _
  by_cases hgH : g ∈ zeroStabilizer K
  · exact hHJ hgH
  have hf0 : f 0 ≠ 0 := by simpa using hfH
  have hg0 : g 0 ≠ 0 := by simpa using hgH
  obtain ⟨h, hh⟩ := move_nonzero K hf0 hg0
  let a : AffineGroup K := (h : AffineGroup K) * f
  have ha0 : a 0 = g 0 := hh
  have haJ : a ∈ J := J.mul_mem (hHJ h.property) hfJ
  have hrH : a⁻¹ * g ∈ zeroStabilizer K := by
    change a.symm (g 0) = 0
    rw [← ha0]
    exact a.symm_apply_apply 0
  have hrJ : a⁻¹ * g ∈ J := hHJ hrH
  have hproduct : a * (a⁻¹ * g) ∈ J := J.mul_mem haJ hrJ
  simpa using hproduct

/-- This count is defined from the actual action, not stipulated numerically. -/
noncomputable def orbitCount (H : Subgroup (AffineGroup K)) : Nat :=
  Nat.card (MulAction.orbitRel.Quotient H K)

/-- The actual orbit equivalence relation has precisely zero and nonzero classes. -/
theorem zeroStabilizer_orbitRel_iff (x y : K) :
    MulAction.orbitRel (zeroStabilizer K) K x y ↔ (x = 0 ↔ y = 0) := by
  change (∃ h : zeroStabilizer K, h • y = x) ↔ (x = 0 ↔ y = 0)
  constructor
  · rintro ⟨h, hxy⟩
    have h0 : (h : AffineGroup K) 0 = 0 := h.property
    change (h : AffineGroup K) y = x at hxy
    constructor
    · intro hx
      apply (h : AffineGroup K).injective
      rw [hxy, hx, h0]
    · intro hy
      rw [hy, h0] at hxy
      exact hxy.symm
  · intro hiff
    by_cases hy : y = 0
    · have hx : x = 0 := hiff.mpr hy
      subst x
      subst y
      exact ⟨1, by simp⟩
    · have hx : x ≠ 0 := mt hiff.mp hy
      exact move_nonzero K hy hx

/-- A concrete equivalence of the genuine orbit quotient with its two classes. -/
noncomputable def zeroStabilizer_orbitQuotientEquivBool :
    MulAction.orbitRel.Quotient (zeroStabilizer K) K ≃ Bool := by
  classical
  refine {
    toFun := Quotient.lift (fun x : K => decide (x = 0)) ?_
    invFun := fun b => Quotient.mk _ (if b then (0 : K) else 1)
    left_inv := ?_
    right_inv := ?_ }
  · intro x y hxy
    have hiff := (zeroStabilizer_orbitRel_iff K x y).mp hxy
    by_cases hx : x = 0
    · have hy : y = 0 := hiff.mp hx
      simp [hx, hy]
    · have hy : y ≠ 0 := mt hiff.mpr hx
      simp [hx, hy]
  · intro q
    refine Quotient.inductionOn q ?_
    intro x
    apply Quotient.sound
    apply (zeroStabilizer_orbitRel_iff K _ _).mpr
    by_cases hx : x = 0 <;> simp [hx]
  · intro b
    cases b <;> simp

theorem zeroStabilizer_orbitCount : orbitCount K (zeroStabilizer K) = 2 := by
  unfold orbitCount
  rw [Nat.card_congr (zeroStabilizer_orbitQuotientEquivBool K)]
  simp

/-- Counterexamples beyond every bound and threshold, in genuine prime fields. -/
theorem arbitrarily_large_maximal_counterexamples (C q0 : Nat) :
    ∃ (p : Nat) (hp : Nat.Prime p),
      letI : Fact (Nat.Prime p) := ⟨hp⟩
      ∃ H : Subgroup (AffineGroup (ZMod p)),
        IsCoatom H ∧ q0 ≤ p ∧ orbitCount (ZMod p) H = 2 ∧
          orbitCount (ZMod p) H + C < p := by
  obtain ⟨p, hbound, hp⟩ := Nat.exists_infinite_primes (max q0 (C + 3))
  refine ⟨p, hp, ?_⟩
  let : Fact (Nat.Prime p) := ⟨hp⟩
  refine ⟨zeroStabilizer (ZMod p), zeroStabilizer_isCoatom (ZMod p), ?_,
    zeroStabilizer_orbitCount (ZMod p), ?_⟩
  · exact le_trans (le_max_left _ _) hbound
  · rw [zeroStabilizer_orbitCount]
    have hlarge : C + 3 ≤ p := le_trans (le_max_right _ _) hbound
    omega

/-- A necessary, deliberately weaker consequence of any eventual uniform q+O(1). -/
def EventuallyUniformLowerBound : Prop :=
  ∃ C q0 : Nat, ∀ (p : Nat) (hp : Nat.Prime p),
    letI : Fact (Nat.Prime p) := ⟨hp⟩
    ∀ H : Subgroup (AffineGroup (ZMod p)), IsCoatom H → q0 ≤ p →
      p ≤ orbitCount (ZMod p) H + C

theorem not_eventuallyUniformLowerBound : ¬ EventuallyUniformLowerBound := by
  rintro ⟨C, q0, h⟩
  obtain ⟨p, hp, H, hmax, hq0, _, hlarge⟩ :=
    arbitrarily_large_maximal_counterexamples C q0
  exact (not_le_of_gt hlarge) (h p hp H hmax hq0)

/-- Exact signed-deviation reading of the necessary orbit-count clause.

`q0` permits every finite exception. The integer `c` is the actual difference
between two natural cardinalities. It may be positive, negative, or zero.
-/
def OrbitCountClause : Prop :=
  ∃ C q0 : Nat, ∀ (p : Nat) (hp : Nat.Prime p),
    letI : Fact (Nat.Prime p) := ⟨hp⟩
    ∀ H : Subgroup (AffineGroup (ZMod p)), IsCoatom H → q0 ≤ p →
      ∃ c : Int, (orbitCount (ZMod p) H : Int) = (p : Int) + c ∧ c.natAbs ≤ C

theorem orbitCountClause_implies_lowerBound : OrbitCountClause → EventuallyUniformLowerBound := by
  rintro ⟨C, q0, h⟩
  refine ⟨C, q0, ?_⟩
  intro p hp
  let : Fact (Nat.Prime p) := ⟨hp⟩
  intro H hmax hq0
  obtain ⟨c, heq, hc⟩ := h p hp H hmax hq0
  have hc_lower : -(C : Int) ≤ c := by
    have habs : -c ≤ (c.natAbs : Int) := by
      simpa using (Int.le_natAbs (a := -c))
    omega
  omega

/-- The prime-field restriction of the count clause is already false. -/
theorem not_primeFieldOrbitCountClause : ¬ OrbitCountClause :=
  fun h => not_eventuallyUniformLowerBound (orbitCountClause_implies_lowerBound h)

/-- The source's necessary count clause for all finite fields, even eventually.

The field cardinality is `Nat.card F`; the subgroup action is the genuine
natural evaluation action of `AffineGroup F` on the field line.
-/
def FiniteFieldOrbitCountClause : Prop :=
  ∃ C q0 : Nat, ∀ (F : Type) [Field F] [Finite F],
    ∀ H : Subgroup (AffineGroup F), IsCoatom H → q0 ≤ Nat.card F →
      ∃ c : Int, (orbitCount F H : Int) = (Nat.card F : Int) + c ∧ c.natAbs ≤ C

theorem finiteFieldClause_implies_primeFieldClause :
    FiniteFieldOrbitCountClause → OrbitCountClause := by
  rintro ⟨C, q0, h⟩
  refine ⟨C, q0, ?_⟩
  intro p hp
  let : Fact (Nat.Prime p) := ⟨hp⟩
  intro H hmax hq0
  have hcount := h (ZMod p) H hmax (by simpa using hq0)
  simpa using hcount

/-- Refutation of the necessary first conjunct, with all finite-field quantifiers. -/
theorem refutation_00000001100 : ¬ FiniteFieldOrbitCountClause :=
  fun h => not_primeFieldOrbitCountClause (finiteFieldClause_implies_primeFieldClause h)

/-- No interpretation of the additional clause can make the conjunction true. -/
theorem refutation_with_additional_clause (additionalClause : Prop) :
    ¬ (FiniteFieldOrbitCountClause ∧ additionalClause) :=
  fun h => refutation_00000001100 h.1

#print axioms zeroStabilizer_isCoatom
#print axioms zeroStabilizer_orbitCount
#print axioms arbitrarily_large_maximal_counterexamples
#print axioms refutation_00000001100

end Affine1100
