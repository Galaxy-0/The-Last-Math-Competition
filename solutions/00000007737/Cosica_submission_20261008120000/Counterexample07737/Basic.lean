import Mathlib

/-!
  Formal component for the counterexample to conjecture 00000007737.

  The conjecture's claimed formula at `k = 2` is `16 / exp 2`. This file
  proves that this number is strictly larger than `1`, derives the spectrum
  bound for products of positive contractions, and transports it to the
  support of every scalar spectral probability law of such a product.
-/

noncomputable section

open Set
open MeasureTheory
open scoped CStarAlgebra

def claimedEndpoint : ℝ := 16 / Real.exp 2

def lowerEndpoint (S : Set ℝ) : ℝ := sInf S

theorem lowerEndpoint_le_one {S : Set ℝ} (hS : S.Nonempty)
    (hcontained : S ⊆ Set.Icc (0 : ℝ) 1) : lowerEndpoint S ≤ 1 := by
  rcases hS with ⟨x, hx⟩
  calc
    lowerEndpoint S = sInf S := rfl
    _ ≤ x := csInf_le ⟨0, fun y hy => (hcontained hy).1⟩ hx
    _ ≤ 1 := (hcontained hx).2

theorem claimedEndpoint_gt_one : 1 < claimedEndpoint := by
  have hExpOne : Real.exp (1 : ℝ) < 3 := Real.exp_one_lt_three
  have hExpTwo : Real.exp (2 : ℝ) < 9 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_pos (1 : ℝ)]
  rw [claimedEndpoint, lt_div_iff₀ (Real.exp_pos 2)]
  linarith

/- The operator-level part applies to all positive contractions, so freeness
and uniformity are not needed for this necessary support bound. -/
section Operators

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def positiveProduct (a b : A) : A := CFC.sqrt a * b * CFC.sqrt a

theorem positiveProduct_nonneg {a b : A} (hb : 0 ≤ b) :
    0 ≤ positiveProduct a b :=
  conjugate_nonneg_of_nonneg hb (CFC.sqrt_nonneg a)

theorem positiveProduct_le_one {a b : A} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hb1 : b ≤ 1) : positiveProduct a b ≤ 1 := by
  calc
    positiveProduct a b ≤ CFC.sqrt a * 1 * CFC.sqrt a :=
      conjugate_le_conjugate_of_nonneg hb1 (CFC.sqrt_nonneg a)
    _ = a := by simpa using CFC.sqrt_mul_sqrt_self a ha
    _ ≤ 1 := ha1

theorem positiveProduct_spectrum_subset [Nontrivial A] {a b : A} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    spectrum ℝ (positiveProduct a b) ⊆ Set.Icc (0 : ℝ) 1 := by
  have hp := positiveProduct_nonneg (a := a) hb
  have hn : ‖positiveProduct a b‖ ≤ 1 :=
    (CStarAlgebra.norm_le_iff_le_algebraMap _ (by norm_num : (0 : ℝ) ≤ 1) hp).2
      (by simpa using positiveProduct_le_one ha ha1 hb1)
  intro x hx
  exact ⟨spectrum_nonneg_of_nonneg hp hx,
    (Real.le_norm_self x).trans ((spectrum.norm_le_norm_of_mem hx).trans hn)⟩

/-- The scalar law of an operator is a probability measure on its spectrum,
viewed as a measure on the real line via the inclusion map. This covers every
state's spectral distribution, independently of faithfulness. -/
def spectralLaw (c : A) (ρ : Measure (spectrum ℝ c)) : Measure ℝ :=
  ρ.map (fun x : spectrum ℝ c => (x : ℝ))

omit [PartialOrder A] [StarOrderedRing A] in
theorem spectralLaw_support_subset {c : A} (ρ : Measure (spectrum ℝ c))
    (hc : spectrum ℝ c ⊆ Set.Icc (0 : ℝ) 1) :
    (spectralLaw c ρ).support ⊆ Set.Icc (0 : ℝ) 1 := by
  apply Measure.support_subset_of_isClosed isClosed_Icc
  change ∀ᵐ x ∂(ρ.map (fun x : spectrum ℝ c => (x : ℝ))), x ∈ Set.Icc (0 : ℝ) 1
  apply (ae_map_iff measurable_subtype_coe.aemeasurable
    (show MeasurableSet {x : ℝ | x ∈ Set.Icc (0 : ℝ) 1} from measurableSet_Icc)).2
  exact Filter.Eventually.of_forall fun x => hc x.property

omit [PartialOrder A] [StarOrderedRing A] in
theorem spectralLaw_support_nonempty {c : A} (ρ : Measure (spectrum ℝ c))
    [IsProbabilityMeasure ρ] : (spectralLaw c ρ).support.Nonempty := by
  apply Measure.nonempty_support
  exact (Measure.map_ne_zero_iff measurable_subtype_coe.aemeasurable).2
    (IsProbabilityMeasure.ne_zero ρ)

/-- No spectral distribution of a positive-contraction product can have the
claimed lower endpoint at k = 2. In particular this excludes the distribution
used to define the free multiplicative convolution of two uniform laws. -/
theorem positiveProduct_law_refutes_endpoint [Nontrivial A] {a b : A}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (ρ : Measure (spectrum ℝ (positiveProduct a b))) [IsProbabilityMeasure ρ] :
    lowerEndpoint (spectralLaw (positiveProduct a b) ρ).support ≠ claimedEndpoint := by
  intro h
  have hle := lowerEndpoint_le_one (spectralLaw_support_nonempty ρ)
    (spectralLaw_support_subset ρ (positiveProduct_spectrum_subset ha ha1 hb hb1))
  rw [h] at hle
  exact (not_le_of_gt claimedEndpoint_gt_one) hle

end Operators

def conjecturedEndpoint (k : ℕ) : ℝ :=
  Real.exp (-2 * (k : ℝ) + 2) * (k : ℝ) ^ (2 * (k : ℝ) / ((k : ℝ) - 1))

theorem conjecturedEndpoint_two : conjecturedEndpoint 2 = claimedEndpoint := by
  norm_num [conjecturedEndpoint, claimedEndpoint, Real.exp_neg, Real.rpow_natCast]
  ring

#print axioms positiveProduct_law_refutes_endpoint
#print axioms conjecturedEndpoint_two

/-- The conjecture's actual formula fails at k = 2 for every scalar spectral
law of a product of positive contractions. The free, uniform case is a
specialization of this stronger operator statement. -/
theorem conjecture_00000007737_endpoint_false
    {A : Type*} [CStarAlgebra A] [Nontrivial A] [PartialOrder A] [StarOrderedRing A]
    {a b : A} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (ρ : Measure (spectrum ℝ (positiveProduct a b))) [IsProbabilityMeasure ρ] :
    lowerEndpoint (spectralLaw (positiveProduct a b) ρ).support ≠ conjecturedEndpoint 2 := by
  rw [conjecturedEndpoint_two]
  exact positiveProduct_law_refutes_endpoint ha ha1 hb hb1 ρ

#print axioms conjecture_00000007737_endpoint_false

theorem claimed_formula_incompatible_with_unit_support {S : Set ℝ}
    (hS : S.Nonempty) (hcontained : S ⊆ Set.Icc (0 : ℝ) 1) :
    lowerEndpoint S ≠ claimedEndpoint := by
  intro h
  have hle : lowerEndpoint S ≤ 1 := lowerEndpoint_le_one hS hcontained
  have hgt : 1 < lowerEndpoint S := by simpa [h] using claimedEndpoint_gt_one
  linarith
