import Conjecture2802.Formula
import Mathlib.Data.EReal.Basic

noncomputable section
open scoped ContDiff

namespace Conjecture2802

/-- A finite real representative, with continuous derivatives through order two. -/
def RateC2On (I : ℝ → EReal) (S : Set ℝ) : Prop :=
  ∃ f : ℝ → ℝ, ContDiffOn ℝ 2 f S ∧ ∀ x ∈ S, I x = (f x : EReal)

/-- A real representative with two ordinary derivatives on the specified domain.
On an open domain the equality identifies the local derivatives of the actual rate. -/
def RateTwiceDifferentiableOn (I : ℝ → EReal) (S : Set ℝ) : Prop :=
  ∃ f : ℝ → ℝ, DifferentiableOn ℝ f S ∧ DifferentiableOn ℝ (deriv f) S ∧
    ∀ x ∈ S, I x = (f x : EReal)

/-- This is only the sufficient implication; mere twice differentiability need not be C². -/
theorem RateC2On.twiceDifferentiableOn {I : ℝ → EReal} {S : Set ℝ}
    (h : RateC2On I S) (hS : IsOpen S) : RateTwiceDifferentiableOn I S := by
  rcases h with ⟨f, hf, heq⟩
  refine ⟨f, hf.differentiableOn (by norm_num), ?_, heq⟩
  have hd : ContDiffOn ℝ 1 (deriv f) S := hf.deriv_of_isOpen hS (by norm_num)
  exact hd.differentiableOn (by norm_num)

/-- Every extended-real function has the empty-domain certificate, vacuously. -/
theorem rateC2On_empty (I : ℝ → EReal) : RateC2On I ∅ := by
  exact ⟨fun _ => 0, contDiffOn_const, by simp⟩

/-- Ordinary logarithm calculus gives smoothness on the nonempty interior interval. -/
theorem binaryRate_contDiffOn : ContDiffOn ℝ ∞ binaryRate (Set.Ioo 0 1) := by
  have hid : ContDiffOn ℝ ∞ (fun x : ℝ => x) (Set.Ioo 0 1) := contDiffOn_id
  have hsub : ContDiffOn ℝ ∞ (fun x : ℝ => 1 - x) (Set.Ioo 0 1) :=
    contDiffOn_const.sub hid
  have hlog : ContDiffOn ℝ ∞ Real.log (Set.Ioo 0 1) :=
    hid.log (fun _ hx => ne_of_gt hx.1)
  have hlogsub : ContDiffOn ℝ ∞ (fun x : ℝ => Real.log (1 - x)) (Set.Ioo 0 1) :=
    hsub.log (fun _ hx => ne_of_gt (sub_pos.mpr hx.2))
  exact (contDiffOn_const.add (hid.mul hlog)).add (hsub.mul hlogsub)

/-- The C² certificate transfers only through an exact equality of extended-real values. -/
theorem rateC2On_of_eq_binaryRate {I : ℝ → EReal}
    (h : ∀ x ∈ Set.Ioo (0 : ℝ) 1, I x = (binaryRate x : EReal)) :
    RateC2On I (Set.Ioo 0 1) := by
  refine ⟨binaryRate, binaryRate_contDiffOn.of_le ?_, h⟩
  exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)

end Conjecture2802
