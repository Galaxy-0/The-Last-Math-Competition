import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace Conjecture1554

/-- The index of the lower-closed, upper-open horizontal strip. -/
noncomputable def stripIndex (w y : ℝ) : ℤ := Int.floor (y / w)

/-- True and false are the two colors, given by integer parity. -/
noncomputable def scalarColor (w y : ℝ) : Bool := decide (stripIndex w y % 2 = 0)

theorem stripIndex_mono {w a b : ℝ} (hw : 0 < w) (hab : a ≤ b) :
    stripIndex w a ≤ stripIndex w b := by
  exact Int.floor_mono ((div_le_div_iff_of_pos_right hw).2 hab)

theorem stripIndex_le_add_one {w a b : ℝ} (hw : 0 < w) (hgap : b - a ≤ w) :
    stripIndex w b ≤ stripIndex w a + 1 := by
  have hdiv : b / w - a / w ≤ 1 := by
    have h := (div_le_div_iff_of_pos_right hw).2 hgap
    simpa only [sub_div, div_self (ne_of_gt hw)] using h
  have ha := Int.lt_floor_add_one (a / w)
  change Int.floor (b / w) ≤ Int.floor (a / w) + 1
  apply Int.floor_le_iff.mpr
  push_cast
  linarith

theorem stripIndex_eq_of_sameColor_of_gap_le {w a b : ℝ} (hw : 0 < w)
    (hab : a ≤ b) (hgap : b - a ≤ w) (hcolor : scalarColor w a = scalarColor w b) :
    stripIndex w a = stripIndex w b := by
  have hlo := stripIndex_mono hw hab
  have hhi := stripIndex_le_add_one hw hgap
  have hpar : (stripIndex w a % 2 = 0) ↔ (stripIndex w b % 2 = 0) := by
    simpa only [scalarColor, decide_eq_decide] using hcolor
  omega

theorem gap_lt_of_stripIndex_eq {w a b : ℝ} (hw : 0 < w)
    (hindex : stripIndex w a = stripIndex w b) : b - a < w := by
  have ha := Int.floor_le (a / w)
  have hb := Int.lt_floor_add_one (b / w)
  change Int.floor (a / w) = Int.floor (b / w) at hindex
  rw [← hindex] at hb
  have hdiv : (b - a) / w < 1 := by
    rw [sub_div]
    linarith
  exact (div_lt_one hw).mp hdiv

theorem ordered_not_all_sameColor {w a b c : ℝ} (hw : 0 < w)
    (hab : a ≤ b) (hbc : b ≤ c) (habgap : b - a ≤ w) (hbcgap : c - b ≤ w)
    (hspan : w ≤ c - a) :
    ¬ (scalarColor w a = scalarColor w b ∧ scalarColor w b = scalarColor w c) := by
  intro hc
  have hiab := stripIndex_eq_of_sameColor_of_gap_le hw hab habgap hc.1
  have hibc := stripIndex_eq_of_sameColor_of_gap_le hw hbc hbcgap hc.2
  have hlt := gap_lt_of_stripIndex_eq hw (hiab.trans hibc)
  linarith

theorem scalarColor_zero (w : ℝ) : scalarColor w 0 = true := by
  simp [scalarColor, stripIndex]

theorem scalarColor_width {w : ℝ} (hw : 0 < w) : scalarColor w w = false := by
  simp [scalarColor, stripIndex, ne_of_gt hw]

end Conjecture1554
