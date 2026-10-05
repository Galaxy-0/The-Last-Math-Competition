import Conjecture1554.Geometry
import Conjecture1554.Coloring

noncomputable section
namespace Conjecture1554

/-- A total two-coloring of the ordinary Euclidean plane by alternating half-open strips. -/
def stripeColor (p : Plane) : Bool := scalarColor stripWidth (height p)

/-- Three vertices of one color whose three actual Euclidean distances are one. -/
def HasMonochromaticUnitTriangle (c : Plane → Bool) : Prop :=
  ∃ p q r : Plane, unitEquilateral p q r ∧ c p = c q ∧ c q = c r

/-- The explicit first assertion in both language versions of conjecture 00000001554. -/
def UnitTriangleRamsey : Prop :=
  ∀ c : Plane → Bool, HasMonochromaticUnitTriangle c

/-- Both colors occur; the counterexample is a partition into two nonempty classes. -/
theorem stripeColor_surjective : Function.Surjective stripeColor := by
  intro b
  cases b with
  | false =>
      refine ⟨(WithLp.equiv 2 _).symm ![0, stripWidth], ?_⟩
      exact scalarColor_width stripWidth_pos
  | true =>
      refine ⟨(WithLp.equiv 2 _).symm ![0, 0], ?_⟩
      exact scalarColor_zero stripWidth

theorem ordered_triangle_not_monochromatic {p q r : Plane}
    (h : unitEquilateral p q r) (hpq : height p ≤ height q)
    (hqr : height q ≤ height r) :
    ¬ (stripeColor p = stripeColor q ∧ stripeColor q = stripeColor r) := by
  obtain ⟨ha, hb, hab⟩ := ordered_height_bounds h hpq hqr
  exact ordered_not_all_sameColor stripWidth_pos hpq hqr ha hb hab

/-- All six weak height orders are covered, including equal heights. -/
theorem triangle_not_monochromatic {p q r : Plane} (h : unitEquilateral p q r) :
    ¬ (stripeColor p = stripeColor q ∧ stripeColor q = stripeColor r) := by
  intro hc
  have hpq : dist p q = 1 := h.1
  have hqr : dist q r = 1 := h.2.1
  have hrp : dist r p = 1 := h.2.2
  have hqp : dist q p = 1 := by rw [dist_comm]; exact hpq
  have hrq : dist r q = 1 := by rw [dist_comm]; exact hqr
  have hpr : dist p r = 1 := by rw [dist_comm]; exact hrp
  rcases le_total (height p) (height q) with hpq' | hqp'
  · rcases le_total (height q) (height r) with hqr' | hrq'
    · exact ordered_triangle_not_monochromatic h hpq' hqr' hc
    · rcases le_total (height p) (height r) with hpr' | hrp'
      · exact ordered_triangle_not_monochromatic ⟨hpr, hrq, hqp⟩ hpr' hrq'
          ⟨hc.1.trans hc.2, hc.2.symm⟩
      · exact ordered_triangle_not_monochromatic ⟨hrp, hpq, hqr⟩ hrp' hpq'
          ⟨(hc.1.trans hc.2).symm, hc.1⟩
  · rcases le_total (height p) (height r) with hpr' | hrp'
    · exact ordered_triangle_not_monochromatic ⟨hqp, hpr, hrq⟩ hqp' hpr'
        ⟨hc.1.symm, hc.1.trans hc.2⟩
    · rcases le_total (height q) (height r) with hqr' | hrq'
      · exact ordered_triangle_not_monochromatic ⟨hqr, hrp, hpq⟩ hqr' hrp'
          ⟨hc.2, (hc.1.trans hc.2).symm⟩
      · exact ordered_triangle_not_monochromatic ⟨hrq, hqp, hpr⟩ hrq' hqp'
          ⟨hc.2.symm, hc.1.symm⟩

theorem stripeColor_has_no_monochromatic_unit_triangle :
    ¬ HasMonochromaticUnitTriangle stripeColor := by
  rintro ⟨p, q, r, ht, hc⟩
  exact triangle_not_monochromatic ht hc

/-- The conjecture's universal unit-length assertion is false. -/
theorem unit_triangle_ramsey_false : ¬ UnitTriangleRamsey := by
  intro h
  exact stripeColor_has_no_monochromatic_unit_triangle (h stripeColor)

end Conjecture1554
