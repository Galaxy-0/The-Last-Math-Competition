import Mathlib.RingTheory.HahnSeries.Valuation
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.Topology.Algebra.Valued.ValuedField
import Mathlib.Tactic

/-!
# A continuous valuation whose intrinsic value group is not an integer power

The field is the Hahn-series field with rational coefficients and rational exponents.
The valuation is the lowest exponent. Its finite values, attained on monomials, form Q.
The domain has the valuation topology; the codomain has `WithZeroTopology`.
-/

noncomputable section

namespace Counterexample5754

abbrev K := HahnSeries ℚ ℚ
abbrev ExtendedValue := Multiplicative (WithTop ℚ)ᵒᵈ

def additiveValuation : AddValuation K (WithTop ℚ) := HahnSeries.addVal ℚ ℚ

def valuation : Valuation K ExtendedValue := additiveValuation.toValuation

instance : Valued K ExtendedValue := Valued.mk' valuation

open WithZeroTopology

/-- Continuity for the canonical valuation topology on the Hahn field. -/
theorem valuation_continuous : Continuous (valuation : K → ExtendedValue) :=
  Valued.continuous_valuation

/-- Continuity also holds for the ordinary order topology on the extended value group. -/
theorem valuation_continuous_orderTopology :
    @Continuous K ExtendedValue inferInstance (Preorder.topology ExtendedValue) valuation := by
  apply continuous_generateFrom_iff.mpr
  rintro s ⟨a, rfl | rfl⟩
  · exact isOpen_Ioi.preimage valuation_continuous
  · exact _root_.isOpen_Iio.preimage valuation_continuous

/-- All finite rational values are realized by nonzero monomials. -/
theorem realizes_every_rational (q : ℚ) :
    ∃ x : K, x ≠ 0 ∧ additiveValuation x = (q : WithTop ℚ) := by
  refine ⟨HahnSeries.single q 1, HahnSeries.single_ne_zero one_ne_zero, ?_⟩
  exact HahnSeries.orderTop_single one_ne_zero

/-- The homomorphism from the multiplicative group of the field to additive exponents. -/
def valueHom : Additive Kˣ →+ ℚ where
  toFun u := ((Additive.toMul u : Kˣ) : K).order
  map_zero' := by simp
  map_add' u w := HahnSeries.order_mul (Units.ne_zero _) (Units.ne_zero _)

/-- The intrinsic value group: the image of the valuation on nonzero field elements. -/
def valueGroup : AddSubgroup ℚ := valueHom.range

/-- The unit homomorphism is exactly the finite part of the additive valuation. -/
theorem valueHom_agrees (u : Kˣ) :
    additiveValuation (u : K) = (valueHom (Additive.ofMul u) : WithTop ℚ) :=
  HahnSeries.addVal_apply_of_ne (Units.ne_zero u)

/-- Membership is precisely attainment as a finite value at a nonzero field element. -/
theorem mem_valueGroup_iff (q : ℚ) :
    q ∈ valueGroup ↔ ∃ x : K, x ≠ 0 ∧ additiveValuation x = (q : WithTop ℚ) := by
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨((Additive.toMul u : Kˣ) : K), Units.ne_zero _, valueHom_agrees _⟩
  · rintro ⟨x, hx, hq⟩
    refine ⟨Additive.ofMul (Units.mk0 x hx), ?_⟩
    exact WithTop.coe_inj.mp ((valueHom_agrees (Units.mk0 x hx)).symm.trans hq)

theorem valueGroup_eq_top : valueGroup = ⊤ := by
  apply top_unique
  intro q _
  refine ⟨Additive.ofMul (Units.mk0 (HahnSeries.single q (1 : ℚ))
    (HahnSeries.single_ne_zero one_ne_zero)), ?_⟩
  exact HahnSeries.order_single one_ne_zero

/-- The intrinsic value group is Q, as an additive group. -/
def valueGroupEquiv : valueGroup ≃+ ℚ :=
  AddEquiv.ofBijective valueGroup.subtype ⟨Subtype.val_injective, fun q => by
    refine ⟨⟨q, ?_⟩, rfl⟩
    rw [valueGroup_eq_top]
    trivial⟩

/-- A divisible nontrivial group cannot be any Cartesian power of Z. -/
theorem rationals_not_integer_power (I : Type*) : IsEmpty (ℚ ≃+ (I → ℤ)) := by
  refine ⟨fun e => ?_⟩
  classical
  by_cases h : Nonempty I
  · obtain ⟨i⟩ := h
    let x := e.symm (fun _ => (1 : ℤ))
    let y := x / 2
    have hhalf : y + y = x := by dsimp [y]; ring
    have he : e y + e y = (fun _ => (1 : ℤ)) := by
      rw [← e.map_add, hhalf]
      exact e.apply_symm_apply _
    have hi : (e y) i + (e y) i = 1 := congrFun he i
    omega
  · haveI : IsEmpty I := not_nonempty_iff.mp h
    have he : e 0 = e 1 := Subsingleton.elim _ _
    have hz : (0 : ℚ) = 1 := e.injective he
    norm_num at hz

/-- The obstruction concerns the intrinsic image group, not an artificially large codomain. -/
theorem valueGroup_not_integer_power (I : Type*) : IsEmpty (valueGroup ≃+ (I → ℤ)) := by
  refine ⟨fun e => ?_⟩
  exact (rationals_not_integer_power I).false (valueGroupEquiv.symm.trans e)

/-- No choice of a natural-number rank can make the last clause of the conjecture hold. -/
theorem not_rank_indexed_integer_power :
    ¬ ∃ rank : ℕ, Nonempty (valueGroup ≃+ (Fin rank → ℤ)) := by
  rintro ⟨rank, ⟨e⟩⟩
  exact (valueGroup_not_integer_power (Fin rank)).false e

/-- A single continuous valuation contradicts the claimed integer-power conclusion. -/
theorem continuous_valuation_counterexample :
    Continuous (valuation : K → ExtendedValue) ∧
    @Continuous K ExtendedValue inferInstance (Preorder.topology ExtendedValue) valuation ∧
    (∀ q : ℚ, ∃ x : K, x ≠ 0 ∧ additiveValuation x = (q : WithTop ℚ)) ∧
    (∀ I : Type, IsEmpty (valueGroup ≃+ (I → ℤ))) ∧
    ¬ ∃ rank : ℕ, Nonempty (valueGroup ≃+ (Fin rank → ℤ)) :=
  ⟨valuation_continuous, valuation_continuous_orderTopology, realizes_every_rational,
    valueGroup_not_integer_power,
    not_rank_indexed_integer_power⟩

end Counterexample5754
