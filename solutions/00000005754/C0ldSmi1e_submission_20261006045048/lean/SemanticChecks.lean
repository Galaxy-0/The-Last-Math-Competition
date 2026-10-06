import Counterexample

noncomputable section
open Counterexample5754
open WithZeroTopology

example : Field K := inferInstance
example : IsTopologicalDivisionRing K := inferInstance
example : T2Space K := inferInstance
example : (Valued.v : Valuation K ExtendedValue) = valuation := rfl
example : (inferInstance : TopologicalSpace K) =
    (Valued.mk' valuation).toUniformSpace.toTopologicalSpace := rfl
example : @Continuous K ExtendedValue
    (Valued.mk' valuation).toUniformSpace.toTopologicalSpace
    WithZeroTopology.topologicalSpace valuation := valuation_continuous
example : @Continuous K ExtendedValue
    (Valued.mk' valuation).toUniformSpace.toTopologicalSpace
    (Preorder.topology ExtendedValue) valuation := valuation_continuous_orderTopology
example : valuation = HahnSeries.addVal ℚ ℚ := rfl
example (x : K) : additiveValuation x = x.orderTop := rfl
example (q : ℚ) : q ∈ valueGroup ↔
    ∃ x : K, x ≠ 0 ∧ additiveValuation x = (q : WithTop ℚ) := mem_valueGroup_iff q
example (I : Type*) : IsEmpty (valueGroup ≃+ (I → ℤ)) := valueGroup_not_integer_power I
set_option pp.universes true in
#check @rationals_not_integer_power
set_option pp.explicit true in
#check @valuation_continuous
set_option pp.explicit true in
#check @valuation_continuous_orderTopology
#print axioms continuous_valuation_counterexample
