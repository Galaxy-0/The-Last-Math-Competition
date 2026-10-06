import Counterexample

noncomputable section

#print Counterexample5754.K
#print Counterexample5754.ExtendedValue
#print Counterexample5754.additiveValuation
#print Counterexample5754.valuation
#print Counterexample5754.valueHom
#print Counterexample5754.valueGroup
#check @Counterexample5754.valueHom_agrees
#check @Counterexample5754.mem_valueGroup_iff
#check @Counterexample5754.valueGroup_eq_top
#check @Counterexample5754.valueGroupEquiv
#check @Counterexample5754.rationals_not_integer_power
#check @Counterexample5754.valueGroup_not_integer_power
#check @Counterexample5754.valuation_continuous
#check @Counterexample5754.valuation_continuous_orderTopology
#check @Counterexample5754.not_rank_indexed_integer_power
#print Counterexample5754.continuous_valuation_counterexample
#print axioms Counterexample5754.valueHom_agrees
#print axioms Counterexample5754.mem_valueGroup_iff
#print axioms Counterexample5754.valueGroup_eq_top
#print axioms Counterexample5754.valueGroupEquiv
#print axioms Counterexample5754.rationals_not_integer_power
#print axioms Counterexample5754.valueGroup_not_integer_power
#print axioms Counterexample5754.valuation_continuous
#print axioms Counterexample5754.valuation_continuous_orderTopology
#print axioms Counterexample5754.not_rank_indexed_integer_power
#print axioms Counterexample5754.continuous_valuation_counterexample

example : Field Counterexample5754.K := inferInstance
example : IsTopologicalDivisionRing Counterexample5754.K := inferInstance
example : T2Space Counterexample5754.K := inferInstance

set_option pp.explicit true in
#check @Counterexample5754.continuous_valuation_counterexample
