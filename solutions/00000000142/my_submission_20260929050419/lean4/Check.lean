import Main
/-!
Axiom audit for the disproof of TLMC conjecture 00000000142.
Every theorem must report "does not depend on any axioms".
Run: lake env lean Check.lean   (after `lake build`)
-/

#print axioms bev_add_self
#print axioms bev_two_mul
#print axioms even_composite
#print axioms diag_step_zero
#print axioms diag_eq_one
#print axioms diag_1000
#print axioms entry_sym
#print axioms entry_mul_sym
#print axioms trRow_eq_rowSum
#print axioms trSq_eq_pc_aux
#print axioms traceSq_eq_pairCount
#print axioms pairCount_8
#print axioms pairCount_64
#print axioms pairCount_128
#print axioms moment_gt_one_64
#print axioms moment_gt_one_128
#print axioms moment_growth
#print axioms traceSq_64
