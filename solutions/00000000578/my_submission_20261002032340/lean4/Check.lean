import Main

/- Axiom audit: every line below must print
   "... does not depend on any axioms". -/

-- sanity: myXor agrees with core Nat.xor on 0..63
#eval ((List.range 64).all fun n => (List.range 64).all fun m => TLMC578.myXor n m == Nat.xor n m)

#print axioms TLMC578.myXor
#print axioms TLMC578.insertBasis
#print axioms TLMC578.rankOf
#print axioms TLMC578.rank
#print axioms TLMC578.pick
#print axioms TLMC578.vadd
#print axioms TLMC578.vadd_assoc
#print axioms TLMC578.vadd_comm
#print axioms TLMC578.chiTermV
#print axioms TLMC578.chiFromV
#print axioms TLMC578.chunkSumV
#print axioms TLMC578.chiTotalV
#print axioms TLMC578.vval
#print axioms TLMC578.chiNeg
#print axioms TLMC578.E53
#print axioms TLMC578.E62
#print axioms TLMC578.chiFromV_add
#print axioms TLMC578.chiFromV_eq_chunkSumV
#print axioms TLMC578.rankE53
#print axioms TLMC578.chiE53m1
#print axioms TLMC578.chiE53m2
#print axioms TLMC578.chiE53m3
#print axioms TLMC578.rankE62
#print axioms TLMC578.chiE62m1
#print axioms TLMC578.chiE62m2
#print axioms TLMC578.chiE62m3
#print axioms TLMC578.rem_nat_332
#print axioms TLMC578.rem_nat_2520
#print axioms TLMC578.int_rem_53
#print axioms TLMC578.int_rem_62
#print axioms TLMC578.not_dvd_int_12_332
#print axioms TLMC578.not_dvd_int_48_2520
#print axioms TLMC578.counter_bin53
#print axioms TLMC578.counter_bin62
#print axioms TLMC578.conjecture_00000000578_false
