/- Axiom audit for the disproof of TLMC 00000000450.

Run with:  lake env lean Check.lean

Every line must print "does not depend on any axioms". -/

import Main

#print axioms C2_eq
#print axioms C2_ne_sqrt3_sq
#print axioms C3_eq
#print axioms C3_ne_claim
#print axioms C4_eq
#print axioms C5_eq
#print axioms C5_ne_claim
#print axioms C6_eq
#print axioms C1_eq
#print axioms count2
#print axioms count3
#print axioms count4
#print axioms count5
#print axioms seqs2_val
#print axioms C2_poly
