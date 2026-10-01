import Main

/-!
Axiom audit for the disproof of TLMC conjecture 00000000589.
Every line below must print "... does not depend on any axioms".
-/

-- toolkit
#print axioms my_add_cancel_r
#print axioms my_add_right_comm
#print axioms my_le_exists
#print axioms my_le_of_add_le_add_right
#print axioms my_le_of_add_le_add_left
#print axioms my_sub_cancel
#print axioms my_add_sub_cancel'
#print axioms my_sub_add_cancel
#print axioms my_sub_sub
#print axioms my_sub_le_sub_left
#print axioms my_le_sub_right_of_add
#print axioms my_add_mul
#print axioms my_add_sub_assoc
#print axioms my_mul_cancel
#print axioms my_one_add

-- main development
#print axioms window
#print axioms repr_step
#print axioms repr_shifted
#print axioms repr_ge
#print axioms notrepr
#print axioms frobN_succ
#print axioms frob_family

-- concrete instances and certificates
#print axioms frob6
#print axioms frob20
#print axioms frob100
#print axioms cert6
#print axioms cert20
#print axioms cert100
#print axioms violation6
#print axioms violation20
#print axioms violation100
