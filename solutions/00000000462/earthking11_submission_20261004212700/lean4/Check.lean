/-
  Axiom audit for the formalisation in `Main.lean`.

  Build and run with:

      lake build
      lake env lean Check.lean

  Every theorem must report only the core axioms (`propext`, `Quot.sound`,
  possibly `Classical.choice`); in particular none may report `sorryAx`.
-/

import Main

open Tlmc462

-- Lucas numbers and the recurrence for the even-index Lucas numbers
#print axioms L_rec
#print axioms L_add_four
#print axioms M_rec

-- The sign sequence and the sequence u
#print axioms s_succ
#print axioms s_add_two
#print axioms u_rec

-- Iterated forms and the two vanishing parts
#print axioms u3
#print axioms u4
#print axioms u5
#print axioms u6
#print axioms P_zero
#print axioms Q_zero

-- The six-term recurrence for n·u(n)
#print axioms c_rec

-- Integrality and the spanning-tree sequence
#print axioms five_dvd_u
#print axioms five_dvd_c
#print axioms five_mul_tau
#print axioms tau_rec

-- Initial values (the known spanning-tree counts)
#print axioms tau_5
#print axioms tau_6
#print axioms tau_7
#print axioms tau_8
#print axioms tau_9
#print axioms tau_10
#print axioms tau_11
#print axioms tau_12

-- Coefficients and the factorisation of the characteristic polynomial
#print axioms char_factor
#print axioms char_square

-- The algebraic obstruction in Z[sqrt 3]
#print axioms alpha_sq
#print axioms alpha_sq_factor
#print axioms pEval_alpha_sq
#print axioms alpha_sq_ne_neg_one

-- The refutation
#print axioms conjecture_00000000462_false
