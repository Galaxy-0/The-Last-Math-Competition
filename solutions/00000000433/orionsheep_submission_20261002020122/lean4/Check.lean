/-
  Axiom audit for the disproof of TMC conjecture 00000000433.
  Run after `lake build` with:  lake env lean Check.lean

  Expected output: every theorem "does not depend on any axioms".
-/
import Main

#print axioms exponentsB2_val
#print axioms exponentsB2_pairwise_distinct
#print axioms T_B2
#print axioms conjecture_00000000433_B2_false
