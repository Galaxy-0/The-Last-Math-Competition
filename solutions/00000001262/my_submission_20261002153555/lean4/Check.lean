import Lean
import Main

/-! Verification harness: every theorem of `Main.lean` must be axiom-free. -/

#print axioms Tlmc1262.ph_succ
#print axioms Tlmc1262.ph_shift3
#print axioms Tlmc1262.ch_shift
#print axioms Tlmc1262.A_succ
#print axioms Tlmc1262.A_step0
#print axioms Tlmc1262.A_step1
#print axioms Tlmc1262.A_step2
#print axioms Tlmc1262.sum3
#print axioms Tlmc1262.A_shift3
#print axioms Tlmc1262.A3add
#print axioms Tlmc1262.A_shiftQ
#print axioms Tlmc1262.A0_triple
#print axioms Tlmc1262.A1_triple
#print axioms Tlmc1262.A2_triple
#print axioms Tlmc1262.distinct3_refl
#print axioms Tlmc1262.distinct3_aab
#print axioms Tlmc1262.distinct3_abb
#print axioms Tlmc1262.one_add_ne
#print axioms Tlmc1262.one_add_left_ne
#print axioms Tlmc1262.omega_triple
#print axioms Tlmc1262.omega_triple_succ
#print axioms Tlmc1262.omega_triple_succ2
#print axioms Tlmc1262.omega_values
#print axioms Tlmc1262.omega_one
#print axioms Tlmc1262.omega_two
#print axioms Tlmc1262.omega_three
#print axioms Tlmc1262.not_eventually_two

open Lean in
#eval show MetaM Unit from do
  let names := [``Tlmc1262.ph_succ, ``Tlmc1262.ph_shift3, ``Tlmc1262.ch_shift,
                ``Tlmc1262.A_succ, ``Tlmc1262.A_step0, ``Tlmc1262.A_step1,
                ``Tlmc1262.A_step2, ``Tlmc1262.sum3, ``Tlmc1262.A_shift3,
                ``Tlmc1262.A3add, ``Tlmc1262.A_shiftQ, ``Tlmc1262.A0_triple,
                ``Tlmc1262.A1_triple, ``Tlmc1262.A2_triple,
                ``Tlmc1262.distinct3_refl, ``Tlmc1262.distinct3_aab,
                ``Tlmc1262.distinct3_abb, ``Tlmc1262.one_add_ne,
                ``Tlmc1262.one_add_left_ne, ``Tlmc1262.omega_triple,
                ``Tlmc1262.omega_triple_succ, ``Tlmc1262.omega_triple_succ2,
                ``Tlmc1262.omega_values, ``Tlmc1262.omega_one,
                ``Tlmc1262.omega_two, ``Tlmc1262.omega_three,
                ``Tlmc1262.not_eventually_two]
  for n in names do
    let axs ← Lean.collectAxioms n
    unless axs.isEmpty do
      throwError "{n} depends on axioms: {axs}"
  logInfo "AXIOM CHECK PASSED: every theorem is axiom-free"
