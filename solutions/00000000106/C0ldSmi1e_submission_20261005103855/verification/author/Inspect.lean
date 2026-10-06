import Conjecture106

open Lean in
run_cmd do
  let env ← getEnv
  let names := env.constants.toList.filterMap fun (n, _) =>
    if (`Conjecture106).isPrefixOf n then some n else none
  logInfo m!"Conjecture106 namespace declaration count: {names.length}"
  logInfo m!"Conjecture106 namespace declarations: {names}"
  for n in names do
    let some ci := env.find? n | throwError "Missing declaration {n}"
    logInfo m!"DECLARATION {n} : {ci.type}"
    logInfo m!"AXIOMS {n} : {← collectAxioms n}"
    match ci with
    | .defnInfo info =>
      logInfo m!"DEFINITION SAFETY {n} : {repr info.safety}"
      logInfo m!"DEFINITION VALUE {n} : {info.value}"
    | _ => pure ()

#check @Conjecture106.largestPrimeFactor
#check @Conjecture106.largestPrimeFactor_spec
#check @Conjecture106.threshold_iff_prime_divisor
#check @Conjecture106.Good
#check @Conjecture106.Statement
#check @Conjecture106.dyadic_primes
#check @Conjecture106.bounded_representative
#check @Conjecture106.unbounded_good
#check @Conjecture106.conjecture

set_option pp.all true in
#print Conjecture106.largestPrimeFactor
set_option pp.all true in
#print Conjecture106.Good
set_option pp.all true in
#print Conjecture106.Statement

#print axioms Conjecture106.largestPrimeFactor
#print axioms Conjecture106.largestPrimeFactor_spec
#print axioms Conjecture106.threshold_iff_prime_divisor
#print axioms Conjecture106.Good
#print axioms Conjecture106.Statement
#print axioms Conjecture106.dyadic_primes
#print axioms Conjecture106.bounded_representative
#print axioms Conjecture106.unbounded_good
#print axioms Conjecture106.conjecture

set_option pp.all true in
#synth Pow ℝ ℝ
set_option pp.all true in
#synth Pow ℕ ℕ
set_option pp.all true in
#synth LT ℝ
set_option pp.all true in
#synth LE ℕ
set_option pp.all true in
#synth Dvd ℕ
set_option pp.all true in
#synth NatCast ℝ

#print Real.rpow
#print Real.instPow
#print Nat.instDvd
#print Nat.instOrderBot
#print Set.Infinite
#print Nat.Prime
#check @Nat.prime_def
#check @Nat.mem_primeFactors
#check @Nat.primeFactors_eq_empty
#check @Finset.le_sup
#check @Finset.sup_mem_of_nonempty
#check @Set.infinite_iff_exists_gt
#check @Real.rpow_inv_lt_iff_of_pos
#check @Real.rpow_natCast
#check @Nat.exists_prime_lt_and_le_two_mul
#check @Nat.chineseRemainderOfFinset
#check @Nat.chineseRemainderOfFinset_lt_prod
