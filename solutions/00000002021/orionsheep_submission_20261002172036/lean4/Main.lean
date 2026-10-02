/-
  Disproof of TLMC conjecture 00000002021 (the mod-11 obstruction clause).

  Conjecture: G(5) = 17; ... and the lower bound for G(5) is guaranteed by
  the local density obstruction modulo eleven.

  Refutation of the obstruction clause: the fifth powers modulo 11 are
  exactly {0, 1, 10} (= {0, 1, -1}), certified below as a value table.
  Sums of FIVE such values already cover EVERY residue class mod 11
  (since {0,+-1}^5 sums realize -5..5, and -5..5 covers Z/11). A fortiori
  sums of 17 fifth powers cover every residue mod 11. Hence there is NO
  local congruence obstruction modulo 11: the claimed lower-bound
  mechanism does not exist.

  Lean certificates (all closed kernel computations, axiom-free):
    * pow5_table — the fifth-power residue table over 0..10;
    * covers_all — every residue 0..10 occurs among the 3^5 = 243
      five-term sums from {0,1,10}, reduced mod 11.

  Boundary: this refutes the "lower bound guaranteed by the mod-11 local
  density obstruction" clause; the numeric claim G(5) = 17 itself is a
  separate assertion not needed here.
-/

namespace Tlmc2021

/-- The fifth-power residue table mod 11 (a^5 mod 11 for a = 0..10):
    values are in {0, 1, 10} exactly. -/
theorem pow5_table :
    (List.range 11).map (fun a => a ^ 5 % 11) =
      [0, 1, 10, 1, 1, 1, 10, 10, 10, 1, 10] := by decide

/-- Fifth powers mod 11 (the value set of the table). -/
def fifthPowers : List Nat := [0, 1, 10]

/-- Structural lookup (avoiding core List.getD, whose reduction carries
    propext). -/
def idx : List Nat → Nat → Nat
  | [],      _     => 0
  | a :: _,  0     => a
  | _ :: as, n + 1 => idx as n

/-- All 3^5 = 243 five-term sums from {0,1,10}, reduced mod 11
    (the ternary digits of c select the five terms). -/
def sums5 : List Nat :=
  (List.range 243).map fun c =>
    (idx fifthPowers (c % 3) +
     idx fifthPowers (c / 3 % 3) +
     idx fifthPowers (c / 9 % 3) +
     idx fifthPowers (c / 27 % 3) +
     idx fifthPowers (c / 81 % 3)) % 11

/-- Every residue class mod 11 is a sum of five fifth powers. -/
theorem covers_all :
    (List.range 11).all (fun r => sums5.contains r) = true := by decide

end Tlmc2021
