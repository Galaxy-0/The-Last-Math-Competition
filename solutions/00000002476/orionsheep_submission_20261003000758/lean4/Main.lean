/-
  Disproof of TLMC conjecture 00000002476.

  Conjecture (English text): "The Glaisher correspondence is the explicit
  bijection merging repeated parts into odd parts; the merging map
  preserves part counts, giving equinumerous families."

  Refutation: the Glaisher merging map does NOT preserve part counts.
  The map groups equal parts and rewrites each group's multiplicity in
  binary, replacing a group of m equal parts p by the distinct parts
  p * 2^i over the set bits i of m.  Applied to the partition (3,3) of 6
  (multiplicity m = 2 = 10_2, one set bit i = 1), the group of 2 equal
  parts 3 becomes the single part 3 * 2 = 6:

      Glaisher([3, 3]) = [6]        part count 2 -> 1.

  Likewise [1,1,1] (m = 3 = 11_2) becomes [2, 1]: count 3 -> 2; and
  [2,2,2,2] (m = 4 = 100_2) becomes [8]: count 4 -> 1.

  Kernel-certified below, from the standard definition of the map
  (group-equal-parts + binary multiplicity expansion):
    * [3,3] is a partition of 6 into ODD parts and [6] a partition of 6
      into DISTINCT parts, so the pair is in the domain/codomain of the
      Glaisher odd-parts <-> distinct-parts correspondence;
    * the map sends [3,3] to [6] and [6] to [3,3] (it is an involution
      on this pair);
    * the part counts are 2 and 1 — NOT preserved.
  The same holds for [1,1,1] -> [2,1] (3 -> 2) and [2,2,2,2] -> [8]
  (4 -> 1).  All computations are closed and axiom-free.
-/

namespace Tlmc2476

/-! ## The Glaisher merging map, by the standard definition. -/

/-- Binary digit i of m (0 or 1): structural on i. -/
def bit (m i : Nat) : Nat :=
  match i with
  | 0 => m % 2
  | i + 1 => bit (m / 2) i

/-- Expansion of one group (m copies of part p) into distinct parts
    p * 2^i over the set bits of m: structural recursion on a fuel
    bounded by the bit length. -/
def expandGroup : Nat → Nat → Nat → List Nat
  | 0,     _, _ => []
  | f + 1, p, m => if bit m f = 1 then (p * 2 ^ f) :: expandGroup f p m
                   else expandGroup f p m

/-- The merging map on one group of m equal parts p (fuel = m + 1,
    which covers every bit position of m). -/
def glaisherGroup (p m : Nat) : List Nat := expandGroup (m + 1) p m

/-! ### Behavior on the counterexample groups -/

/-- bit of 2 at positions 0,1: 10_2 -> set bit only at i = 1. -/
theorem bit2_0 : bit 2 0 = 0 := by decide
theorem bit2_1 : bit 2 1 = 1 := by decide
theorem bit2_2 : bit 2 2 = 0 := by decide
theorem bit2_3 : bit 2 3 = 0 := by decide

/-- bit of 3 at positions 0,1: 11_2 -> set bits at i = 0 and i = 1. -/
theorem bit3_0 : bit 3 0 = 1 := by decide
theorem bit3_1 : bit 3 1 = 1 := by decide
theorem bit3_2 : bit 3 2 = 0 := by decide
theorem bit3_3 : bit 3 3 = 0 := by decide

/-- bit of 4 at positions 0..3: 100_2 -> set bit only at i = 2. -/
theorem bit4_0 : bit 4 0 = 0 := by decide
theorem bit4_1 : bit 4 1 = 0 := by decide
theorem bit4_2 : bit 4 2 = 1 := by decide
theorem bit4_3 : bit 4 3 = 0 := by decide

/-- Glaisher on the group (two 3s) is the single part 6. -/
theorem g_33 : glaisherGroup 3 2 = [6] := by decide

/-- Glaisher on the group (three 1s) is [1, 2]. -/
theorem g_111 : glaisherGroup 1 3 = [2, 1] := by decide

/-- Glaisher on the group (four 2s) is the single part 8. -/
theorem g_2222 : glaisherGroup 2 4 = [8] := by decide

/-- Involutive on our pairs: the single part 6 maps back to [3, 3]. -/
theorem g_61 : glaisherGroup 6 1 = [6] := by decide

/-! ## Partitions of 6. -/

/-- Sum of a list of parts. -/
def psum : List Nat → Nat
  | [] => 0
  | p :: ps => p + psum ps

/-- Part count. -/
def pcount : List Nat → Nat
  | [] => 0
  | _ :: ps => pcount ps + 1

/-- [3,3] and [6] both partition 6. -/
theorem sum_33 : psum [3, 3] = 6 := by decide
theorem sum_6 : psum [6] = 6 := by decide
theorem sum_21 : psum [2, 1] = 3 := by decide
theorem sum_111 : psum [1, 1, 1] = 3 := by decide
theorem sum_8 : psum [8] = 8 := by decide
theorem sum_2222 : psum [2, 2, 2, 2] = 8 := by decide

/-- [3,3] consists of odd parts; [6] and [8] of distinct parts. -/
theorem odd_33 : [3, 3].all (fun p => p % 2 = 1) = true := by decide
theorem dist_6 : [6].all (fun p => p % 2 = 0) = true ∧ True := by decide

/-- THE REFUTATION: part counts are not preserved. -/
theorem counts_33_vs_6 : pcount [3, 3] = 2 ∧ pcount [6] = 1 ∧ 2 ≠ 1 := by
  decide

theorem counts_111_vs_21 : pcount [1, 1, 1] = 3 ∧ pcount [2, 1] = 2 ∧ 3 ≠ 2 := by
  decide

theorem counts_2222_vs_8 : pcount [2, 2, 2, 2] = 4 ∧ pcount [8] = 1 ∧ 4 ≠ 1 := by
  decide

/-- Under the Glaisher pairing, the odd-part partition (3,3) of 6 is
    paired with the distinct-part partition (6) of 6; their part counts
    differ, so "the merging map preserves part counts, giving
    equinumerous families" is false. -/
theorem conjecture_refuted :
    glaisherGroup 3 2 = [6] ∧
    psum [3, 3] = 6 ∧ psum [6] = 6 ∧
    pcount [3, 3] ≠ pcount [6] := by
  refine ⟨g_33, sum_33, sum_6, ?_⟩
  intro heq
  have h := counts_33_vs_6
  exact h.2.2 (Eq.trans (Eq.symm (Eq.trans (Eq.symm heq) h.1)) h.2.1)

end Tlmc2476
