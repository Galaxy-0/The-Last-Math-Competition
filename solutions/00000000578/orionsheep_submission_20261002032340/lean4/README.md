# Lean 4 verification for conjecture 00000000578 (disproof)

Core Lean 4 only (no Mathlib). Toolchain: `leanprover/lean4:v4.33.1`.

`Main.lean` implements, from scratch:

- `GF(2)` rank of bitmask vectors via echelon insertion (`insertBasis`, `rank`);
  bitwise xor is a fuel-structural `myXor` because core `Nat.xor` compiles
  with `propext`;
- characteristic-polynomial evaluation by full subset enumeration
  (`pick`, `chiTermV`, `chiFromV`, `chiTotalV`, `vval`, `chiNeg`), so the
  attack numbers `chi_{bin(5,3)}(-1) = -332` and `chi_{bin(6,2)}(-2) = -2520`
  are *computed by the kernel from the matroid data*, not assumed. Signed sums
  are carried as `Nat × Nat` pairs (`vadd`) so that summation reasoning uses
  only clean `Nat` lemmas; the 2^15 = 32768 subsets of bin(6,2) are summed in
  1024-subset chunks (`chunkSumV`, splitting lemma `chiFromV_add`) to keep the
  kernel evaluation depth small;
- boundary values `chi_{5,3}(-2) = -1263`, `chi_{5,3}(-3) = -3624`,
  `chi_{6,2}(-1) = -720`, `chi_{6,2}(-3) = -6720`;
- the divisibility failures `12 ∤ 332` and `48 ∤ 2520` (hence `12 ∤ -332`,
  `48 ∤ -2520` in `Int`), proving conjecture 00000000578 false.

## Build and check

```sh
lake build
lake env lean Check.lean
```

Every `#print axioms` line in `Check.lean` must report
`does not depend on any axioms` (zero axioms, zero `sorry`).
