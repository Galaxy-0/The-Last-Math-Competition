# Counterexample to conjecture 00000004383

The conjecture makes two incompatible assertions about the same first nonzero homotopy group among the first five: it is a direct sum of copies of a prime field's additive group, and it is cyclic of order four.

The Lean proof isolates precisely the properties needed from those descriptions. `PrimeCharacteristicAdditive` records the additive operation and the characteristic-p law; `directSum` forms pointwise sums and a theorem proves that p annihilates every element of every such direct sum. `OrderFourGenerator` records that a generator is annihilated by n exactly when 4 divides n. The same group satisfying both properties would imply that 4 divides the prime p. The Lean development proves from its elementary factorization definition of primality that this is impossible. No primality fact is postulated, and no additional axioms, `sorry`, or `native_decide` are used.

The abstraction does not calculate the homotopy groups of the sphere spectrum. It formalizes the inconsistency between the two stated descriptions of the first nonzero group, conditional on the first five groups being of the stated prime-field direct-sum form. It does not verify the claimed degree, the remaining four groups, or any actual THH computation.

## Verification

From this directory, run:

```sh
cd lean && lake build
cd .. && TECTONIC_CACHE_DIR=.tectonic-cache tectonic --keep-logs -o . main.tex
```

The Lean project has no external dependencies and targets Lean 4.33.1. The included PDF is generated from `main.tex`.
