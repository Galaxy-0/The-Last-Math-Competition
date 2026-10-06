# Disproof of conjecture 00000008304

The conjecture assigns the same breakpoint set `brk_pts` both a finite exact cardinality, `2^n - n - 1`, and infinitely many breakpoints for `n >= 24`. At `n = 24`, these assertions are incompatible: a set in bijection with a finite type `Fin k` is finite and cannot also be infinite.

The Lean project models the breakpoint set as an arbitrary family of types indexed by `n`. It formalizes the stated exact finite count and the infinite-threshold clause, then proves the source's full conjunction false. The other clauses about EHZ ratios and E8 duality are left arbitrary because they cannot repair the contradiction between the two clauses above.

Scope: the disproof reads `n` and `brk_pts` consistently across the two clauses, as the source text does. It does not formalize symplectic packing or any unneeded geometric claim.

To reproduce the verification:

```text
cd lean
lake build
lake env lean Check.lean
```

See `BUILD_AUDIT.md` for build and axiom-audit results.
