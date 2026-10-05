# Disproof of conjecture 00000000331

Choose the strictly positive constant function psi(n) = 1/4. The required series
is one quarter of the harmonic series and tends to positive infinity. For every
fixed real numerator a, each alpha in [1/2,3/4] has only finitely many positive
denominators satisfying |alpha-a/n| < 1/4. The failure interval has Lebesgue
measure 1/4, so the asserted almost-everywhere conclusion fails.

This addresses the repository's literal fixed-numerator formula. It makes no
claim to resolve a differently formulated inhomogeneous Duffin-Schaeffer problem.
The source imposes no condition that psi tend to zero. The example is positive,
bounded, and nonincreasing, and the proof works for every real a, hence also for
integer or rational numerators. Both positive and nonnegative function classes
and real-line/closed/open/half-open unit-interval readings are addressed.

## Reproduce

Use the pinned Lean 4.19.0 toolchain and Mathlib v4.19.0 manifest in `lean/`.
From that directory, with the dependencies available:

```sh
lake build
lake env lean -DwarningAsError=true Conjecture331.lean
lake env lean -DwarningAsError=true Check.lean
```

The explicit default target is `Conjecture331`. The source defines the sum over
exactly n=1,...,N, divergence as a limit to positive infinity, and infinitude of
the actual set of successful positive denominators. Equivalence theorems bridge
these to exceeding every real bound and to arbitrarily large successful indices.
The numerator a stays fixed and the radius remains psi(n). Actual Lebesgue measure
and restricted Lebesgue measure are used. The final implication-negating theorems
are `literal_claim_false` and `nonnegative_literal_claim_false`.

`Check.lean` prints all eight definitions and the types and axiom dependencies
of all 20 authored theorems. Every theorem is proved in Lean; no external
mathematical computation is required. There are no admitted proofs,
`native_decide`, custom axioms, unsafe source declarations or partial definitions.

## Materials

`main.tex` and `main.pdf` contain the complete mathematical report. `conjecture.md`
is the byte-identical bilingual source. `verification.txt` summarizes the fresh
build, strict replays, exhaustive compiled-module inventory, dependency pins,
PDF checks and eligibility audit. Detailed records and inspection scripts are
in `verification/`; their absolute scratch paths document the local execution
and are not required by the mathematical project. `SEMANTIC_REVIEW.md` records
the independent internal review of frozen inputs. `verification/SHA256SUMS.json`
covers every other submitted file.

Local validation and internal review do not establish maintainer acceptance.
