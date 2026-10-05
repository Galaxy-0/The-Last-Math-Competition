# Disproof of conjecture 00000007662

For the exact functional equation in the bilingual statement, `C_n(2)` is a positive prime **if and only if `n = 2`**. Its value there is 2. The prime-index set is `{2}`, contradicting the conjecture's explicit infinitude assertion.

The proof constructs the actual unique formal power series over every commutative ring, specializes its polynomial coefficients at 2, and proves the classification for every index. Negative coefficients remain integers; primality never means primality of their absolute values. The formal counting theorem uses a real cutoff and counts natural indices.

## Contents

- `main.tex`, `main.pdf`: complete four-page report and matching PDF.
- `conjecture.md`: byte-identical copy of the official bilingual statement.
- `lean/`: pinned Lean 4.19.0 / Mathlib v4.19.0 project and inspection commands.
- `auxiliary/check.py`: exact bounded comparison of the recurrence with the original quotient equation.
- `VERIFICATION.md`, `verification/`: execution, identity, trust, PDF, and eligibility evidence.
- `SEMANTIC_REVIEW.md`: independent local review of the frozen package; not maintainer acceptance.

## Reproduce the formal proof

With Lean installed through elan, run from `lean/`:

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true Conjecture7662.lean
lake env lean -DwarningAsError=true Check.lean
```

The default build target imports the entire implementation and treats warnings as errors. The committed manifest pins all nine dependency revisions. `Check.lean` prints all eight authored definitions, all 34 theorem types, and their transitive axiom dependencies.

If the platform's native cache executable is unavailable, the pinned Mathlib cache can be run through Lean in `.lake/packages/mathlib/` with `lake env lean --run Cache/Main.lean get`. This only supplies compiled dependencies; the submitted proof is built locally.

To reproduce the complete compiled-module inventory, run from `lean/` after building:

```sh
lake env lean -DwarningAsError=true ../verification/environment-inventory.lean
```

This diagnostic harness only prints existing declarations and collects their axioms. It is not imported by the proof and proves no submitted theorem. The recorded environment includes compiler-generated names, not just names beginning with the submission namespace.

## Reproduce the bounded coefficient checks

From the submission root, with standard-library Python 3:

```sh
python3 auxiliary/check.py --degree 32 --output /tmp/tlmc7662-results.json
```

The checker rejects optimized Python execution so its assertions cannot silently disappear. It compares every coefficient of degrees 0 through 32 for `q = -2, -1, 0, 1, 2, 3, 4`: 231 exact comparisons. Its second method builds the actual truncated quotient using unit-series inversion and substitution `t -> q*t`, then verifies the original identity and its cross-multiplied form. The `q=2` values begin `1, -1, 2, -11, 150, -4474`.

No probable-prime test is used. Within the tested range, negative odd coefficients, even positive coefficients at least 4, and the explicit values at 0 and 2 certify the classification. The finite computation does not establish the all-index result; that result is proved in Lean.

## Report and evidence

Compile `main.tex` with a standard LaTeX installation or the standalone document editor. The submitted PDF was exported with Tectonic 0.17.0 from the same final source, then all four pages were rendered and visually inspected. The text uses standard Latin fonts and requires no CJK setup; the full bilingual source remains in `conjecture.md`.

`verification/SHA256SUMS.json` covers every other package file. It excludes itself to avoid a self-reference. Local absolute paths in execution records describe the original runs; the relative reproduction commands above are portable.

The disproof negates the necessary infinitude conjunct. The exact count is 0 before index 2 and 1 thereafter, so the advertised growing lower bound also fails under either conventional positive-Omega interpretation. Formalization of logarithmic asymptotic notation is unnecessary to the logical disproof. The upper-bound assertion need not be false.
