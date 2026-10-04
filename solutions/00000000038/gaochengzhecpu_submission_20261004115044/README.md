# Conjecture 00000000038: counterexample

**Result:** for every `N >= 4`, the set `A_N = {3,...,N}` has density at least `1/2` in `[N]`, but every choice of at least two entries from it, including repetitions, has product strictly larger than sum. Counterexamples therefore occur at arbitrarily large `N` and simultaneously exclude every nontrivial length.

The source expressly requires nontriviality. Singleton selections always satisfy `x = x`; Lean separately proves that singleton identities are the only possible identities in these sets. The argument applies to any nontriviality convention that excludes singleton identities. Admitting `k = 1` would make the original statement vacuous by choosing that length.

## Contents

- `main.tex`, `main.pdf`: complete elementary proof and formalization scope.
- `SOURCE.md`: byte-for-byte copy of the original bilingual source.
- `lean/Main.lean`: actual proof for arbitrary finite lists and arbitrary interval sizes.
- `lean/lean-toolchain`, `lean/lakefile.toml`, `lean/lake-manifest.json`: Lean 4.19.0 and public Git dependencies pinned to exact commits.
- `verification/BUILD.json`: real clean-build, axiom, source-hash, PDF compilation, rendering, and visual-review evidence.
- `verification/SELF_REVIEW.md`: adversarial review against the original statement.
- `verification/SOURCE_PROVENANCE.md`: source identity and reading notes.
- `verification/lake-build.log`, `verification/lean-axioms.log`, `verification/pdf-build.log`: actual compiler outputs.

No numerical verifier is used or needed: the Lean proof covers every permitted length and every `N >= 4`.

## Reproduce

With the official Lean toolchain specified in `lean/lean-toolchain`, and Git/network access for the pinned Mathlib dependency:

```text
cd lean
lake update
lake exe cache get Mathlib/Algebra/BigOperators/Group/List/Basic.lean Mathlib/Order/Interval/Finset/Nat.lean Mathlib/Data/Real/Basic.lean Mathlib/Tactic/NormNum.lean Mathlib/Tactic/Linarith.lean
lake build
lake env lean -DwarningAsError=true Main.lean
```

`lakefile.toml` pins the full Mathlib Git commit. Keep the supplied `lake-manifest.json` under version control; local `.lake` artifacts are not part of the source package. The recorded clean verification copies the Lean source to a fresh directory and reuses only the official, commit-pinned dependency cache.

From the package directory, compile the paper with:

```text
tectonic --keep-logs main.tex
```

The desktop native compiler is unavailable on this host; the delivered PDF is an actual export from the existing Tectonic compiler, followed by Poppler rendering and review of every page.

## Exact formal coverage

The formal proof uses ordinary natural-number list sums/products, `Finset.Icc 3 N`, the exact cardinality `N-2`, and real-valued density `A.card / N`. Lists retain repetitions. It proves:

1. For every list of length at least two with entries at least three, sum is strictly less than product.
2. Every sum-product identity with such entries is a singleton identity.
3. The family lies in `[N]` and has density at least one half for every `N >= 4`.
4. For every bound `B`, a counterexample exists with `N >= B`.
5. No fixed nontrivial length works even if the conclusion is only required for all sufficiently large `N`.

Only `propext`, `Classical.choice`, and `Quot.sound` appear in the axiom audit. The source's word “nontrivial” is addressed explicitly in the paper; there is no hidden change to the arithmetic or density definitions.

This package does not publish or modify upstream material.
