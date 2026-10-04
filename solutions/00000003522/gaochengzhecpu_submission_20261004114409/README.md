# Proof of conjecture 00000003522

Hessenberg natural addition is cancellative in both arguments for arbitrary
ordinals. In contrast, ordinary ordinal addition has the explicit failure
of right cancellation `0 + omega = 1 + omega` although `0 != 1`.

This is a standard theorem, not a claimed new discovery. The submission
proves the entire assertion in the source, including its comparison with
ordinary addition. It does not incorrectly claim ordinary left cancellation
fails: that direction remains valid and is also formalized.

## Reproduce

With Lean 4.19.0 and the supplied public-Git, commit-pinned manifest:

```text
cd lean
lake exe cache get
lake build
lake env lean -DwarningAsError=true Main.lean
```

The cache command is optional when dependencies are already built.
Compile `main.tex` with Tectonic or a compatible LaTeX installation.
There is no auxiliary finite-sample Python check: the Lean theorem
quantifies over arbitrary ordinals directly.

## Contents

- `SOURCE.md`: byte-exact upstream English and Chinese source.
- `main.tex` and `main.pdf`: mathematical proof and precise scope.
- `lean/Main.lean`: full formal assertion, using real Mathlib ordinals.
- `lean/lakefile.toml`, `lean/lake-manifest.json`, `lean/lean-toolchain`:
  reproducible dependency pins.
- `verification/BUILD.json` and logs: actual validation results.
- `verification/SELF_REVIEW.md`: same-author adversarial review.
- `verification/SOURCE_PROVENANCE.md`: source provenance, kept outside SOURCE.

## Formalization boundary

The theorem `Conjecture3522.conjecture_true` has no problem-specific
hypotheses. It gives left and right cancellation of `Ordinal.nadd` and
an ordinary-addition counterexample. Every ordinal variable has type
`Ordinal.{u}`, with arbitrary universe `u`; the proof is not limited to
countable ordinals or a finite Cantor-normal-form encoding.

The standard library already defines the Hessenberg sum recursively.
The file proves strict monotonicity from its lower-set characterization
`Ordinal.lt_nadd_iff` and deduces cancellation via injectivity. It does
not postulate cancellation or replace the operation with an abstract
cancellative structure. Standard library ordinal arithmetic proves
`1 + omega = omega`. The foundational ordinal library is reused, not
claimed as newly implemented here.

No custom axiom, `sorry`, `admit`, or `native_decide` is used. Printed
theorem dependencies are checked against the three standard Lean axioms.
