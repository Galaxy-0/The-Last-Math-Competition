# Conjecture 00000000040: disproved

The uniform bound `|(A+A) intersect (A*A)| <= |A|^(1+o(1))` is false. For every positive integer `n`, the set

```text
A_n = {2^i : 0 <= i < 2n} union {1+2^i : 0 <= i < 2n}
```

has size between `2n` and `4n`, while the actual sumset/product-set intersection contains the `n^2` distinct values `2^i + 2^(n+j)`, for `0 <= i,j < n`. Every such value is also the product `2^i * (1+2^(n+j-i))` of two members of `A_n`.

This is a family of positive integer sets embedded in the reals. It disproves even a uniform `O(|A|^(3/2))` bound. The Lean proof treats arbitrary family parameters, not only computed examples.

## Files

- `main.tex` and `main.pdf`: complete proof and formalization correspondence.
- `SOURCE.md`: byte-exact original bilingual source.
- `lean/Main.lean`: actual finite real sets, cardinalities, positive integer membership, injective grid, and formal asymptotic negation.
- `lean/lean-toolchain`, `lean/lakefile.toml`, `lean/lake-manifest.json`: complete portable pinned Lake project.
- `verify.py`: optional exact integer cross-checks for six illustrative sample sizes.
- `verification/BUILD.json` and adjacent logs: fresh-build results, dependency identities, theorem axioms, auxiliary output, PDF compilation, and rendering.
- `verification/SELF_REVIEW.md`: authoring-agent adversarial checks.

## Reproduce

With Lean installed through elan, run from `lean/`:

```text
lake build
lake env lean -DwarningAsError=true Main.lean
```

Lean is pinned to version 4.19.0 and Mathlib to commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. All transitive dependency revisions are locked in the manifest, and all dependency URLs are public Git URLs. On a fresh machine, `lake exe cache get` can optionally fetch official Mathlib build artifacts instead of rebuilding dependencies.

From the submission directory, the auxiliary verification and PDF can be reproduced using:

```text
python verify.py
tectonic main.tex
```

The Python script uses only the standard library. It computes actual sumsets and product sets with exact integers. Its finite examples are supplementary checks; the infinite conclusion follows from the Lean theorem and the written proof.

## Formalization correspondence

`sumset` and `productset` take the images of `A x A` under real addition and multiplication. `overlap` is their finite intersection. `witness` is precisely the displayed family, and `witness_positive_integer` proves the positive integer property of every member.

The theorems `witness_card_lower`, `witness_card_upper`, `pairValue_injective_on`, `embeddedGrid_subset_overlap`, and `overlap_card_lower` prove all claims about the actual objects. `arbitrarily_large_super_three_halves` proves, for every natural `C,N`, the existence of `A` with `|A| >= N` and `C*|A|^3 < |overlap(A)|^2`.

`SupremumNearLinearBound` is the uniform interpretation: for every real epsilon greater than zero, there is a size threshold above which every finite real set satisfies the real-power bound `|overlap(A)| <= |A|^(1+epsilon)`. The theorem `conjecture40_false` directly negates this proposition. It uses epsilon `1/2` and the verified real-power identity `(x^(3/2))^2=x^3` for nonnegative `x`. The stronger squared inequality also rules out an implicit multiplicative constant, as the paper explains by bounding its square with a natural number.

No proof holes, admitted terms, custom axioms, opaque declarations, or native evaluation proof shortcuts are used. Printed theorem dependencies contain only `propext`, `Classical.choice`, and `Quot.sound`.

## Source and evidence

The bilingual source agrees on the universal finite-real-set claim and its supremum interpretation. Its SHA-256 is `b546cfd14249a2a218a69eaf899283644ccbf01534c661e00cbdbc3efe770014`.

The native LaTeX editor was requested and compilation was attempted. The native compiler returned `Unable to find standard directories for platform`; this platform limitation is recorded in `verification/native-compiler.json`. The delivered PDF is exported with the existing Tectonic installation and checked using Poppler-rendered page images.

The fresh build uses unmodified artifacts for dependencies at pinned official Git commits. This submission's own Lean artifacts are not reused. `verification/BUILD.json` records the exact submitted source hashes and commands. See its final status for completed checks and PDF page count.

The final evidence records a successful fresh `lake build`, direct Lean with warnings treated as errors, all six auxiliary checks, and warning-free Tectonic export. Both pages of the final PDF were rendered and visually inspected. `pdf_visual_review` is `PASS`.

Review status: authoring-agent self-review completed. Parent review and final upstream source/duplicate checks must be completed before publication. This agent performed no GitHub writes.
