# TLMC 00000001209 — disproof for 2-Wythoff

Under Fraenkel's standard definition of t-Wythoff and coordinatewise ratio asymptotics, the conjecture is false. The sorted P-positions for t=2 are exactly

`(a_n,b_n) = (floor(n*sqrt(2)), floor(n*sqrt(2))+2*n)`.

Their first-coordinate ratio to the conjectured `phi*n` tends to `sqrt(2)/phi`, approximately 0.874032049, rather than one.

The Lean proof defines the legal game moves and the losing-position predicate by recursion on total heap size, supplies a terminating finite decision procedure, proves the exact P-position characterization using the proved Mathlib Beatty partition theorem, identifies the n-th smaller heap directly from the game via `Nat.nth`, and establishes the asymptotic refutation. It also refutes the necessary first-coordinate part of the universal assertion over all t >= 1.

The phrase “linear correction coefficient” has an alternative interpretation: an order-n correction that changes the leading slope. That expansion is true at t=2 with coefficient `sqrt(2)-phi`; it is also formalized. This submission refutes the stated asymptotic equivalence and does not claim to refute that alternative corrected expansion. The report discusses t=1 and the known general-t formula; the strict t=2 game and its equivalent non-strict t=1 game are fully formalized.

The conclusion also survives the alternative move convention `|k-l| ≤ t`. For integer removal amounts this is exactly the strict convention with parameter `t+1`; its `t=1` game already differs from classical Wythoff and has P-positions `(floor(n*sqrt(2)), floor(n*sqrt(2))+2*n)`, hence slopes `sqrt(2)` and `sqrt(2)+2`. For example, its first positive P-position is `(1,3)`, whereas classical Wythoff has `(1,2)`. `verify.py` directly computes both games on `[0,100]^2`: non-strict t=1 agreed with strict t=2, with observed smaller-heap slope `41/29 ≈ 1.413793103` at index 29. Lean proves the move and P-position equivalences, the slope, and `universal_le_refutation`. The universal ratio-asymptotic claim fails under this convention too.

## Contents

- `lean4/Wythoff.lean`: complete formalization; main theorems `Wythoff.t_two_refutation` and `Wythoff.universal_refutation`.
- `lean4/lean-toolchain`, `lakefile.toml`, `lake-manifest.json`: pinned self-contained project configuration.
- `report.tex`, `report.pdf`: self-contained mathematical proof, interpretation discussion, and semantic correspondence.
- `verification.txt`: recorded successful Lean compiler output, axiom audits, and independent Python output.
- `verify.py`: supplementary finite checks using only Python's standard library.

## Reproduction

From `lean4/`, run:

```sh
lake exe cache get && lake build
```

Versions: Lean `leanprover/lean4:v4.33.0`, Mathlib `v4.33.0`, revision `db584cd6d46c92f209a44c0f1c829460d327499d`. Successful compilation against this pinned Mathlib environment and the axiom audits are recorded in `verification.txt`.

From this directory, run:

```sh
python3 verify.py
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

All audited mathematical theorems use only `propext`, `Classical.choice`, and `Quot.sound`. There are no proof holes, added axioms, or native decision shortcuts. Python checks are supplementary and are not dependencies of the Lean proof. No trureturing code is vendored.

Submitted by AlyciaBHZ on behalf of the Omega Institute (trureturing project, https://github.com/the-omega-institute/trureturing).
