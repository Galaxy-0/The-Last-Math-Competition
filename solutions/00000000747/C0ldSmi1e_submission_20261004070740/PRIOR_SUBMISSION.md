# Earlier submission: errors and correction

This note supplies the previous-submission account required by contribution rule 2. It distinguishes the maintainer's recorded removal reason from an additional error identified by reading the old report.

## History and authoritative disposition

[PR35](https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/pull/35) submitted `earthking11_submission_20260913120000` and was merged on 2026-10-01. [Re-audit commit 541cf4fbc7aef3e17085577f6403c11c09f31fe1](https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/commit/541cf4fbc7aef3e17085577f6403c11c09f31fe1) removed it and returned the conjecture to unsolved status. The stated removal reason is:

> #747 (mod-5^8 residue arithmetic; no Z_p/Hensel in Lean)

The immutable sources below use the original submission commit `5daa67497ec88d9d37f1c63e407e4f6b6d3a7267`. The Lean file, report, and README were compared byte for byte with the last snapshot before removal (`efab34b80a63963991d6c7ed625442a89a328a44`) and are identical.

## 1. The concluding Lean theorem did not concern p-adic integers

The old [lean4/Main.lean](https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/blob/5daa67497ec88d9d37f1c63e407e4f6b6d3a7267/solutions/00000000747/earthking11_submission_20260913120000/lean4/Main.lean) imports `Std`. It proves Fermat-style facts for `Fin 5`, a congruence involving `110443` modulo `5^8`, and one lifting step from modulus 5 to modulus 25. The theorem named `conjecture_00000000747_false` packages finite `Nat` and `Fin` statements. No theorem constructs a point of `Z_5` or transfers the finite checks to a p-adic fixed point.

The author explicitly disclosed the finite scope in the code and [README](https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/blob/5daa67497ec88d9d37f1c63e407e4f6b6d3a7267/solutions/00000000747/earthking11_submission_20260913120000/README.md). The one-step Hensel argument in prose was mathematically sound, but the essential actual-domain conclusion was absent from Lean. Finite numerical checks and a single lifting step do not supply that missing formal proof.

**Present correction:** the witness is `(-1 : PadicInt p)`, a point of the actual Mathlib p-adic integer ring. Characteristic zero distinguishes it from 0 and 1. Oddness of every prime `p ≥ 5` proves its fixed-point equality in that ring. Actual function iteration proves every iterate fixes it. The final theorem negates the universally quantified original restriction using `p=5`.

## 2. The higher-iterate root count in the old report was wrong

The old [main.tex, lines 239–246](https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/blob/5daa67497ec88d9d37f1c63e407e4f6b6d3a7267/solutions/00000000747/earthking11_submission_20260913120000/main.tex#L239) and the README claim that `X^(p^n) - X` has `p^n` roots in `Z_p`, because all roots of unity of order dividing `p^n-1` allegedly lie there. This is false for `n > 1`.

For `n ≥ 1`, every residue modulo `p` is a root of `F_n(X)=X^(p^n)-X`, and `F_n'(a) ≡ -1 (mod p)`. Simple-root Hensel therefore gives exactly one p-adic root in each of the `p` residue classes, hence exactly `p` roots. See [Keith Conrad, Hensel's Lemma, Theorem 2.1](https://kconrad.math.uconn.edu/blurbs/gradnumthy/hensel.pdf). The `p^n` count belongs to an algebraic closure, not to `Z_p`. The earlier first-iterate count of `p` roots was correct.

This second issue is our independent source finding; the removal commit explicitly cites the formalization gap, not this extra prose error. The present proof does not depend on any total root count. Its report gives the correction as historical context and clearly separates it from the submitted formal theorem.

## What is and is not reused

The present contribution is a new proof project in the required personal folder. No earlier finite-residue certificate or numerical computation is used. It supplies complete Lean proofs on actual p-adic integers, a matching report and PDF, independent semantic review, and local validation records. This is a corrective submission awaiting official review.
