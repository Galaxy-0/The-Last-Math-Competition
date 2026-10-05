# Solution Review — Conjecture 00000007752 (PR 618)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005000037`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-05

## Verification

The official bilingual statement, full report, all PDF pages, and all Lean/source files were reviewed. Only the declared submission folder was added. Base metadata marks 00000007752 unsolved and no prior solution existed; the included conjecture is byte-identical to the official source. The PDF was independently rebuilt twice with `xelatex`; both passes exited 0, both versions have four pages, and extracted text agrees after whitespace normalization. The Lean 4.33.1/Mathlib `0df444a…` project was independently linked and built; `lake build`, direct warning-as-error checks, and submitted/extended axiom audits exited 0. All principal theorems use only `propext`, `Classical.choice`, and `Quot.sound`. No executable forbidden shortcut or kernel bypass is present. Independent numerical checks corroborate the explicit branch, functional equation, normalization, and bounded critical orbit. Two checksum-manifest entries are stale, but the actual conjecture/source independently pass.

## Disproof

For `c=-2`, the critical orbit is `0→−2→2→2`, so the parameter satisfies the stated non-escaping condition. The Böttcher coordinate is explicitly

`φ(z)=z/2·(1+(1−4/z²)^{1/2})`,

using the branch asymptotic to `z` at infinity. It satisfies `φ(z²−2)=φ(z)²`, is analytic and injective for large `|z|`, and has `φ(z)/z→1`; a rigidity argument proves it is the unique normalized coordinate. Every algebraic `z` gives algebraic `φ(z)` and algebraic `φ(z)/z`. Since there are arbitrarily large algebraic integers, the claimed eventual transcendence fails. The submission also classifies unnormalized meromorphic solutions as zero or integer powers of this algebraic coordinate, so that reading cannot evade the counterexample. The separate ratio for parameters 0 and −2 is algebraic, refuting the stated independence clause under its natural interpretation.

**Disposition: APPROVED.**
