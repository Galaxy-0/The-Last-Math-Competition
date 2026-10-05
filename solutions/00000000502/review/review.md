# Solution Review — Conjecture 00000000502 (PR 617)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261004235618`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-05

## Verification

The official bilingual statement, full report, all PDF pages, and all Lean/source files were reviewed. Only the declared submission folder was added. Base metadata marks 00000000502 unsolved and no prior solution existed; the included conjecture is byte-identical to the official source. The PDF was independently rebuilt twice with `xelatex`; both passes exited 0, both versions have three pages, and extracted text agrees after whitespace normalization. The Lean 4.33.1/Mathlib `0df444a…` project was independently linked and built; `lake build`, direct warning-as-error checks, and submitted/extended axiom audits exited 0. All principal theorems use only `propext`, `Classical.choice`, and `Quot.sound`. No executable forbidden shortcut or kernel bypass is present. Three checksum-manifest entries are stale, but the actual conjecture/source/report independently pass.

## Disproof

For `K2`, the edge ideal is principal: `I(K2)^t=((x0x1)^t)`. Its nonzero generator is homogeneous of degree `2t`, so `0→S(−2t)→I^t→0` is a minimal free resolution and `reg I(K2)^t=2t` for every `t`, including `t=0`. Hence the literal eventual slope is `a(K2)=2`.

The graph is bipartite and chordal bipartite, with matching and induced-matching numbers both 1. The general formula predicts `max{0,⌈2/3⌉}=1`, while the chordal-bipartite specialization predicts 0. Both contradict the proved slope 2. The witness has a nonzero edge ideal, so the counterexample is non-vacuous and applies over every field.

**Disposition: APPROVED.**
