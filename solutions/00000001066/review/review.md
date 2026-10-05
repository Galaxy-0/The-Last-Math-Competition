# Solution Review — Conjecture 00000001066 (PR 597)

**Submitter:** C0ldSmi1e  
**Submission:** `solutions/00000001066/C0ldSmi1e_submission_20261005021731/`  
**Head:** `d73a9ae0b8e9f66df0036f10b517c23639114a2d`  
**Result:** Approved

## Claim

The official conjecture states that for a Sidon set \(B\subset\mathbb F_p\), \(|B|\le p^{1/2}+1\), and that \(p^{1/2}\) is attained for prime \(p\). The submission disproves the exact-attainment clause, and therefore the full written conjunction, under both its natural universal-prime reading and the weaker reading in which attainment is required at only one prime.

## Mathematical audit

For a prime \(p\), suppose a finite subset \(B\subseteq\mathbb F_p\) has \(|B|=\sqrt p\) in \(\mathbb R\). Setting \(n=|B|\in\mathbb N\) and squaring gives \(n^2=p\). This is impossible for prime \(p\): \(n=0\) or \(1\) would make \(p\) nonprime, while \(n\ge2\) gives a proper factorization of \(p\). Hence no finite subset—Sidon or otherwise—has cardinality exactly \(\sqrt p\).

This stronger obstruction makes the result non-vacuous and independent of the unresolved upper-bound clause. Prime \(2\) is explicitly available, and every prime field has finite subsets, including empty and singleton Sidon sets.

## Formal statement correspondence

The Lean definitions use actual `Finset (ZMod p)` objects, cast cardinalities and \(p\) into \(\mathbb R\), and define exact attainment by `(B.card : ℝ) = Real.sqrt (p : ℝ)`. The Sidon condition uses injectivity of ordered nondiagonal differences. The project separately formalizes:

- the full universal-prime conjunction, negated by `Conjecture1066.universal_conjecture_false`; and
- the all-primes-bound plus one-prime-attainment reading, negated by `Conjecture1066.existential_prime_conjecture_false`.

The formalization and LaTeX report use the same literal exact square-root interpretation and explicitly disclose that they do not address rounded or asymptotic variants or the upper-bound clause alone.

## Verification

The complete LaTeX and Lean sources were independently reviewed. A fresh pdfLaTeX rebuild succeeded and produced the expected two pages. In a fresh copied Lean project, `lake build` succeeded. Direct warning-as-error replays succeeded for `Conjecture1066.lean`, `Check.lean`, and the environment inventory.

`Check.lean` printed all five definitions, all seven theorem types, and all seven axiom lists. Every theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`. The complete environment inventory found exactly the five definitions and seven submitted theorems, with no extra axiom, unsafe, or partial declarations.

Both Python auxiliary scripts were syntax-checked and replayed. The independent verifier passed its fresh build, strict replays, source-declaration coverage, dependency-pin, and complete environment checks. The PDF export logic also replayed successfully. There is no required external numerical search; the proof is exact, with ordinary kernel-checked `decide` used only for `2 ≤ 2`.

Scans found no `sorry`, admission, custom axiom, `native_decide`, unsafe declaration, `implemented_by`, `extern`, kernel-check bypass, or incomplete proof. The base metadata marks conjecture 00000001066 unsolved and no duplicate solution directory existed.

## Conclusion

The submission gives a complete, faithful, independently replayed disproof of the stated conjecture. Approved.
