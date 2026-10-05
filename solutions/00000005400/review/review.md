# Solution Review — Conjecture 00000005400 (PR 601)

**Submitter:** Jackmeson1  
**Submission:** `solutions/00000005400/Jackmeson1_submission_20261004213311/`  
**Head:** `8247ae6038835d0cd0a4fec64735fde20fad1c4a`  
**Result:** Approved

## Claim

The conjecture requires two maps with identical orbit-distribution limits and different periodic-point counts, and says that this separation is realized by an explicit conjugate pair with the same measure but different periods. The submission disproves the final clause: a pointwise bijective conjugacy preserves every periodic-point count, exact-period count, cycle count, period set, and pointwise least period, so such a conjugate pair cannot exist.

## Mathematical audit

Suppose \(h:X\to Y\) is a bijection and \(h\circ f=g\circ h\). Induction gives \(h(f^n x)=g^n(hx)\) for every \(n\). Since \(h\) is injective, \(f^n x=x\) iff \(g^n(hx)=hx\). Thus periodicity and least periods are preserved at every point.

Consequently \(h\) restricts to bijections between the \(n\)-periodic point sets and the points of least period \(n\), maps \(n\)-cycles bijectively to \(n\)-cycles, and preserves the period set. All corresponding cardinalities agree, even for infinite sets. Therefore the conjecture's required conjugate pair with different periods is impossible, independently of the unspecified orbit-distribution and same-measure conditions. Identity conjugacies show the theorem is nonvacuous, and topological or measure-preserving conjugacies are special cases.

## Formal statement correspondence

Lean uses a bijection `X ≃ Y` with `Function.Semiconj h f g`, i.e. pointwise conjugacy. `PeriodDataDiffer` broadly covers differing period sets, fixed-point cardinalities, least-period-point cardinalities, or cycle counts. The final clause also explicitly covers differing least periods at corresponding points.

`Statement` leaves the orbit-distribution and same-measure predicates arbitrary and allows the separating pair to differ from the initial pair, so it does not weaken the claim. `conjecture5400_false` refutes this general statement, while `conjecture5400_samePair_false` and the topological and measure-preserving corollaries cover narrower readings.

## Verification

The complete LaTeX, supplied three-page PDF, and Lean source were independently reviewed. A fresh pdfLaTeX rebuild produced three pages. The Lean 4.33/Mathlib project built successfully. Direct warning-as-error replays passed for `Conjecture5400/Basic.lean`, the root module, and the sole auxiliary file `Axioms.lean`.

An independent type audit printed the periodic-data definitions and all authored theorem types. The four main theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`. Scans found no `sorry`, admission, custom axiom, `native_decide`, unsafe implementation, external implementation, kernel bypass, or incomplete proof.

The passive checksum manifest contains one stale `conjecture.md` entry, and `SEMANTIC_REVIEW.md` has two trailing-whitespace lines. These are nonblocking hygiene issues: the submission includes no required checksum verifier, its documented reproduction commands pass, and the packaged conjecture is byte-identical to the official source.

## Conclusion

The conjugacy-invariance argument is correct, general, faithfully formalized, and independently replayed. Approved.
