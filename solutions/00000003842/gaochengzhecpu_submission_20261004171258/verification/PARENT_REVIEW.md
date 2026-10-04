# Parent review of conjecture 00000003842

Verdict: PASS.

Reviewer: the coordinating AI agent that delegated this problem. This is an internal review
within the same workflow, not an external or independent peer review. No source file was
changed in review.

1. Source and reading. The English text counts classes of length at most l, the Chinese text
   classes of length l over an alphabet of n letters. Both are stated as propositions over all
   n and l and both are refuted.
2. Objects. The hypoplactic congruence is Mathlib's `conGen` of the Knuth relations together
   with the two quartic relations on Mathlib's `FreeMonoid`; the monoid is the quotient. The
   relations agree with the standard presentation as I know it (cadb = acbd for a <= b < c <= d
   and bdac = dbca for a < b <= c < d). `knuth_instance` and `quartic_instance` show that both
   families identify distinct words, so the congruence is not the identity. Class sets are
   subsets of the quotient; plane partitions are arrays with values in {0..c}, weakly
   decreasing along rows and columns.
3. Argument. Every defining relation preserves length and relates words of length 3 or 4, so a
   word of length at most 2 is alone in its class. I rechecked the congruence argument in the
   paper's Lemma 1 and the three counts: 4 classes of length 2 and 7 of length at most 2 over
   two letters, and 20 plane partitions in the 2x2x2 box (sum over x >= w of (x-w+1)^2 =
   3 + 8 + 9). The count 20 is a kernel evaluation over all 81 arrays.
4. Robustness. The counterexamples use only that relations preserve length and have length at
   least 3, so they do not depend on the exact form of the quartic relations; the paper says
   this. The one-letter and length-one families show the failure is not confined to one
   instance.
5. Final statements. `ClaimedIdentityUpTo` and `ClaimedIdentityExact` quantify over all n and
   l; the theorems negate them at n = l = 2.
6. Earlier submission. The account of PR #280 matches the reviewer's public comment. The
   publication text acknowledges it and says the example was right.
7. Not formalised, and stated as such: exact values for longer words, MacMahon's formula, the
   quasi-ribbon count and the table in the remark.
8. Evidence. `validate_draft.py`: fresh build with warnings as errors, only `propext`,
   `Classical.choice`, `Quot.sound`, three PDF pages, no TeX warnings; recorded hashes match
   the files. All three rendered pages (prefix 37810a08d11e) were opened and inspected: no
   clipping, overflow or missing glyphs.
