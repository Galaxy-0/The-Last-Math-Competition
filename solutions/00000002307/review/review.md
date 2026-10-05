# Solution Review — Conjecture 00000002307 (PR 598)

**Submitter:** Jackmeson1  
**Submission:** `solutions/00000002307/Jackmeson1_submission_20261004200122/`  
**Head:** `f16219bdd15bb70525cbed21c92c024fa37bee39`  
**Result:** Approved

## Claim

The conjecture states that a solvable group's Fitting height is bounded by twice its derived length minus one and predicts tightness at total derived chain two. The submission refutes both precise mathematical clauses: the trivial group violates the literal numeric inequality under the standard convention \(h(1)=dl(1)=0\), and no solvable group of derived length two can attain the proposed bound because every solvable group has Fitting height at most its derived length.

## Mathematical audit

For a solvable group \(G\) of derived length \(d\), the reversed derived series runs from \(G^{(d)}=1\) to \(G\). Its successive quotients are abelian, hence nilpotent, so it is a Fitting chain of length \(d\). Therefore \(h(G)\le dl(G)\). If equality \(h=2dl-1\) held at \(dl=2\), then \(3\le2\), impossible; indeed the inequality forces \(dl\le1\). Thus the claimed derived-length-two extremal example cannot exist.

Under the standard convention that the trivial group has both invariants zero, the linear bound also fails literally: \(0\le -1\) is false. The submission separately proves that all nontrivial solvable groups do satisfy the numeric inequality, accurately distinguishing the trivial-group edge case from the structural tightness failure.

## Formal statement correspondence

Lean defines a genuine Fitting chain as subgroups from \(1\) to \(G\), normal in the next stage, with nilpotent quotients. Fitting height and derived length are minima over the corresponding chains/series. `LinearBound` states the integer inequality for finite solvable groups, and `TightAtDerivedLengthTwo` states the exact derived-length-two equality reading.

`fittingLength_le_derivedLength` formalizes the reversed-derived-series argument. `not_linearBound` uses the concrete trivial group, while `not_tightAtDerivedLengthTwo` uses the structural inequality. The final theorem negates the conjunction of the two precise clauses. The vague projection clause is not needed because the conjunction already fails.

## Verification

The complete LaTeX, supplied PDF, and Lean source were independently reviewed. A fresh pdfLaTeX rebuild produced the expected three pages. The Lean 4.33/Mathlib project built successfully from a fresh copied tree. Direct warning-as-error replays passed for `Conjecture2307/Basic.lean`, the root module, and the sole auxiliary file `Axioms.lean`.

An independent type audit printed all relevant definitions and theorem types. Every listed theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`. Despite its filename, `Axioms.lean` only prints axioms and declares none. Scans found no `sorry`, admission, custom axiom, `native_decide`, unsafe implementation, external implementation, kernel bypass, or incomplete proof. Base metadata marks the conjecture unsolved and no duplicate solution directory existed.

The passive `verification/SHA256SUMS.txt` has one stale entry for `conjecture.md`. This is nonblocking hygiene: the README does not require checksum verification, no verifier program is included, all documented build/audit commands pass, and the packaged conjecture is byte-identical to the official source.

## Conclusion

The mathematical argument is correct, faithfully formalized, non-vacuous, and independently replayed. Approved.
