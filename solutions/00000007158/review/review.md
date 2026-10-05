# Solution Review — Conjecture 00000007158 (PR 599)

**Submitter:** C0ldSmi1e  
**Submission:** `solutions/00000007158/C0ldSmi1e_submission_20261005033139/`  
**Head:** `9c4eb85ae4566b42a34d59ce179e79f5c738bddf`  
**Result:** Approved

## Claim

The conjecture asserts that a real matrix's complex spectral imaginary-part bandwidth equals the norm of its antisymmetric part, and adds a claim about normal minimizers. The submission disproves the explicit bandwidth equality with a concrete matrix, thereby refuting the written conjunction without inventing constraints for the underspecified minimization clause.

## Mathematical audit

Let

\[
N=\begin{pmatrix}0&2\\0&0\end{pmatrix}.
\]

Since \(N^2=0\), its complex algebraic spectrum is exactly \(\{0\}\), so both imaginary extrema and the actual imaginary bandwidth are zero. Its antisymmetric part is

\[
\frac{N-N^T}{2}=
\begin{pmatrix}0&1\\-1&0\end{pmatrix},
\]

a quarter-turn isometry of Euclidean operator norm \(1\). Thus the asserted equality would require \(0=1\), which is impossible. The witness is a concrete non-normal \(2\times2\) real matrix.

The counterexample is convention-robust. The maximum-absolute-imaginary-part convention is also zero; multiplying the norm by any positive factor still gives a nonzero value; the unhalved antisymmetric part has norm \(2\); and every genuine norm assigns the nonzero quarter-turn a positive value. Viewing the real matrix over \(\mathbb C\), its transpose is its adjoint, and the corresponding skew-Hermitian and Hermitian imaginary-part conventions also give norm \(1\).

## Formal statement correspondence

Lean uses Mathlib's actual algebraic spectrum and proves its equivalence with nonzero complex eigenvectors. `imaginaryBandwidth` is the supremum minus infimum of imaginary parts of that spectrum, `antisymmetricPart` is `(A - A.transpose)/2`, and `Matrix.L2OpNorm` explicitly selects the Euclidean operator norm. `BandwidthEquality` universally quantifies over every positive dimension and real matrix.

`counterexample_spectrum`, `counterexample_imaginaryBandwidth`, `counterexample_antisymmetricPart_norm`, and `counterexample_bandwidth_ne_norm` establish the counterexample. `bandwidthEquality_false` negates the universal equality. `conjecture_conjunction_false` negates its conjunction with an arbitrary additional proposition, covering the minimization clause without assigning it an invented meaning. This is a non-vacuous, exact correspondence to the written claim.

## Verification

The complete LaTeX and Lean sources were independently reviewed. A fresh pdfLaTeX rebuild produced the expected two pages. The linked Lean 4.19 project built successfully. Direct warning-as-error replays passed for `Conjecture7158.lean`, `Check.lean`, and the environment inventory.

`Check.lean` printed all eight definitions and all 24 authored theorem types and axiom dependencies. The full environment inventory found exactly 42 constants from the proof module, including ten generated constants, with no unsafe, partial, or axiom declarations. Every theorem used only `propext`, `Classical.choice`, and `Quot.sound`.

Both Python auxiliary scripts were syntax-checked and independently replayed. The verification coordinator passed dependency-pin, fresh-build, strict-replay, source-declaration, forbidden-token, and environment checks. PDF export replay succeeded. All 36 packaged SHA-256 entries independently matched. There is no required external numerical computation; all mathematics is symbolic in Lean.

Scans found no `sorry`, admission, custom axiom, `native_decide`, unsafe implementation, `implemented_by`, `extern`, kernel-check bypass, or incomplete proof. Base metadata marks the conjecture unsolved and no duplicate solution directory existed.

## Conclusion

The submission provides a complete, faithful, and independently verified disproof. Approved.
