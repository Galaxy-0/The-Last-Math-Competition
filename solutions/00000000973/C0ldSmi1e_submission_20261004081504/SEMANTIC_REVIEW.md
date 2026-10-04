# Independent semantic review: conjecture 00000000973

**Verdict: PASS — no mathematical or semantic blocker found in the frozen Lean sources and final report.**

This is an internal, independent source review, not an official maintainer review or acceptance. It does not claim that this reviewer independently compiled the project or inspected the PDF. The parent task records strict replay, another agent performs a separate build, and the parent handles final PDF and package checks. This review concerns the mathematical statement, formalization, report, and identity of the inspected source files.

## Materials and frozen identities

Read in full:

- The exact English and Chinese statement in `conjectures/00000000973.md`.
- `/private/tmp/tlmc973-proof/Conjecture973/Jordan.lean`.
- `/private/tmp/tlmc973-proof/Conjecture973/BoundedSet.lean`.
- `/private/tmp/tlmc973-proof/Conjecture973.lean`.
- `/private/tmp/tlmc973-proof/Check.lean`.
- The project's `lakefile.toml`, `lake-manifest.json`, and `lean-toolchain`.
- `/private/tmp/tlmc973-package/main.tex`.

The corresponding files were also compared byte for byte with the saved submission at:

`/Users/daniel/.codex/worktrees/conjecture-420/The-Last-Math-Competition/solutions/00000000973/C0ldSmi1e_submission_20261004081504`

Every listed Lean/configuration file, the report, and the bilingual source copy matched. Hashes below are SHA-256; Lean and configuration paths are relative to the project's `lean/` directory in the submission.

| File | SHA-256 |
|---|---|
| `Conjecture973/Jordan.lean` | `299fc0343ef095cc60daf0011c0cf1de14836e9e0e8077dde60e8ca3c31ad148` |
| `Conjecture973/BoundedSet.lean` | `c62844265022d390c9bd7b8fef201575c99b53c2844de4bff4b1b73f32b0e10d` |
| `Conjecture973.lean` | `ee8c252d5b1461a083b01d963926c50581cad92fa56baec14ea72336e95564a6` |
| `Check.lean` | `753e859e56eef7c8d3dafbe68db41cf4583389014e9878d0b3c99778384c5dfa` |
| `lakefile.toml` | `8e267062a5417ec0ddb8680c01b356c4fb70b30d2a247cf622228c2b28402a2f` |
| `lake-manifest.json` | `a01aea0ee8b3c9b3065dc90bc48de5ca6a3f6edda4bc5bd982e5662567ac1d35` |
| `lean-toolchain` | `55e97be96000b5e9e290c9e74482e5e317861499a5540353ce845471bded8cea` |
| Submission `main.tex` | `f94d15d7151143fb1ed243b0b23ae114a15250eb90347ff792fd1386172a82cc` |
| Submission `conjecture.md` | `3d902726a16ff01b131bb23723cc47e2250e711b672ccc83b685830fd4bf5fd4` |

The final report differs from the initially read report, hash `b70e5ecbeda164032613594a0a6b2f3d408b58f186e1b99e7a0635425b50da54`, only in pagination: page breaks were inserted before sections 2 and 4, and the break before section 3 was removed. Reversing exactly these edits restores the earlier hash. Mathematical content is unchanged.

## 1. Fidelity to the bilingual conjecture

Both language versions define the relevant property by quantifying over every n-by-n complex matrix whose spectrum is contained in K and every polynomial. They state explicitly that all matrix orders n < 15 satisfy the inequality. Neither version imposes normality, a contraction condition, a numerical-range condition, or a resolvent bound.

`SpectralSetOrder K n` faithfully retains the unrestricted domain of complex matrices and complex polynomials. It uses `spectrum ℂ A`, `Polynomial.aeval A p`, and the operator norm after `Matrix.toEuclideanCLM`. The right side is the real `sSup` of the actual set of scalar polynomial moduli. Jordan matrices are witnesses; they are not substituted for the full matrix quantifier in this definition.

`SmallOrderClaim K` requires the property for every natural n with 0 < n < 15. Refuting it at n = 2 directly refutes the explicitly stated necessary clause. Restricting to positive dimensions introduces no loophole, since the actual counterexample has dimension 2. No interpretation or separate formalization of the awkward “minimal order between 15 and 33” phrase is required. A false conjunct suffices to disprove the full conjecture; the submission does not claim separately to refute the existence of an order-33 counterexample.

## 2. Genuine Jordan matrix, spectrum, evaluation, and norm

`jordan c r` is the actual matrix `!![c, (r : ℂ); 0, c]`, for every c : ℂ and r : ℝ. `shiftedPolynomial c` is the actual polynomial `X - C c`.

The module computes `det(z I - jordan c r) = (z - c)^2`. It then obtains the actual matrix spectrum `{c}` through Mathlib's noninvertibility definition and `Matrix.isUnit_iff_isUnit_det`. The additional `jordan_operator_spectrum` theorem explicitly transports this spectrum to the associated Euclidean continuous linear operator using an algebra equivalence.

Actual algebraic polynomial evaluation yields `jordan 0 r`. Its operator action is proved to send v to the vector whose coordinate 0 is `(r : ℂ) * v 1` and whose other coordinate is zero. Applying the operator to the second Euclidean unit vector gives the lower norm bound `|r|`; the coordinate bound for the Euclidean norm proves the matching upper bound. Thus the module proves the exact Euclidean operator norm `|r|`, not an entrywise matrix norm or an assumed singular-value formula. All these theorems allow arbitrary complex centers and arbitrary real parameters, including zero and negative r.

Mathlib definitions inspected include:

- `Matrix.toEuclideanCLM`, a star-algebra equivalence to continuous endomorphisms of Euclidean space induced by its canonical orthonormal basis.
- `EuclideanSpace 𝕜 n = PiLp 2 (fun _ => 𝕜)` and the actual `EuclideanSpace.norm_single` theorem.
- `spectrum`, the complement of the resolvent set defined through invertibility, and `AlgEquiv.spectrum_eq`.
- `Matrix.isUnit_iff_isUnit_det`.

## 3. General bounded-set theorem and actual supremum

The theorem assumes exactly K.Nonempty and the ordinary norm-boundedness condition `∃ B : ℝ, ∀ z ∈ K, ‖z‖ ≤ B`. In complex normed space this is the usual bounded-set condition; Mathlib provides the equivalence `isBounded_iff_forall_norm_le`.

The proof chooses c ∈ K and a norm bound B, then sets `r = |B| + ‖c‖ + 1`. The report now uses the same absolute value of B. The nonnegative quantity D = |B| + ‖c‖ satisfies r = D + 1 > 0. The actual spectrum `{c}` is contained in K.

For the selected polynomial, the proof establishes for every z ∈ K that `‖z - c‖ ≤ ‖z‖ + ‖c‖ ≤ B + ‖c‖ ≤ |B| + ‖c‖`. This exhibits a finite upper bound for every member of the actual polynomial-norm image. The image is nonempty because c ∈ K supplies an element. Consequently `csSup_le` applies to the genuine nonempty, bounded-above set and gives `sSup ≤ D`. Its default behavior on empty or unbounded sets is never exploited. No compactness, closedness, attainment of a maximum, or nonempty interior is assumed.

The exact operator norm becomes r by the proved nonnegativity of r. The strict inequality `sSup ≤ D < D + 1 = r` then constructs an actual matrix/polynomial counterexample. `boundedSet_not_spectralSetOrder_two` applies the full predicate to this witness and derives its negation. No conclusion about all matrices is assumed in an auxiliary hypothesis.

The predicate is written for arbitrary K, but every application relevant to the conjecture has nonempty bounded K. For the actual witness polynomial, both supremum obligations are explicitly discharged in Lean.

## 4. Both disk conventions and quantifiers

`twoClosedDisks` and `twoOpenDisks` are actual unions of Mathlib metric closed balls and open balls in ℂ. The centers and real radii are quantified without fixing the arrangement.

For closed disks, the first radius need only be nonnegative to make the union nonempty. The bound `max(‖a‖ + r, ‖b‖ + s)` follows from the actual norm bound on a closed ball. The second radius is arbitrary; this strengthens the result and does not exclude the intended case of two positive radii.

For open disks, the first radius is positive, so the first center belongs to the union. Each open disk is contained in its corresponding closed disk, supplying the same finite bound. Again the second radius is arbitrary. The final two theorems negate `SmallOrderClaim` by specializing it to n = 2 and the formally checked inequalities 0 < 2 < 15.

Thus every pair of positive-radius disks is covered under both conventions, with arbitrary centers: disjoint, overlapping, nested, or coincident. There is no dependence on an unspecified geometric placement.

## 5. Report alignment and concrete example

The report's theorem, proof, and scope agree with the formal result. It identifies the exact objects used, explains the genuine supremum bound, acknowledges the stronger radius quantifiers, and describes the final conclusion as the negation of a necessary explicit source clause.

The concrete example in the report is correct: the union of the two closed unit disks centered at 0 and 3 has modulus bounded by 4, and 4 belongs to the second disk. Thus the supremum for p(z) = z is exactly 4. The displayed matrix `[[0,5],[0,0]]` has spectrum `{0}` and Euclidean operator norm 5. It is an illustration of the general construction (take c = 0 and B = 4), not a separately named theorem proving the numerical supremum equality in the Lean source. The principal general counterexample theorem and the full conjecture-clause negations are formally proved; no numerical program is needed for this illustration.

The terminology note is accurate. The usual spectral-set notion is relative to a fixed operator and requires norm inequalities in addition to spectrum containment. The report explicitly follows the stronger all-matrices definition in the conjecture and does not silently add hypotheses from other spectral-set theorems. The primary context reference, Badea–Beckermann–Crouzeix, §1.1 of https://arxiv.org/abs/0712.0522, supports this distinction; it is not used as an unformalized proof bridge.

## 6. Trust, configuration, and limits of this review

Lean 4.19.0 is pinned. The manifest pins Mathlib to `c44e0c8ee63ca166450922a373c7409c5d26b00b` (v4.19.0) and records exact revisions for every listed dependency. The build target imports both supporting modules.

`Check.lean` prints six central definitions, then checks and requests transitive axiom lists for all 17 theorems across the proof, including both final disproof theorems. A source scan of all four Lean files found no `sorry`, `admit`, custom `axiom`, `native_decide`, unsafe declaration, or option weakening checks. Ordinary proof-producing tactics and imported Mathlib theorems are used. Actual compiler and axiom-output evidence belongs to the separate build records; this source audit does not replace them.

The cached eligibility record inspected states that the conjecture was unsolved at upstream revision `0862407ef50dda4f7376342ca3e79368dce942d2`. Its exact-ID, short-ID, and comment search result files are empty, and the cached prior solution history is empty. These support the report's cautious statement that no prior submission was identified. This audit did not independently repeat remote eligibility queries.

No mathematical changes are requested. The final package must preserve the audited source/report identities or obtain a delta review; PDF rendering, final README commands, and publication bookkeeping remain the parent workflow's responsibility.
