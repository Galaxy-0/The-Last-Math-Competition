# Solution Review — Conjecture 00000007793 (PR 754)
**Submission:** Jackmeson1 — `solutions/00000007793/Jackmeson1_submission_20261005205556`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results
- **Official conjecture read in full** (bilingual, `conjectures/00000007793.md`); shipped `conjecture.md` is **byte-identical** to it (`diff` clean).
- **LaTeX:** entire `proof.tex` read; rebuilt independently with `latexmk -pdf -interaction=nonstopmode` — exit 0, 3 pages as shipped. Rebuilt vs shipped PDF text compared with pypdf after Unicode/whitespace normalization: content matches; differences are pure extraction artifacts (the shipped PDF's fonts map `|`, `→`, `∈`, `√`, `−`, `≤` to placeholder glyphs while the rebuild carries proper ToUnicode maps, plus one hyphenation split) — cosmetic.
- **Lean build:** `lake build` re-run: **zero errors, zero warnings**, `Build completed successfully (8708 jobs)`; toolchain `leanprover/lean4:v4.33.1`, Mathlib rev `0df444a360` (v4.33.1).
- **Axioms:** no `sorry`/`admit`/`native_decide`/`implemented_by`/`extern`/`unsafe`/declared `axiom` anywhere. Independent audit via `lake env lean Axioms.lean`: `C7793.not_conjecture` and `C7793.not_conjecture_rv` depend only on `[propext, Classical.choice, Quot.sound]`; matches shipped `verification/axioms.txt`.
- **Aux code:** `verification/axioms.txt` reproduced by my fresh run; `build.txt` consistent with a clean 8708-job build; all 14 SHA-256 checksums in `SHA256SUMS.txt` match the shipped files after CRLF→LF normalization (author hashed on Windows; `proof.pdf` matches as-is).
- **Metadata:** `metadata.csv` lists 00000007793 as `proven=false, disproven=false`; no solution folder for it on `main`.

## Semantic audit
The conjecture's definition fixes the objects: `R = |X−Y|` for two independent isotropic uniform ball points, and the first conjunct claims `Var(R)/Var(|X|) = 2 − 2/√3 + O(n^{-1})` with `n` the dimension. The submission models exactly these objects: `ballUnif n` is normalized Lebesgue measure on the open Euclidean unit ball, independence is the product measure (or `IndepFun` in the general random-variable form), the norm is the Euclidean one, and `ratio n` is Mathlib's variance ratio. The decisive theorem `C7793.not_conjecture` states precisely `¬ (fun n => ratio n − (2 − 2/√3)) =O[atTop] (1/n)` — the exact negation of the asymptotic — and `not_conjecture_rv` lifts it to arbitrary radii `r_n > 0`, which covers the isotropic normalization (the ratio is scale-invariant, proved in Lean via `map_smul_ballUnif`). Refuting the first conjunct refutes the conjecture-as-conjunction; the report says explicitly that the `−1/(3√3)` coefficient and the coupling clause are not addressed separately.

The proof is short and airtight, and I re-verified every step by hand. (1) Radial moments: `E|X|^k = n/(n+k)` from Mathlib's polar-coordinate formula, giving `Var|X| = n/(n+2) − (n/(n+1))² = n/((n+1)²(n+2))` — I confirmed this identity to 1e-16 by quadrature at n=1 and by Monte Carlo for n = 2,…,20. (2) Lower bound on `Var(R)`: with `a = ‖x−y‖`, `b = ‖x+y‖` one has `4⟨x,y⟩ = (b−a)(b+a)` and `a,b ≤ 2`, so `⟨x,y⟩² ≤ (b−a)² ≤ 2((a−c)²+(b−c)²)` with `c = E‖X−Y‖`; the reflection `Y ↦ −Y` preserves the product law and makes the `‖X+Y‖` term equal the `‖X−Y‖` term, whence `E⟨X,Y⟩² ≤ 4 Var(R)`. (3) Independence and Cauchy–Schwarz on `m_{ij} = E X_iX_j` give `E⟨X,Y⟩² = Σ m_{ij}² ≥ (Σ m_{ii})²/n = (E|X|²)²/n = n/(n+2)²`. Combining, `ratio n ≥ (n+1)²/(4(n+2)) ≥ n/8 → ∞`. The Lean bounding of the reflection and integrability details (continuous functions on the compact closed ball) is careful and correct.

The mathematics is not merely formally valid but quantitatively honest: Monte Carlo gives `a_1 = 8/3` (exactly `(2/9)/(1/12)`, matching the report), `a_10 ≈ 7.3` (report: ≈7.4), and growth roughly like `n/2` toward `+∞`, while the conjectured limit is `2 − 2/√3 ≈ 0.845`; the Lean lower bound `~n/4` is a faithful, non-vacuous certificate of divergence. No toy surrogate is involved — the witness measure is the conjecture's own object, and the quantifier structure of the negation is exact.

## Issues found
None blocking. Non-substantive: `SHA256SUMS.txt` hashes were computed with CRLF line endings (git normalized to LF), so a naive checksum run reports 2 mismatches until normalization; contents verified identical.

## Verdict
APPROVED. A complete, faithful, machine-checked refutation: the decisive theorem negates exactly the conjectured asymptotic for the conjecture's own objects, every inequality was re-derived independently and confirmed numerically, the build is clean, and the axiom footprint is minimal.
