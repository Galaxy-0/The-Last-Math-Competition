# Solution Review — Conjecture 00000001729 (PR 742)

**Submission:** Jackmeson1 — `solutions/00000001729/Jackmeson1_submission_20261005195052`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- **Official conjecture read in full** (English + Chinese) from `conjectures/00000001729.md`: Campana points = rational points satisfying orbifold denominator divisibility conditions; the count of Campana points of (P¹, 2[0]+2[1]+2[∞]) "is always c·√B/√(log B)", with a second conjunct about "additive-energy duality". Shipped `conjecture.md` is **byte-identical** to the official file (`diff` clean).
- **LaTeX rebuild:** independent `latexmk -pdf` from the shipped `proof.tex` succeeds; pypdf comparison (whitespace/ligature-normalized) shows identical content; all textual differences are glyph-extraction artifacts of the shipped font subsets (e.g. ∞ extracted as "1", √ as "p", ≤/≥ as control codes) — cosmetic.
- **Lean build:** independent `lake build` (Lean `v4.33.1`, Mathlib v4.33.1, pool rev 0df444a360) — **Build completed successfully (8708 jobs), zero errors, zero warnings**, ~55 s.
- **Axioms:** `lake env lean Axioms.lean` prints only `[propext, Classical.choice, Quot.sound]` for `C1729.campana_count_disproof` and `C1729.campana_count_pow_disproof`; matches `verification/axioms.txt`. Greps for `sorry`/`native_decide`/`admit`/`implemented_by`/`extern`/`unsafe`/declared `axiom` are clean.
- **Aux code:** no computation scripts; `verification/build.txt` consistent with the independent rebuild; `SHA256SUMS.txt` — the single `conjecture.md` mismatch matches exactly after CRLF conversion (author hashed Windows CRLF files; git stores LF); all 13 other entries verify as stored.
- **Metadata:** `metadata.csv` lists 00000001729 as unsolved; no solution folder for it on main. README eligibility statement accurate; README line count (370) matches the Lean file.

## Semantic audit

The conjecture asserts that the count N(B) of Campana points of the orbifold (P¹, 2[0]+2[1]+2[∞]) is "always" c·√B/√(log B). The submission refutes this first conjunct under every reading that implies an order of magnitude — eventual equality with c√B/√(log B) for any real c, asymptotic equivalence for any real c, and even Big-O — which suffices to refute the conjunction; the undefined "additive-energy duality" conjunct is not needed.

The formalization is faithful to the conjecture's own objects. On the standard model P¹_Z, a rational point x = a/b (lowest terms, b > 0) off {0, 1, ∞} has p-adic intersection numbers v_p(a), v_p(b), v_p(a−b) with [0], [∞], [1]; the Campana condition for multiplicity 2 — the conjecture's "orbifold denominator divisibility conditions" — is that each of these is 0 or ≥ 2 for every prime p. This is exactly `IsCampanaPoint`, and it coincides with the squareful-triples condition studied by Browning–Van Valckenborgh (arXiv:1106.4472, cited as context only). Since the conjecture does not pin down a height, the submission proves the disproof for the naive height H = max(|a|, b) and, by a clean monotonicity comparison (`count_le_countPow`), for every height H^κ with 0 < κ ≤ 1 — which includes the orbifold anticanonical height H^{1/2} (−(K+Δ) has degree 2 − 3/2 = 1/2). This covers all plausible readings of B.

The mathematics is correct and fully machine-checked. The family x = (m²+n²)²/(m²−n²)² for coprime m odd, n even gives reduced fractions with a, b, a−b = (2mn)² all nonzero perfect squares (whence Mult2 via v_p(k²) = 2v_p(k)), x ∉ {0,1}, height (m²+n²)², and injectivity (m² ± n² arguments with parity killing the sign ambiguity). The counting lemma `card_good` shows at least K²/2 pairs (i, j), i < K, 1 ≤ j ≤ K with gcd(2i+1, 2j) = 1, via a union bound: every bad pair is divisible by an odd d = 2e+3 ≤ 2K, contributing at most ⌊2K/d⌋·⌊K/d⌋ ≤ 2K²/d² bad pairs, and Σ 1/(2e+3)² ≤ 1/4 − 1/(4(K+1)) by the telescoping bound 1/(2e+3)² ≤ 1/(4(e+1)) − 1/(4(e+2)), which holds since (2e+3)² ≥ 4(e+1)(e+2). My independent verification of this telescoping inequality and a brute-force count of Campana points (N(1024) = 111197 at K = 2; N(5184) = 1448573 at K = 3, both ≫ K²/2) confirm the lower bound with a huge margin; the family points themselves were checked to be distinct Campana points of height ≤ 64K⁴. From N(64K⁴) ≥ K²/2 with K ≫ e^{256C²}, the negation of Big-O follows by evaluating at B = 64K⁴ (√B = 8K², √(log B) > 16|C|), and ¬O kills eventual equality and asymptotics (`readings_of_not_isBigO`).

This is a genuine counterexample family of the conjecture's own objects (actual Campana points of the actual orbifold), the decisive theorems are exact negations of the claimed asymptotic under its three readings, and no hypothesis is strengthened: the points satisfy all stated Campana conditions and the bounds are unconditional for all K.

## Issues found

None blocking. Trivial notes: (i) the report says `#print axioms` was run for "each of the three theorems" while `Axioms.lean` prints the two main theorems (`campanaCount_lower` is an intermediate lemma used by both) — immaterial; (ii) the SHA256SUMS CRLF artifact as described above.

## Verdict

APPROVED. A faithful, self-contained, machine-checked disproof: the Campana count of (P¹, ½[0]+½[1]+½[∞]) grows at least like √B/16 along an unbounded sequence of B (indeed ≫ √B by a large margin), so it is not c√B/√(log B) in any sense implying that order of magnitude — for the naive height and all heights H^κ, 0 < κ ≤ 1, including the orbifold anticanonical. Build clean, axioms minimal, report matches the code.
