# Solution Review — Conjecture 00000003991 (PR 770)

**Submission:** Jackmeson1 — `solutions/00000003991/Jackmeson1_submission_20261005215947`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- **Official conjecture read in full** (English + Chinese, `conjectures/00000003991.md`); shipped `conjecture.md` is **byte-identical** to it.
- **LaTeX:** entire `proof.tex` (174 lines) read; rebuilt independently with `latexmk -pdf -interaction=nonstopmode` (build succeeds). pypdf comparison shipped vs rebuilt: identical alphanumeric content after normalizing font-extraction artifacts (`\sum` signs dropped by the extractor in one PDF, `á` in "Turán" extracted as `a`, ligatures); no words, formulas or claims differ.
- **Lean build:** `lake build` succeeds with zero errors and zero warnings — Lean **v4.33.1**, Mathlib **v4.33.1** (pool rev `0df444a360`). Matches the shipped `verification/build.txt`.
- **Axioms:** no `sorry`, `admit`, `native_decide`, `implemented_by`, `extern`, `unsafe`, or declared `axiom` (the word "axiom" appears only in docstrings describing CP axiom lines). Independent `#print axioms` for `C3991.conjecture_3991_false` and `C3991.fphp_short_refutation`: only `[propext, Classical.choice, Quot.sound]` — matches the shipped `verification/axioms.txt`.
- **Aux code:** no aux scripts shipped, but the report states a Python check rebuilt the refutation and verified it line by line for n ≤ 8. I reproduced that check independently: implementing exactly the Lean construction (per hole j and 2 ≤ m ≤ n: emit the m hole axioms, form C₀ = (m−1)T_{j,m} + h₀ and C_k = C_{k−1} + h_k as positive combinations, round C_{m−1} by m) and verifying every line against an explicit rule certificate. For every n ≤ 8: all lines valid, exact length n³+2n²+n+1 (as claimed in the report), bound 8n³ satisfied, max |coefficient| ≤ 2n, last line 0 ≥ 1. All shipped verification outputs match my re-runs; `SHA256SUMS.txt` text-file mismatches are the commit-time CRLF→LF normalization artifact (verified byte-wise in the sibling submission); binary files pass.
- **Metadata:** `metadata.csv` lists 00000003991 as unsolved; the PR adds only its own submission folder.

## Semantic audit

The conjecture asserts (first clause) that every cutting-plane refutation of PHP_n has length at least 2^{n/8}, and (second clause) that the constant 1/8 cannot be improved under CP with bounded coefficients. The submission refutes the first clause — hence the conjunction, whose second clause presupposes the first — by explicitly constructing polynomial-length CP refutations for every n, in a formalization whose faithfulness is airtight.

The proof system is the standard one, not a surrogate: a `Line` is a pair (a, b) meaning Σa_vx_v ≥ b over integers; `Step` allows exactly the axioms, the Boolean axioms x_v ≥ 0 and −x_v ≥ −1, positive integer linear combinations of earlier lines, and the division rule (a/α, ⌈b/α⌉) when α > 0 divides every coefficient — precisely the two rules quoted from Beame et al. (arXiv:1710.03219) and the definition attributed to Cook–Coullard–Turán in Dantchev–Galesi–Ghani–Martin (arXiv:2102.07622). Positive rather than non-negative multipliers only restrict the system, so refutations here are refutations in the standard system of equal length. The encoding faithfulness is proved, not asserted: `fphp_sat_iff` shows the 0/1 assignments satisfying all of `FPHP n` are exactly the indicator graphs of injections `Fin(n+1) → Fin n` (pigeon axiom = totality, hole axiom = injectivity, functionality axiom = being a function), so `FPHP n` is the formalization of the absence of an injection from n+1 to n, exactly as the conjecture's definition requires.

The construction is the classical Cook–Coullard–Turán argument, carried out for all n in Lean: for each hole j, from `T_{j,m}: −Σ_{i<m}x_{i,j} ≥ −1` one derives `T_{j,m+1}` by forming `(m−1)T_{j,m} + Σ_{k<m} holeAx(k,m,j)` — the line `−m·Σ_{i≤m}x_{i,j} ≥ −(2m−1)` — and rounding by m (all coefficients divisible, `⌈−(2m−1)/m⌉ = −1`), costing 2m+1 lines; summing the pigeon axioms gives `Σ_{i,j}x_{i,j} ≥ n+1` in 2n+1 lines; adding the n hole lines cancels every variable and yields `0 ≥ 1`. I re-derived the arithmetic by hand and independently rebuilt the whole refutation in Python with per-line rule certificates for n ≤ 8: exact length n³+2n²+n+1 (matching the report), ≤ 8n³, all coefficients bounded by 2n, ending in 0 ≥ 1. The asymptotic step is Mathlib's little-o: `8n³ < c·2^{εn}` for all large n, for every ε, c > 0, whence `no_exponential_lower_bound` and `conjecture_3991_false` refute both the unrestricted 2^{n/8} lower bound and its restriction to refutations with coefficients bounded by 2n (so even "polynomially bounded coefficients" — the natural reading of clause 2 — is covered). The report is scrupulously honest about the one reading it does not address (coefficients bounded by an absolute constant independent of n), and correctly notes that this cannot save the conjunction since the first clause is refuted outright.

## Issues found

None blocking. (Cosmetic: the same CRLF-induced `SHA256SUMS.txt` text-file mismatches as the sibling submissions.)

## Verdict

APPROVED. The conjecture's central claim — a 2^{n/8} cutting-plane lower bound for the functional pigeonhole principle — is false: the submission exhibits, for every n, a machine-checked CP refutation of at most 8n³ lines with coefficients at most 2n (exactly n³+2n²+n+1 lines, matching the classical Cook–Coullard–Turán construction), ruling out every exponential lower bound of the form c·2^{εn} even under polynomially bounded coefficients. The formalization uses the conjecture's own objects (the standard CP rules and the standard fPHP encoding, with faithfulness proved), the build is clean, and the axiom footprint is exactly the standard three.
