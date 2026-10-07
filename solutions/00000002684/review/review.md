# Solution Review — Conjecture 00000002684 (PR 774)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005222441`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

**Kind:** DISPROOF. **Conjecture:** DML intersection count polynomial law.

## Checklist results

- **Official conjecture.** `conjectures/00000002684.md` read in full (bilingual); the submission's `conjecture.md` copy is byte-identical to it.
- **LaTeX report.** `proof.tex` read in full; rebuilt independently with `latexmk -pdf -interaction=nonstopmode` in a scratch directory (exit 0). Extracted text of shipped and rebuilt PDFs agrees after whitespace normalization; residual differences are font/ToUnicode glyph artifacts only (ligatures, math symbols such as ∑, ‖·‖, ≥), not content.
- **Lean build.** `lake build` with toolchain v4.33.1 / Mathlib `0df444a360` (prebuilt package pool via `.lake/packages` symlink): exit 0, zero errors. No warnings.
- **No cheating.** Grep for `sorry`, `native_decide`, `admit`, `implemented_by`, `extern`, `unsafe`, declared `axiom` over all `.lean` files: clean. `#print axioms` re-run independently (`lake env lean Axioms.lean`) for every decisive theorem: only `propext`, `Classical.choice`, `Quot.sound`.
- **Auxiliary code.** `verification/` contains the build log, axiom output and a SHA-256 manifest; all entries verify against the extracted files (matching after CRLF normalization, consistent with the submitter's Windows build environment). Self-reported build/axiom outputs agree with my independent runs. No other executable auxiliary code is shipped.
- **Semantic audit.** Pass; details below.

## Semantic audit

The conjecture claims the count of intersection points of an orbit with a codimension-r subvariety is a degree-r polynomial in log n along the iterates. The submission refutes it for every r ≥ 1 with an explicit polynomial self-map of 𝔸^{r+1}_ℚ: f(x₁,…,x_r,z) = (−x₁, x₂, …, x_r, z+1), start x₀ = (1,0,…,0;0), and V = {x₁ = 1, x₂ = ⋯ = x_r = 0}, the zero locus of r degree-one equations. All the geometric hypotheses are certified in Lean, not asserted: the vanishing ideal of V is prime (via the surjective restriction to ℚ[z], whose kernel is exactly the vanishing ideal), the coordinate ring has Krull dimension 1, and the ambient ring has dimension r+1, so V is an irreducible subvariety of codimension exactly r with degree vector (1,…,1). The orbit is ((−1)ⁿ, 0,…,0; n) — injective by the z-coordinate — and meets V exactly at the even times, so the hit count is ≥ N/2, while every real polynomial satisfies P(log N) ≤ N/4 eventually (`isLittleO_pow_log_id_atTop`). Hence the count is not eventually ≤ P(log N) for any polynomial of any degree or coefficients — refuting the upper-bound reading, the equality reading, and any degree-r reading (both for points and for times).

A second witness covers the finite-intersection readings: g_K(x₁,…,x_r,z) = (∏_{j<K−1}(z−j), x₂,…,x_r, z+1) with the fixed z-axis W meets W in exactly K points (the x₁-coordinate of g_K^{n+1}(0) is ∏_{j<K−1}(n−j), vanishing iff n < K), so an eventual equality c(N) = P(log N) forces P to be the constant K, of degree 0 ≠ r; and no single polynomial bounds the counts uniformly over all K, so coefficients depending only on the subvariety cannot rescue the claim. The report is scrupulous about what is and is not refuted: if the claim is restricted to finite intersections with coefficients allowed to depend on f and x₀, it is trivially true and is explicitly left standing. The witness also respects the DML-flavored structure (the return set of Witness 1 is a single arithmetic progression, and V is invariant under f²), so it is not an artifact of pathological returns.

I verified the orbit formula and both witnesses numerically (parity of n for membership in V; the falling factorial ∏_{j<K−1}(n−j) vanishing exactly on n < K−1 at time n+1) and the asymptotic lemma P(log N) ≤ N/4. The injectivity of the orbit, the non-degeneracy check (x₀ ∈ V, f x₀ ∉ V), and the codimension certificates are all machine-checked.

## Issues found

None material.

## Verdict

APPROVED. A decisive disproof: for every r ≥ 1 an explicit polynomial map and codimension-r subvariety whose orbit–variety hit count grows like N/2 and therefore beats every polynomial in log N, refuting the claimed polylogarithmic law in upper-bound, equality, and degree-r readings, with a second witness covering the finite-intersection readings.
