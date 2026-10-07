# Solution Review — Conjecture 00000004285 (PR 667)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005092743`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- Conjecture read in full from `conjectures/00000004285.md` (bilingual); shipped `conjecture.md` is byte-identical (`diff` clean). Extraction matches the PR tree file-for-file and hash-for-hash (15 files).
- LaTeX rebuilt independently with `latexmk -pdf` in a scratch dir; shipped vs rebuilt PDFs compared by normalized extracted text (pypdf) and rendered page images. Content identical; residual diffs are glyph-extraction artifacts only (the `∈` symbol and `|·|` bars extract differently between the two PDF builds).
- `lake build` in the submitted `lean/` project: success, 8708 jobs, zero errors, zero warnings. Toolchain Lean 4.33.1, Mathlib v4.33.1 rev 0df444a360 (prebuilt pool).
- Cheating scan clean: no `sorry`, `admit`, `native_decide`, `implemented_by`, `extern`, `unsafe`, or declared `axiom`. Independent scratch `Check.lean` with `#print axioms` for all seven decisive theorems (`not_minCardClaim`, `exists_countable_two_free_not_three_free`, `G_two_free`, `G_not_three_free`, `bad_finite`, `key_dvd`, `bounded_den`): only `propext`, `Classical.choice`, `Quot.sound`.
- Aux code: `verification/axioms.txt` and `verification/build.txt` reproduce exactly under my independent run. Minor blemish (non-blocking): `verification/SHA256SUMS.txt` is stale for `conjecture.md` and `proof.tex`; the shipped files themselves are correct (`conjecture.md` byte-identical to the official; all files match the PR git tree).
- Metadata: `metadata.csv` lists 00000004285 as `proven=false, disproven=false` at submission time; no competing solution on main.

## Semantic audit

The conjecture defines n-free (every subset of size at most n is contained in a free pure subgroup) and claims that the smallest cardinality of a group that is n-free but not (n+1)-free is ℵ_{n-1}, with strictly increasing cardinal spectrum and optimal bound. The submission reads this exactly as written: abelian groups (purity is an abelian-group notion), "free" = free ℤ-module, "pure" = the standard mA ∩ H ⊆ mH. Its `NFree n A` quantifies over Finsets of card ≤ n into a pure, ℤ-free subgroup — matching the definition clause verbatim. Its `MinCardClaim` formalizes the main clause as `∀ n ≥ 1, IsLeast {κ | ∃ A, #A = κ ∧ NFree n A ∧ ¬ NFree (n+1) A} ℵ_{n-1}`.

The disproof exhibits, at n = 2, a counterexample satisfying all the stated hypotheses: the explicit countable group G = ℤ³ + Σ_k ℤ·w_k ⊆ ℚ³ with w_k = (1,k,k²)/p_k, p_k the k³-th prime. G is 2-free: any two elements of ℚ³ lie in a rational hyperplane, cleared to an integer vector N ≠ 0; H = ker(N·) ∩ G is pure (ℚ³ is torsion-free) and has bounded denominators — multiplying N·g = 0 by ∏ p_k over the support and reducing mod p_j shows p_j ∣ c_j whenever p_j ∤ q_N(j), and only finitely many j are "bad" since p_k ≥ k³ outgrows |q_N(k)| ≤ A k²; so M·H ⊆ ℤ³ and H is finitely generated, torsion-free, hence free. G is not 3-free: a pure subgroup containing e₀,e₁,e₂ contains every w_k (p_k·w_k ∈ H and purity give w_k ∈ H by torsion-freeness), and a basis coordinate functional f would force p_k ∣ f(e₀)+k·f(e₁)+k²·f(e₂) for all k, which by the finiteness lemma kills the coefficient vector, contradicting f(e₀) ≠ 0. Since #G ≤ ℵ₀ while the conjecture asserts the least cardinality is ℵ₁ = ℵ_{2-1}, the `IsLeast` lower-bound half fails, and with it the whole conjunction (the "strictly increasing / optimal" clauses are restatements of the least-cardinality claim).

The formalization is faithful: it works with the conjecture's own objects (abelian groups, purity, ℤ-freeness), assumes no deep theorem as a hypothesis (everything from `import Mathlib` down to Baer-style arithmetic on primes is proven), and does not trivialize the claim — the counterexample is a concrete subgroup of ℚ³, and the refutation of a ∀n statement by a single n is the exact logical negation. The paper is also honest about scope (n = 1 is untouched; cardinal-indexed "κ-free" readings and non-abelian readings are not refuted). I verified the arithmetic input numerically (p_k ≥ k³; the divisibility sets {k : p_k ∣ q_a(k)} are empty or tiny for sampled nonzero a).

## Issues found

None blocking. (Verification-only: `verification/SHA256SUMS.txt` records stale hashes for `conjecture.md` and `proof.tex`; the files themselves match the PR tree and the official conjecture copy.)

## Verdict

APPROVED. This is a complete, faithful, and correct disproof: a concrete countable abelian group that is 2-free but not 3-free, refuting the conjecture's least-cardinality claim at n = 2 and thereby the conjunction. The Lean development is self-contained, builds with zero errors and zero warnings, depends only on the three standard axioms for every decisive theorem, and the accompanying paper matches both the Lean content and the official bilingual conjecture text.
