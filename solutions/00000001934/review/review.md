# Solution Review — Conjecture 00000001934 (PR 722)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005154016`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results
- Official conjecture read (EN+CN): "All actions of SL(n,Z) (n ≥ 3) on (n−1)-manifolds are finite (the image is a finite group); the classification table of standard forms … exhausted by fractional-linear actions on projective space." Submission's `conjecture.md` is byte-identical to `conjectures/00000001934.md` (diff clean).
- LaTeX: `latexmk -pdf` rebuild from the shipped `proof.tex` exits 0; shipped `proof.pdf` (3 pages, produced by xdvipdfmx) matches my pdfTeX rebuild page-for-page; extracted text identical up to glyph-map/ligature extraction artifacts (− vs -, · spacing) caused by the different TeX engines.
- Lean build: `lake build` exit 0, "Build completed successfully (8708 jobs)", zero errors, zero warnings.
- Forbidden content: grep for `sorry`/`native_decide`/`admit`/`implemented_by`/`extern`/`unsafe`/`axiom` over all sources: no hits (the file `lean/Axioms.lean` contains only `#print axioms` commands). Lakefile is benign (`relaxedAutoImplicit = false`).
- Axioms: independently ran my own `CheckJ6.lean` (not the shipped one) with `#print axioms` on `contMDiff_smul`, `range_toPermHom_infinite`, `not_clause1At`, `not_clause1`, `not_conjecture`: all exactly `[propext, Classical.choice, Quot.sound]`.
- Auxiliary code: `verification/` contains build log, axiom output, SHA-256SUMS. The manifest's two "failures" (`conjecture.md`, `Basic.lean`) reproduce exactly when the files' CRLF variants are hashed — a Windows line-ending artifact of the manifest, not content drift; all other 12 hashes verify.
- Sanity check: numerically, the transvections I+kE₀₁ map e₁ to (e₀+k e₁)/‖·‖, pairwise distinct — confirmed.

## Semantic audit
The conjecture is the conjunction of clause 1 (all SL(n,Z)-actions on (n−1)-manifolds have finite image) and an informal clause 2. The submission formalizes clause 1 as `Clause1At r n`: for every d with d+1 = n, every compact, connected, Hausdorff, boundaryless C^r manifold M modeled on R^d, every MulAction of SL(n,Z) on M whose elements all act by C^r maps has finite `Set.range (MulAction.toPermHom ...)`. This is the natural faithful rendering of a Zimmer-type statement (the actual Zimmer program is about compact manifolds), uniformly over regularity r ∈ {0,1,…,∞,ω}; the added hypotheses only weaken the formal clause, and the refuting witness satisfies all of them, so the disproof extends verbatim to any weaker (hence to the literal) reading. Refuting clause 1 refutes the conjunction whatever clause 2 means, as the main theorem `not_conjecture` records.

The counterexample is the classical one: SL(n,Z) acts on the unit sphere S^{n−1} ⊂ Rⁿ by A·v = Av/‖Av‖. The Lean development proves this is a `MulAction` (radial projection invariance under positive scaling), that every element acts by a real-analytic map (`ContMDiff (𝓡 d) (𝓡 d) ω`, via Mathlib's analytic sphere manifold structure), that S^d is connected for d ≥ 1, and that the image in `Equiv.Perm (Sph n)` is infinite because k ↦ toPermHom (tv k) is injective on Z (coordinate-wise extraction of the i-th and j-th coordinates of the images of e_j, then cancellation). I verified the analyticity direction convention: in Mathlib's `WithTop ℕ∞` regularity order ω is the top element, so `of_le le_top` correctly descends C^ω to C^r for every r — the disproof covers continuous actions as well.

Mathematically this is exactly right and well known: the radial sphere action is the standard reason Zimmer's bound is dim M < n−1 (Brown–Fisher–Hurtado prove finiteness only for dim M < n−1); the report cites this context and correctly observes that the conjecture text states no volume-preservation hypothesis. Since the witness S^{n−1} is compact, connected, Hausdorff and boundaryless, no weakening or strengthening of hypotheses is being exploited: the formal statement `¬ Clause1 r` (for all r, all n ≥ 3) is the exact negation of the formalized clause, and `not_conjecture` reduces the full conjecture to it.

## Issues found
- `verification/SHA256SUMS.txt` lists CRLF hashes for two files (Windows manifest artifact); content verified identical after EOL normalization. Cosmetic.
- No other issues.

## Verdict
APPROVED. The Lean development is complete and clean (no `sorry`, only the three standard axioms — re-verified independently), the report is honest and complete, and the disproof is the mathematically correct one: the conjecture as stated is refuted by the analytic action of SL(n,Z) on S^{n−1} with infinite image, for every n ≥ 3 and every regularity class.
