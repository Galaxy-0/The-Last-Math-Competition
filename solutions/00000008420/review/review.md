# Solution Review — Conjecture 00000008420 (PR 635)

**Submission:** Galaxy-0 — `solutions/00000008420/Galaxy-0_submission_20261005131531`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- **Official conjecture:** read in full (`conjectures/00000008420.md`, bilingual). Compound statement: (i) existence criterion n ≡ 3 (mod 6) (known); (ii) number of parallel classes is (n−1)/2; (iii) smallest order of a KTS with a transitive automorphism is 15; (iv) no KTS has automorphism group cyclic of prime order. Submission's `conjecture.md` matches the official file.
- **LaTeX rebuild:** pass — `build-pdf.sh` (two pdflatex passes) succeeds; 2 pages; no errors.
- **PDF comparison:** pass — rebuilt `proof.pdf` text is byte-for-byte identical to the shipped PDF text after whitespace normalization (4847 chars both).
- **Lean build:** pass — `lake build` completes with zero errors on the pinned Lean 4.31.0 (core only, no Mathlib); `lake env lean -DwarningAsError=true Counterexample.lean` and `Audit.lean` both succeed.
- **Axioms:** pass — all eight authored theorems depend only on `propext` and `Quot.sound` (`cycle3_exact_order` uses only `propext`); no `sorry`, `native_decide`, `unsafe`, custom `axiom`, `extern`, or `implemented_by` anywhere.
- **Auxiliary code:** pass — `SHA256SUMS` verifies on a pristine checkout; `verify.sh` (build + strict warning-as-error elaboration + axiom audit) reproduced successfully; shipped `verification/` logs match independent output; no `check_model.py` shipped (none needed).
- **Semantic audit:** pass — decisive theorem `minimum_order_clause_false : ¬ MinimumOrderIs15`, where `MinimumOrderIs15` is (existence of a KTS(15) with a transitive automorphism) ∧ (every KTS with a transitive automorphism has ≥ 15 points). This is the exact negation of conjunct (iii) ("smallest order ... is 15" = attainment at 15 + universal lower bound), hence the exact negation of the conjecture-as-conjunction. The disproof object KTS(3) satisfies ALL stated hypotheses of a resolvable Steiner triple system.
- **Source statement ground truth:** pass.

## Semantic audit

The counterexample is the order-3 system: V = {0,1,2}, one block B = {0,1,2}, one parallel class. It is an STS (three pairs, each contained in the unique block) and resolvable (the single class partitions V), hence a KTS. The official statement does not exclude n = 3 — its own first clause asserts KTS(n) exists iff n ≡ 3 (mod 6), whose least instance is 3 — so the trivial system is squarely inside the conjecture's own objects. The permutation (0 1 2) fixes B setwise and the sole class setwise, so it is an automorphism of the resolved system; it is a single permutation of exact order 3 whose cyclic action is point-transitive, giving a KTS of order 3 < 15 with a transitive automorphism. This kills the lower-bound half of "smallest order is 15". I verified the arithmetic directly and cross-checked the example against the standard convention (Brown–Mellinger explicitly include this system, with (3−1)/2 = 1 parallel class, consistent with conjunct (ii)). The Lean definitions (incidence function into `Fin v → Bool`, resolution map, bijectivity, incidence/resolution preservation, transitivity via iterates) are standard and faithful; nothing resembling the target claim is assumed as a hypothesis.

Scope is honestly stated: the refutation targets conjunct (iii) only; conjunct (i), (ii) are untouched (and (iv) is untouched — the full automorphism group here is S3, not C3). Falsifying one conjunct of a conjunction is a valid refutation of the whole statement as written. The README also correctly distinguishes this from the author's earlier rejected PR 21 (affine plane of order 9, where a transitive translation group contains no transitive element).

## Issues found

- None material. Minor observation: the disproof succeeds because the statement as written omits a nontriviality condition (n > 3); an amended conjecture excluding order 3 would not be refuted by this construction, as the submission itself notes.

## Verdict

**APPROVED** as a valid disproof of conjecture 00000008420 as officially stated: a fully kernel-checked, axiom-clean Lean counterexample with a matching, honest report.
