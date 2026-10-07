# Solution Review — Conjecture 00000003526 (PR 776)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005223310`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

**Kind:** PROOF. **Conjecture:** ordinal tree well-founded rank height.

## Checklist results

- **Official conjecture.** `conjectures/00000003526.md` read in full (bilingual); the submission's `conjecture.md` copy is byte-identical to it.
- **LaTeX report.** `proof.tex` read in full; rebuilt independently with `latexmk -pdf -interaction=nonstopmode` in a scratch directory (exit 0). Extracted text of shipped and rebuilt PDFs agrees after whitespace normalization; residual differences are font/ToUnicode glyph artifacts only (ligatures, math symbols such as ∑, ‖·‖, ≥), not content.
- **Lean build.** `lake build` with toolchain v4.33.1 / Mathlib `0df444a360` (prebuilt package pool via `.lake/packages` symlink): exit 0, zero errors. No warnings.
- **No cheating.** Grep for `sorry`, `native_decide`, `admit`, `implemented_by`, `extern`, `unsafe`, declared `axiom` over all `.lean` files: clean. `#print axioms` re-run independently (`lake env lean Axioms.lean`) for every decisive theorem: only `propext`, `Classical.choice`, `Quot.sound`.
- **Auxiliary code.** `verification/` contains the build log, axiom output and a SHA-256 manifest; all entries verify against the extracted files (matching after CRLF normalization, consistent with the submitter's Windows build environment). Self-reported build/axiom outputs agree with my independent runs. No other executable auxiliary code is shipped.
- **Semantic audit.** Pass; details below.

## Semantic audit

The conjecture states, for ordinal trees, that vanishing of descending chains is well-foundedness and that the rank of well-foundedness is the ordinal height. The submission proves this for both standard readings of 'tree'. Reading A (descriptive-set-theoretic trees of finite sequences): `treeWF_iff_no_descChain` and `no_descChain_iff_wf` give no-branch ⟺ no infinite descending chain ⟺ the strict-extension relation is well-founded; `wf_iff_exists_ranking` adds the order-reversing-map formulation. For well-founded trees the rank `nodeRank` (Mathlib's `Acc.rank`) satisfies the one-step child recursion (`nodeRank_eq_iSup_child`), is the unique function doing so (`nodeRank_unique`), is the least order-reversing map (`nodeRank_le_of_ranking`), and the ordinal height — defined independently as the least bound of an order-reversing map — equals sup_s(ρ(s)+1) = ρ(∅)+1 (`ordHeight_eq_treeRank`, `treeRank_eq_succ_root`); moreover every ordinal α is realized as the root rank of the tree of strictly decreasing sequences below α, with height α+1 (`ordinal_tree_realization`). Reading B (set-theoretic trees, partial orders with well-ordered initial segments): < is well-founded, the well-founded rank of each node equals its height (order type of its initial segment, `setRank_eq_ht`), and the tree height equals sup(rank+1) (`setTreeHeight_eq_rank`).

The definitions are faithful and the junk values are quarantined: `nodeRank` is 0 and `ordHeight` is 0 on ill-founded trees, but every rank theorem carries the well-foundedness hypothesis explicitly. `ordHeight` is deliberately defined without mentioning ρ, so `ordHeight_eq_treeRank` is a theorem, not a restatement — exactly the content of 'the rank of well-foundedness is the ordinal height'. The branch-to-chain and chain-to-branch directions are both proved (the latter constructing the branch from the k-th entries of the chain, using strictly growing lengths and prefix stability), so 'vanishing of descending chains is well-foundedness' is an equivalence as claimed. The report quotes the two Wikipedia tree definitions it follows and notes that the descending-chain criterion uses dependent choice, supplied by `Classical.choice`.

I checked the realization theorem's content (the rank of a node of the decreasing-sequences tree is its last entry; the sup over children of a bound b is b, so the root rank is α and the height α+1) and the typein computation of Reading B against the standard rank-equals-height lemma for well-orders. Both readings cover the phrase 'ordinal trees' (trees on ordinals are the special case A = Ord of Reading A, realized concretely by `decTree`).

## Issues found

None material.

## Verdict

APPROVED. The conjecture is proved in both standard formalizations of 'tree', with the full chain of equivalences, the rank recursion with uniqueness and minimality, and the rank–height equality — all faithful to the statement and cleanly machine-checked.
