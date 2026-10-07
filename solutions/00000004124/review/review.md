# Solution Review — Conjecture 00000004124 (PR 761)

**Submission:** Jackmeson1 — `solutions/00000004124/Jackmeson1_submission_20261005212441`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- **Official conjecture:** `conjectures/00000004124.md` read in full (English + Chinese). The submission's `conjecture.md` is byte-identical to it (`diff` clean).
- **LaTeX report:** entire `proof.tex` read. Independently rebuilt with `latexmk -pdf -interaction=nonstopmode`; build succeeds with no errors.
- **PDF comparison:** shipped vs rebuilt PDF text compared with pypdf. Content identical modulo glyph-extraction artifacts (the rebuilt font's `_` and the cmex big-cup `\bigcup` map differently in text extraction; rendered content is the same).
- **Lean build:** `lake build` (Lean 4.33.1, Mathlib v4.33.1, pinned 0df444a360 pool) completes with zero errors: `Build completed successfully (8708 jobs)`.
- **No cheating:** grep for `sorry`, `native_decide`, `admit`, `implemented_by`, `extern`, `unsafe`, `axiom` over all `.lean` files finds nothing. Independent `lake env lean Axioms.lean` reproduces: `conjecture4124_false` depends only on `[propext, Classical.choice, Quot.sound]`.
- **Auxiliary code:** `verification/` contains build log, axiom output and SHA-256 sums; all reproduce and all 14 hashes match the shipped files.
- **Faithfulness gate:** the decisive theorem quantifies over actual partial orders / preorders / posets-with-top in `Type u` with the standard forcing definitions (compatible = common lower bound; ccc = every antichain countable; Knaster/property K = every uncountable set has an uncountable linked subset). It does not assume the negation of the conjecture as a hypothesis, nor instantiate toy structures only.
- **Semantic audit:** the conjecture is a conjunction; the submission refutes the first conjunct ("least cardinality of a poset separating ccc from the Knaster property is aleph_2"), which refutes the whole. Since Knaster ⇒ ccc (proved as `ccc_of_knaster`), a separator is exactly a ccc, non-Knaster poset. The decisive theorem `conjecture4124_false` states the exact negation of the aleph_2 claim under both natural readings (`IsLeast` and `sInf`), for three standard notions of "poset". This is a disproof of the stated claim, not of a strawman.
- **Independent mathematical check:** the argument is sound. Knaster ⇒ ccc (an uncountable antichain would have an uncountable linked subset, whose two distinct members are both compatible and incompatible). Countable ⇒ Knaster vacuously, so any separator has |P| ≥ aleph_1. If a separator P exists, failure of Knaster yields an uncountable A ⊆ P with no uncountable linked subset; take W ⊆ A of size aleph_1 and close under a chosen common-lower-bound function f. The closure Q = ⋃_n S_n has size aleph_0 · aleph_1 = aleph_1, contains W, is ccc (Q-antichains are P-antichains), and is not Knaster (any uncountable B ⊆ W linked in Q would be linked in P). So aleph_1 ∈ S whenever S ≠ ∅, and every element of S is ≥ aleph_1: the least element is aleph_1 or does not exist — never aleph_2. The Suslin-tree clause is correctly left unformalized since the refuted first conjunct already kills the conjunction; the report's discussion of the Suslin-tree example (size aleph_1, not aleph_2) is consistent with the result.

## Issues found

None material. The report's parenthetical that "the infimum of the empty set of cardinals is 0" matches Mathlib's `Cardinal.sInf_empty` as used in the proof.

## Verdict

**APPROVED.** A genuine ZFC disproof of the aleph_2 claim: the least cardinality of a ccc, non-Knaster poset is aleph_1 if any separator exists, and no least element otherwise, so the conjecture's first conjunct — hence the conjecture — is false in every model of ZFC. Formally verified with no extra axioms.
