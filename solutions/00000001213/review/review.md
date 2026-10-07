# Solution Review — Conjecture 00000001213 (PR 636)

**Submission:** Jackmeson1 — `solutions/00000001213/Jackmeson1_submission_20261005063538`
**Head:** `9dd787a879e44ca250c4ba7c22013e56405a1f39`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06
**Result:** Approved

## Checklist results

- Official conjecture (`conjectures/00000001213.md`, English + Chinese) read in full; the submission's `conjecture.md` is byte-identical to it. Source-md check: pass.
- LaTeX report read in its entirety; independent `latexmk -pdf` rebuild succeeded; extracted text of shipped and rebuilt PDFs matches exactly at the normalized-character level (4158 chars) and modulo word-boundary/ligature artifacts at the word level. PDF-match check: pass.
- `lake build` (Lean v4.33.1, Mathlib v4.33.1) exits 0 with zero errors and zero warnings. Lean-build check: pass.
- No `sorry`, `admit`, `native_decide`, `implemented_by`, `extern`, `unsafe`, or declared `axiom`. `#print axioms` for `conjecture_00000001213_false`, `not_clause3`, `not_clause3'`, `hutchings`, `clause1_true` → `[propext, Classical.choice, Quot.sound]` only, independently re-run via the shipped `Axioms.lean`. Axiom check: pass.
- Auxiliary `verification/` material agrees with independently reproduced results; the stale SHA256SUMS entry (`conjecture.md`, plus `lean/Conjecture1213/Basic.lean`) hashes CRLF newline variants — bookkeeping artifact, content identical. Aux check: pass (this submission has no separate scripts; the decisive external check was mine, see below).
- Semantic audit: pass (details below), including independent numerical and literature verification.

## Semantic audit

This is a disproof of a three-part claim: (C1) the first player wins Sylver coinage; (C2) every winning first move is composite; (C3/C3′) no prime first move is winning — after a prime opening the second player has a winning response. The submission proves (C1) and refutes (C2) and both phrasings of (C3) by establishing Hutchings' theorem: every prime `p ≥ 5` is a winning first move, specialized to `p = 5`. The disproof structure is faithful to the bilingual text: `WinningFirstMove n := Legal ∅ n ∧ n ≠ 1 ∧ Outcome anyNumber false {n}` captures "the second player, to move, loses", `Clause2`/`Clause3`/`Clause3'` are formalized in both of the text's phrasings, and each is refuted by the single witness `five_wins` (`not_clause2`, `not_clause3`, `not_clause3'`), with determinacy (`not_win_and_lose`) ensuring a position cannot be both won and lost.

The mathematics is the classical Hutchings strategy-stealing argument, and it is correct. After the prime opening `p` and any legal reply `q`, legality forces `q > 1` and `p ∤ q`, hence `gcd(p, q) = 1`. Let `t = pq − p − q`, the Frobenius number of `⟨p,q⟩` (Mathlib `frobeniusNumber_pair`). By the two-generator symmetry lemma (`gap_symm`, the Sylvester exchange `t − x = (p−1−a)q + (q−1−b)p` after writing `x + pq = aq + bp` with `a < p`, `b < q`), every gap `x` satisfies `x ≤ t` and `t − x ∈ ⟨p,q⟩`; in particular the game from `{p,q}` is finite (all legal moves `≤ t`) and `t` itself is legal. Determinacy (`determined`, induction on the number of legal moves below the bound) splits the argument: if naming `t` leaves the opponent lost, the first player names `t`; otherwise the opponent has a winning reply `x` from `{p,q,t}`, and since `t = x + (t−x)` with `t − x ∈ ⟨p,q⟩`, the positions `{p,q,x}` and `{p,q,t,x}` generate the same submonoid (`le_antisymm` of closures), so by closure invariance (`outcome_congr`) the first player can play `x` immediately from `{p,q}` with the same winning outcome. Either way the second player's every reply loses: the prime opening wins. I verified the lemma chain line by line; the game formalization (`Legal` via non-membership in `AddSubmonoid.closure`, the inductive `Outcome` with `n ≠ 1` excluded from winning moves and vacuous loss when only 1 is legal, exactly matching "naming 1 loses") is faithful and is credited to the accepted solution of conjecture 00000008869.

Because this submission's conclusion contradicts a tempting misreading of the literature, I ran two independent external checks. (1) Literature: Wikipedia's *Sylver coinage* article and Guy & Smith (1976) state Hutchings' theorem as "any of the prime numbers 5, 7, 11, 13, … wins as a first move", with exactly this strategy-stealing proof using the Frobenius number — matching the submission. (2) Numerics: I implemented the game with the correct a-priori bound (legal moves from any descendant of `{p,q}` are gaps of `⟨p,q⟩`, all `≤ t`) and solved the finite game trees by memoized backward induction: the player to move from `{5,q}` wins for every tested coprime reply `q ∈ {2,3,4,6,7,8,9,11,12,13,14,16,17,19}`, confirming that no winning response for the second player exists after the opening 5 — i.e. `five_wins` is true in the real game, not an artifact of the formalization. As a control, openings 2, 3, 4 come out losing for the first player, as known.

Build hygiene: zero errors/warnings; axiom profile is the allowed minimum, replayed independently. The report's proof mirrors the Lean development lemma for lemma and cites the literature correctly.

## Issues found

- Minor: two entries of `verification/SHA256SUMS.txt` hash CRLF newline variants of `conjecture.md` and `lean/Conjecture1213/Basic.lean` (verified by re-hashing after newline normalization). Non-blocking hygiene issue.

## Verdict

APPROVED. The disproof is the genuine Hutchings theorem, formalized from first principles with a faithful game formalization, cleanly built, axiom-clean, independently confirmed against the published literature and by my own game-tree computation; the conjecture's clauses 2 and 3 (in both phrasings) are false because the prime 5 is a winning first move, while clause 1 is true.
