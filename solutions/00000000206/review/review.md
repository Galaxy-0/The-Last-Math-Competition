# Solution Review — Conjecture 00000000206 (PR 666)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005092350`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- Conjecture read in full from `conjectures/00000000206.md` (bilingual); shipped `conjecture.md` is byte-identical (`diff` clean). Extraction matches the PR tree file-for-file and hash-for-hash (15 files).
- LaTeX rebuilt independently with `latexmk -pdf` in a scratch dir; shipped and rebuilt PDFs compared by extracted text (pypdf, whitespace-normalized) and by rendered page images. Content identical; differences are cosmetic extraction artifacts only (the precomposed `á` of "Recamán" extracts as `´a` in one build, and line breaks shift by a word).
- `lake build` in the submitted `lean/` project: success, 8708 jobs, zero errors, zero warnings. Toolchain Lean 4.33.1, Mathlib v4.33.1 rev 0df444a360 (prebuilt pool).
- Cheating scan clean: no `sorry`, `admit`, `native_decide`, `implemented_by`, `extern`, `unsafe`, or declared `axiom`. Independent scratch `Check.lean` with `#print axioms` for every decisive theorem (`recaman_finite_occurrences`, `finite_occurrences_of_isRecaman`, `finite_occurrences_of_isRecamanOEIS`, `isRecaman_recaman`, `isRecamanOEIS_recaman`, `isRecaman_unique`): only `propext`, `Classical.choice`, `Quot.sound` (two of the six need only `propext`, `Quot.sound`).
- Aux code: `verification/axioms.txt` and `verification/build.txt` reproduce exactly under my independent run. Minor blemish (non-blocking): `verification/SHA256SUMS.txt` is stale for `conjecture.md` and `lean/Conjecture206/Basic.lean` — the shipped files themselves are correct (they match the PR git tree, and `conjecture.md` is byte-identical to the official), only the checksum manifest was not regenerated after the final edit.
- Metadata: `metadata.csv` lists 00000000206 as `proven=false, disproven=false` at submission time; no competing solution on main.

## Semantic audit

The conjecture says: the Recamán sequence (defined by the backtracking-doubling recurrence) has every nonnegative integer occur only finitely often, "and the finiteness is settled by interval covering". The submission defines the sequence faithfully: `IsRecaman` formalizes the Wikipedia guard (`a (n+1) = a n - (n+1)` if positive and new), `IsRecamanOEIS` the OEIS guard (`≥ 0`); it proves the constructed `recaman` satisfies both (the `≥ 0` guard can only trigger the subtract branch to produce `0`, which is always already present) and that the recurrence determines the sequence uniquely. Crucially, it pins the construction to the actual A005132 by a `decide` check of the first 27 terms including the first repeat (`a 20 = a 24 = 42`), so this is the conjecture's own object, not a surrogate.

The decisive theorem is exactly the conjecture's first clause: `recaman_finite_occurrences (m : ℕ) : {n | recaman n = m}.Finite`, for every `m`, for every sequence satisfying either guard form (a strengthening, which is safe). The core lemma `finite_of_step` assumes only that each step is either an add step or produces a fresh value — both branches of the recurrence satisfy this. The argument: if `a n = m` with `n > m`, the step into `n` cannot be an add step (which forces `a n ≥ n > m`), so it is fresh, i.e. `n` is the first occurrence of `m`; hence at most one occurrence lies beyond index `m`, and the remaining occurrences lie in the finite initial segment `[0, m]` (or `[0, N]` for the first far occurrence). This is literally an interval covering of ℕ by two initial segments, so the proof also embodies the conjecture's second clause; that clause names no mathematical object ("interval covering" is undefined in the source), and reading it as a remark on method is the only coherent reading. The mathematics is elementary and correct: I verified numerically over 200 000 terms that the sequence matches the submitted term list and that no value ever occurs twice at an index beyond its own value.

Faithfulness concerns do not arise: no deep theorem is assumed (the whole file is self-contained from `import Mathlib`), no toy instance is substituted (the theorem is about the constructed Recamán sequence itself), and the quantifier structure (`∀ m, finite`) matches the bilingual source exactly.

## Issues found

None blocking. (Verification-only: `verification/SHA256SUMS.txt` records stale hashes for `conjecture.md` and `lean/Conjecture206/Basic.lean`; the shipped files match the PR tree and the official conjecture copy, so only the manifest is out of date.)

## Verdict

APPROVED. The submission formalizes the genuine Recamán sequence, proves exactly the stated finite-occurrence claim with a stronger-than-required generality (both guard forms, recurrence uniqueness), checks the construction against the published terms, builds cleanly from scratch, and passes the axiom and cheating audits with only the standard three axioms. The one flaw found — a stale checksum manifest in `verification/` — does not affect any artifact of the proof.
