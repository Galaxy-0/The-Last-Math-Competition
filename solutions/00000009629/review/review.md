# Solution Review — Conjecture 00000009629 (PR 824)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261006171417`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- Conjecture read in full (bilingual) from `conjectures/00000009629.md`; shipped `conjecture.md` is byte-identical to it (`diff` clean).
- LaTeX: full `.tex` read; `latexmk -pdf -interaction=nonstopmode` rebuild in a scratch dir succeeds with 0 errors. Shipped vs rebuilt PDF text compared with pypdf: word-for-word identical; all differences are glyph-mapping extraction artifacts (≤, ∈, {, }, ×, ∅, ≠, −, ≥, ⊆, ∩, ⇒⇐ extracted with different mappings by the author's TeX) and math spacing. Cosmetic.
- Lean build: `lake build` from scratch against the prebuilt pool, 0 errors, 0 warnings (Lean 4.33.1, Mathlib v4.33.1, rev 0df444a360 pinned identically by `lake-manifest.json`).
- Axioms: `#print axioms` re-run independently for `counterexample`, `not_OEDimCriterion`, `conjecture_false`, `no_orbit_map`, `dimOrderIso_two_four` — all report exactly `propext, Classical.choice, Quot.sound`. Grep for cheating markers: only audit prose hits.
- Aux code: fresh `Axioms.lean` output matches the claims; all 14 entries of `verification/SHA256SUMS.txt` reproduce over the shipped files (the three "mismatches" are pure CRLF/LF artifacts; CRLF-normalized hashes match exactly).
- Metadata: `metadata.csv` lists 00000009629 as `proven=false, disproven=false` (unsolved); no competing solution folder.

## Semantic audit

The conjecture's first clause: two mixing SFTs are orbit equivalent if and only if their dimension groups are order-isomorphic. Its Definition line fixes orbit equivalence as an orbit-preserving Borel isomorphism; "dimension group" is Krieger's group of the presenting matrix, standardly G_A = {x ∈ R(A) : xA^k ∈ ℤ^r for some k ≥ 0} with cone G_A⁺ from (ℤ₊)^r (the eventual-range model; the literature reserves "dimension triple" for this data plus the shift automorphism δ_A, and the conjecture does not use that word).

The submission refutes the "if" direction with the full 2-shift X_[2] and full 4-shift X_[4] (edge shifts of the 1×1 matrices [2], [4]). Lean proves both are SFTs (`forbidden ∅`) and topologically mixing (explicit pasting using the product-topology characterization, with the index-separation bound n + j ∉ I from |n+j| ≥ n − |j| > M); proves `dimGroup (full 2) = dimGroup (full 4)` as literally equal `AddSubgroup`s of ℚ¹ — both {q : q·2^k ∈ ℤ for some k} = ℤ[1/2], since q·4^k = (q·2^k)·2^k and q·2^{2k} = q·4^k — with equal cones, so `DimOrderIso` holds via the identity; and proves `no_orbit_map`: any bijection mapping each orbit into an orbit is impossible, because φ⁻¹ sends fixed points to fixed points (a fixed configuration is a singleton orbit; the proof needs only orbit-inclusion), the fixed points of the full n-shift are the n constant configurations, and an injection from a 4-element set into a 2-element set is absurd. Hence the biconditional fails for this pair of mixing SFTs, and `conjecture_false` refutes the whole conjunction with the entropy and Kakutani–Rokhlin clauses abstracted — legitimate, since one false conjunct falsifies a conjunction.

The formalization is faithful. `OrbitEquivalent` is exactly the Definition line's notion (bijection, Borel measurable both ways for the subspace-topology Borel σ-algebras, images of orbits equal to orbits); `DimOrderIso` is ordered-group isomorphism (cone preserved in both directions), matching "order-isomorphic" (维数群有序同构). The witnesses are the canonical mixing SFTs, not toy surrogates, and they satisfy all stated hypotheses. The mathematics is airtight and I re-verified its two pillars independently: the fixed-point count is an orbit-equivalence invariant for any bijection preserving orbits set-wise (2 ≠ 4), and ℤ[1/2] = ℤ[1/4] with identical nonnegative cones (checked on 500 random rationals in both directions). The submission explicitly and honestly flags the readings it does not refute: "dimension groups" as the dimension triple (G, G⁺, δ_A) — under which ×2 and ×4 are not intertwined and this witness does not apply — and the Giordano–Putnam–Skau K⁰ group. The conjecture text says "dimension groups are order-isomorphic", which is the ordered-group statement refuted; that is the plain meaning of the words, so the disproof stands, with the alternative reading properly disclosed rather than silently exploited.

## Issues found

None blocking. Non-blocking notes:
- Shipped `verification/axioms.txt` lists three of the four theorems named in the report's audit paragraph (`no_orbit_map` is missing from the file); I audited it independently — clean, so the report's claim holds.
- `verification/SHA256SUMS.txt` was computed over CRLF versions of `conjecture.md`, `lean/Conjecture9629/Basic.lean` and `proof.tex`; shipped files are the LF archive renders, content otherwise byte-identical.
- If the community later reads "dimension groups" as dimension triples (with δ_A), this counterexample no longer applies; the submission's own "readings not refuted" section covers this. Under the text as written, the disproof is valid.

## Verdict

APPROVED. A complete, faithful, machine-checked disproof of the criterion as written: the full 2-shift and full 4-shift are mixing SFTs with identical (hence order-isomorphic) Krieger dimension groups that cannot be orbit equivalent, because orbit-preserving bijections must map the 4 fixed points of one into the 2 of the other. Build clean, axioms clean, LaTeX/PDF consistent, shipped conjecture copy verbatim, and the one interpretive caveat is disclosed in the submission itself.
