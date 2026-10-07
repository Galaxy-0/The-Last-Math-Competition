# Solution Review — Conjecture 00000002718 (PR 740)

**Submission:** Jackmeson1 — `solutions/00000002718/Jackmeson1_submission_20261005194232`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- **Official conjecture read in full** (English + Chinese) from `conjectures/00000002718.md`: "shellable implies d-collapsible but not conversely; the minimal separating complex is a special 2-complex, and the separation spectrum is a finite layer in dimension two". Shipped `conjecture.md` is **byte-identical** to the official file (`diff` clean).
- **LaTeX rebuild:** independent `latexmk -pdf` from the shipped `proof.tex` succeeds; pypdf comparison (normalized) shows identical content; differences are glyph-extraction artifacts only (∪/⊂/≤ extracted as control codes or alternates, underscore retention in identifier names) — cosmetic.
- **Lean build:** independent `lake build` (Lean `v4.33.1`, Mathlib v4.33.1, pool rev 0df444a360) — **Build completed successfully (8708 jobs), zero errors, zero warnings**, ~55 s.
- **Axioms:** `lake env lean Axioms.lean` prints only `[propext, Classical.choice, Quot.sound]` for `C2718.conjecture2718_false` and `C2718.counterexample`; matches `verification/axioms.txt`. Greps for `sorry`/`native_decide`/`admit`/`implemented_by`/`extern`/`unsafe`/declared `axiom` are clean (the only "axiom" hits are the `#print axioms` driver).
- **Aux code:** no computation scripts; `verification/build.txt` consistent with the independent rebuild; `SHA256SUMS.txt` — the single `conjecture.md` mismatch matches exactly after CRLF conversion (Windows hashing artifact); the other 13 entries verify as stored.
- **Metadata:** `metadata.csv` lists 00000002718 as unsolved; no solution folder for it on main. README eligibility accurate; README line count (237) matches the Lean file.

## Semantic audit

The conjecture is a conjunction whose first conjunct is the universal implication "every shellable d-dimensional complex is d-collapsible". The submission's decisive theorem `conjecture2718_false` is precisely the negation `¬ ∀ (n d : ℕ) (K : Finset (Finset (Fin n))), IsComplex K → IsPureOfDim K d → Shellable K → DCollapsible d K`, refuted at d = 2 by an explicit witness; refuting one conjunct refutes the conjunction, and the submission says so without overclaiming (the "not conversely", "minimal separating complex" and "separation spectrum" clauses are explicitly not addressed).

The formalization uses the conjecture's own objects with the standard definitions. Complexes are finite abstract simplicial complexes (`IsComplex`: subset-closed finite families); facets, purity of dimension d, free faces, Wegner's elementary d-collapse in Tancer's exact formulation (arXiv:0808.1991, quoted verbatim in the report: remove [σ, τ(σ)] where dim σ ≤ d−1 and τ(σ) is the unique maximal face containing σ), d-collapsibility = reflexive-transitive closure down to the empty complex, and shellability (ordering of the maximal faces, each once, with (⋃_{i<k}⟨C_i⟩) ∩ ⟨C_k⟩ nonempty and pure of dimension dim C_k − 1). These are the textbook notions; nothing is weakened to trivialize the claim.

The witness is the canonical one: T = boundary of the tetrahedron (all proper subsets of Fin 4, 15 faces), a pure 2-complex. The Lean proof shows T is shellable (order 012, 013, 023, 123 — I independently verified the three intersection complexes ⟨01⟩, ⟨02, 03⟩, ⟨12, 13, 23⟩ are each pure of dimension 1) and that no elementary 2-collapse can start: every face of cardinality ≤ 2 that is not a facet lies in at least two triangles (edges in 2, vertices in 3, ∅ in 4), so no dim ≤ 1 face has a unique maximal containing face (independently verified). The `stuck_of_no_free_face` lemma then gives that any reachable complex equals T, and T ≠ ∅, so T is not 2-collapsible — a ReflexTransGen argument, not a finite case check, so it covers arbitrary collapse sequences. This is mathematically correct and classical: Wegner's d-collapsible complexes are d-Leray, while the 2-sphere T has nonvanishing H̃₂, so T cannot be 2-collapsible; equivalently T simply has no free face at all. The robustness lemmas extend the obstruction to Whitehead simplicial and elementary collapses (so T is not collapsible to a point either), making the disproof independent of the exact reading of the gloss "matched contractions of d-faces".

Faithfulness gate: the counterexample is an actual shellable complex failing d-collapsibility in dimension two — exactly the regime the conjecture itself focuses on ("finite layer in dimension two"); no assumed theorem, no toy surrogate, and the negated universal statement has precisely the conjecture's hypotheses (complex, pure, shellable).

## Issues found

None blocking. Trivial notes: (i) the auxiliary `SimplicialCollapse`/`ElementaryCollapse` definitions adopt an "augmented convention" allowing the empty face as a free face (more permissive than homotopy-preserving Whitehead collapses); this is explicitly disclosed and immaterial since T has no free face of any dimension; (ii) SHA256SUMS CRLF artifact as above.

## Verdict

APPROVED. A faithful, machine-checked disproof of the conjecture's leading conjunct: the boundary of the tetrahedron is a pure, shellable 2-dimensional complex that is not 2-collapsible under Wegner's definition (nor under the usual collapse notions), so "shellable implies d-collapsible" is false and the conjecture as stated fails. Build clean, axioms minimal, report accurate and honest about scope.
