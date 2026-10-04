# Solution Review — Conjecture 00000006825 (PR 360)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261003215646`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — "Lat A (invariant subspaces of A) is a complete lattice, the lattice order being the standard (inclusion) order."
- LaTeX: compiled twice with pdflatex, exit 0; shipped main.pdf is a real 1-page PDF whose extracted text matches the tex (only big-operator glyph rendering differs between the shipped engine and local TeX Live 2022 — same math).
- Lean build: fresh `rm -rf .lake && lake build`, exit 0, zero warnings (lakefile sets `warningAsError = true`), Lean 4.19.0, `Std` only.
- Forbidden content: none — grep for sorry/admit/native_decide/axiom decls/unsafe/implemented_by/extern/skipKernelTC over lean/*.lean found nothing; `#print axioms conjecture6825` = [propext, Quot.sound].
- Auxiliary code: no Python/JS shipped; none required (pure lattice-theoretic proof). VALIDATION.json hashes present; SOURCE.md and conjecture.md byte-identical to official conjectures/00000006825.md.
## Semantic audit
Conjecture (bilingual): "不变子空间的格：Lat A … 不变格的完全格且格的组合为标准序 (standard-order lattice completeness of Lat A)". The submission reads this as: the poset of A-invariant subspaces under inclusion is a complete lattice, and discloses this reading (README "Scope", tex "Meaning of the source"). Completeness-as-total-order is explicitly disclaimed, correctly.

Lean encodes the actual objects: `InvariantSubspace T O A` bundles `carrier : X → Prop` with `isClosed` (topology closed), `zero_mem`, `add_mem`, `smul_mem` under the actual operations, and `invariant : ∀ x, carrier x → carrier (A x)`. The standard order is genuine inclusion: `def Included U V := ∀ x, U.carrier x → V.carrier x`. The final theorem is

`theorem conjecture6825 (T : ClosedTopology X) (O : LinearOperations K X) (A : X → X) : IsCompleteLattice (T := T) (O := O) (A := A)`

where `IsCompleteLattice` conjoins the three partial-order axioms for `Included` with, for EVERY family `F : InvariantSubspace T O A → Prop` (arbitrary, including empty/uncountable), both universal properties of the meet `intersection F` and of the join `join F` (defined as the intersection of all upper bounds; `whole_is_upper` shows the upper-bound family is nonempty). `empty_intersection_is_whole` confirms the empty meet is the top.

Hypotheses are weakened, not strengthened: `LinearOperations` assumes NO vector-space laws and `A` need not be linear or continuous, so every real/complex topological vector space with any linear operator is an instance — this is a strict generalization of the conjecture's setting, hence the conjecture is established, not a proxy. `discreteTopology` covers the algebraic (no-closedness) convention. Not vacuous: `whole` inhabits the type, and `concrete_consistency_example` instantiates the theorem at `Int` with `A n = 2 * n` (a sanity instance, not a restriction — the general theorem `conjecture6825 _ _ _` is stated for arbitrary `T, O, A`). The meet's closedness proof converts the family of subspaces into a family of subsets and proves predicate equality before applying `intersection_closed`, so the topology axiom is applied to the actual intersection. This engages the conjecture's objects directly (contrast with rejected PRs #286–288 where objects were absent).
## Issues found
none blocking
## Verdict rationale
The Lean project cleanly establishes exactly the conjectured statement — Lat A under inclusion is a complete lattice with arbitrary meets (intersections) and joins (intersections of upper bounds) — under hypotheses strictly weaker than the conjecture's setting, so nothing is quietly strengthened. Builds fresh with zero warnings, only standard logical axioms, faithful bilingual source reproduction, and a compiling, matching LaTeX/PDF report. The one interpretation call (complete lattice ≠ total order; "standard order" = inclusion) is both mathematically standard and explicitly disclosed by the author.

## Disposition
APPROVED — merged into main (PR 360). Independent fresh rebuild of the Lean project (exit 0, warnings-as-errors where set, only standard foundational axioms), LaTeX recompilation, auxiliary-script re-runs, and a semantic audit confirming the Lean theorem establishes or refutes the conjecture as stated in both language versions.
