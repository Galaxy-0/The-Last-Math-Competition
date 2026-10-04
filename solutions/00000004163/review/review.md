# Solution Review — Conjecture 00000004163 (PR 458)

**Submission:** feiyuceng06-prog — `feiyuceng06-prog_submission_20261004045051`
**Reviewer:** independent competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — the seven-prime-cube local obstruction table modulo 9 is claimed to contain exactly three classes.
- Change scope: only the allowed submission directory was added; base metadata marked the problem unsolved and no prior solution existed.
- LaTeX: independently rebuilt with `latexmk -pdf -interaction=nonstopmode -halt-on-error` (exit 0; two pages). The source uses the full `import Mathlib` line in a paragraph, which produces three pdfTeX overfull-box notices (largest 20.28pt); the text remains inside the physical page and shipped/fresh text is exactly equal after Unicode/font normalization and whitespace removal. Both shipped pages were split and rasterized.
- Lean build: Lean 4.33.1 / Lake 5.0.0-src, Mathlib v4.33.1 at exact revision `0df444a360eaa60ab8c11dca51a86af692955474`; official exact-revision artifacts were shared and this project's two source modules compiled independently. `lake build` exit 0 (`[8706/8708] Built Submission.Basic`, `[8707/8708] Built Submission`, build completed). Direct `lake env lean -DwarningAsError=true Submission/Basic.lean` exit 0; the final theorem depends only on `[propext, Classical.choice, Quot.sound]`.
- Forbidden content: no executable `sorry`, `admit`, `native_decide`, axiom declaration, `unsafe`, `implemented_by`, `extern`, or `skipKernelTC`; the broad scan hit only prose in the report.
- Auxiliary code: none is supplied. I independently checked all nine explicit prime tuples and cube-sum residues in Python; primality and every modulo-9 value passed.
## Semantic audit
The formal `primeCubeSum` adds exactly seven natural-number cubes indexed by `Fin 7`. `RepresentedBySevenPrimeCubes r` requires an actual tuple, primality of every entry, and equality modulo 9, so it is the literal local-representation predicate and is non-vacuous.

Since \(19^3\equiv1\), \(3^3\equiv0\), and \(2^3\equiv8\pmod9\), residue \(r=0,\dots,7\) is represented by \(r\) copies of 19 and \(7-r\) copies of 3; residue 8 is represented by one 2 and six 3s. Each tuple has exactly seven prime summands. Lean checks primality and all residue equalities by finite case analysis, then proves every \(r\in Fin\,9\) is represented.

`ClaimedThreeObstructions` states that three distinct residues are unrepresented and exactly those residues are unrepresented. Since `every_residue_represented` supplies a representation even for the first alleged residue, the contradiction is immediate and valid. Thus there are zero local obstruction classes modulo 9 for seven prime cubes, not three. The report correctly distinguishes this finite local statement from a global Waring–Goldbach representation theorem; the additional “adding one variable” clause need not be formalized once the shared exact-table assertion is false.
## Issues found
The pdfTeX rebuild reports three overfull boxes in the long Formalization paragraph. They are a minor layout issue, not mathematical or verification defects, and no text is clipped.
## Verdict rationale
The proof is elementary, complete, and exactly targeted. Every residue modulo 9 has a constructed seven-prime-cube representation, which decisively contradicts the conjecture's claim of three non-representable classes. The Lean and PDF builds pass, and only standard foundational axioms occur.

## Disposition
APPROVED — ready to merge (PR 458). Independent fresh rebuild, direct warning-as-error Lean check, axiom audit, PDF rebuild/comparison, source inspection, forbidden-pattern scan, independent residue/primality recomputation, and semantic audit all passed.
