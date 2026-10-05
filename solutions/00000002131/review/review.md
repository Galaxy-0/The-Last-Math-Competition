# Solution Review — Conjecture 00000002131 (PR 613)

**Submission:** C0ldSmi1e — `C0ldSmi1e_submission_20261005064103`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-05

## Verification

The official bilingual conjecture, complete LaTeX report, both PDF pages, both Lean source files, configuration, auxiliary programs, and audit artifacts were read. Only the declared submission folder was added. Base metadata marks 00000002131 unsolved, no prior solution existed, and the included conjecture text is byte-identical to the official source. All 40 checksum-manifest entries independently match.

The PDF was independently rebuilt twice with `pdflatex` (exit 0) and the supplied exporter was replayed with Tectonic (exit 0, no diagnostics). Submitted and rebuilt PDFs have two pages and semantically identical extracted text. The Lean 4.19.0/Mathlib `c44e0c8e…` project was linked to the prescribed shared dependencies and independently built; `lake build`, strict warning-as-error replay of the source and `Check.lean`, the environment inventory, and the author audit all exited 0. All 28 audited theorems use only `propext`, `Classical.choice`, and `Quot.sound`. Complete environment enumeration covered 55 originating constants: all 40 authored declarations plus generated declarations. There are no authored unsafe/partial/axiom declarations or unexpected unsafe constants; seven compiler-generated `_cstage` runtime artifacts were explicitly distinguished and audited. The independent Python verifier and exporter were also replayed successfully.

## Disproof

The source imposes no length-at-least-two restriction. Let `u` be the one-element permutation. Every positive-size permutation contains `u`, so its avoidance count is identically zero and its genuine Stanley–Wilf limit is zero. The direct sum `u⊕u` is the increasing two-element permutation `v`. Avoiding `v` is equivalent to being strictly decreasing, so exactly one permutation of every size avoids `v`; its genuine limit is one. The claimed multiplicativity at `u,u` would require `1=L(u⊕u)=L(u)L(u)=0`, which is false.

Lean formalizes actual finite permutations, classical order-pattern containment, full avoidance cardinalities, the standard block direct sum, positive-index real roots, and genuine `Tendsto` limits. `nonmultiplicative_witness` proves all three required limits and the inequality, so the refutation is non-vacuous. `not_universalMultiplicativity` negates the exact universal displayed assertion, and `not_source_conjunction` validly handles the unspecified additional characterization clause without inventing its content.

**Disposition: APPROVED.**
