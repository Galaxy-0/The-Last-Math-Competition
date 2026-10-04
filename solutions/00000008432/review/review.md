# Solution Review — Conjecture 00000008432 (PR 363)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261003215646`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — "The hypergraph rank of the configuration formed by supports of minimal-weight codewords is t+1 for a design; the rank is determined by generalized Hamming weights; and single-valuedness of minimal weights is complete on MDS codes."
- LaTeX: recompiled twice with pdflatex, exit 0; shipped main.pdf is a real PDF matching the tex.
- Lean build: fresh `rm -rf .lake && lake build`, exit 0, zero warnings (`-DwarningAsError=true`), Lean 4.19.0, `Std` only; build took ~2 min due to kernel-checked `decide` (legitimate; no `native_decide` anywhere).
- Forbidden content: none — no sorry/admit/native_decide/axiom declarations/unsafe/implemented_by/extern/skipKernelTC. `#print axioms conjecture8432_counterexample` = [propext, Classical.choice, Quot.sound].
- Auxiliary code: no Python/JS shipped. Independently re-derived in python3 the FULL design computation: columns 1..7 in binary = all nonzero triples of F_2^3; 8 distinct codewords (encoder injective); all 7 nonzero codewords have weight exactly 4; 7 distinct blocks of size 4; every 2-subset of points lies in exactly 2 blocks (2-(7,4,2)); triple counts {0,1,2}→0 and {0,1,3}→1 (so not a 3-design; t = 2 exactly); hypergraph rank (max edge size) = 4 ≠ 3 = t+1. Every Lean claim matched.
## Semantic audit
Conjecture clause 1 (literal): "极小权码字的支撑形成的组合构形的超图秩为设计的 t+1" — the hypergraph rank of the support configuration equals t+1 [when it is a t-design]. The submission takes the standard hypergraph-theoretic definition of rank = maximum cardinality of an edge (Berge), disclosed in main.tex. Note that under this definition the rank of a support configuration of minimum-weight codewords is always the minimum distance d, so the conjecture asserts d = t+1 for support t-designs — a genuinely restrictive claim, refuted by a classical object: the binary [7,3,4] simplex code.

Lean encodes the actual objects concretely and faithfully: coordinates are the seven nonzero vectors of F_2^3 via `dot u i` with column i = binary of i+1 (verified by me to be all seven nonzero triples); `word u = encode (dot u)` is the codeword c(u) = (u·v)_v; `Code w := ∃ u, word u = w`; `MinimumSupport w := Code w ∧ 0 < weight w ∧ ∀ v, Code v → 0 < weight v → weight w ≤ weight v` is the honest minimum-weight predicate. Bridges are proved, not assumed: `encodeBits_correct`/`every_binary_word_encoded` (bit encoding surjective onto every predicate on 7 coordinates), `bit_injective`, `vector_space_coordinate_bridge` (wadd/wscale ARE the coordinate F_2 operations), `encoder_is_injective`, `encoder_is_linear`, `code_is_linear`. The design facts: `codeword_weights : ∀ u, weight (word u) = if u = 0 then 0 else 4`, `blocks_are_distinct`, `number_of_blocks : blocks.length = 7`, `all_pairs_have_lambda_two : ∀ i j, i ≠ j → pairCount i j = 2`, and `strength_is_not_three : tripleCount 0 1 2 = 0 ∧ tripleCount 0 1 3 = 1` (I verified the count 0 is for the dependent triple {1,2,3} = {e1,e2,e1+e2} and 1 for the independent {1,2,4} — the design has exactly strength 2, not an arbitrarily weakened t). The rank:

`def HypergraphRank (r : Nat) : Prop := (∀ w, MinimumSupport w → weight w ≤ r) ∧ ∃ w, MinimumSupport w ∧ weight w = r`

`theorem exact_rank : HypergraphRank 4`, `theorem rank_is_not_t_plus_one : ¬ HypergraphRank (2+1)`, bundled in

`theorem conjecture8432_counterexample : (Code 0 ∧ …linearity…) ∧ blocks.Nodup ∧ blocks.length = 7 ∧ (∀ w, MinimumSupport w → weight w = 4) ∧ (∀ i j, i ≠ j → pairCount i j = 2) ∧ HypergraphRank 4 ∧ ¬ HypergraphRank (2+1)`

This is exactly the conjecture's hypothesis (a code, its minimum-support configuration forming a 2-design) together with the failed conclusion (rank 4 ≠ t+1 = 3). All instances of "for a design" readings in which t is the design strength are refuted, since the strength is certified to be exactly 2. The remaining two conjuncts (GHW determination, MDS completeness) are untouched, correctly, since the conjunction already fails. Not vacuous: hypotheses and failed conclusion coexist in one concrete kernel-checked code. `all_genuine_supports` further connects the Lean word-representation to arbitrary predicates S on coordinates, so the supports are the actual set-theoretic support configuration.
## Issues found
none blocking
- Disclosed interpretation call: "hypergraph rank" read as maximum edge cardinality (the standard definition; the conjecture itself supplies no other). Under this reading the refutation is decisive; no reading in which t is the design strength survives this witness.
## Verdict rationale
The [7,3,4] simplex code is a genuine, classical counterexample to the rank assertion: minimum supports form a certified 2-(7,4,2) design of exact strength 2 with hypergraph rank 4 ≠ 3, and I reproduced every incidence count independently in Python with exact agreement. The Lean formalization builds the real code with proved encoding/addition bridges and kernel-checked (not oracle-checked) finite facts, compiles fresh with zero warnings, and the report matches. The conjunction refutation logic is sound.

## Disposition
APPROVED — merged into main (PR 363). Independent fresh rebuild of the Lean project (exit 0, warnings-as-errors where set, only standard foundational axioms), LaTeX recompilation, auxiliary-script re-runs, and a semantic audit confirming the Lean theorem establishes or refutes the conjecture as stated in both language versions.
