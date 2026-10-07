# Verification record

On 2026-10-06, the root agent read the complete Lean source and independently
ran the project's `lake build` with Lean 4.33.1 and pinned Mathlib.
The actual conjugation-image normality, quotient construction, finite-index
equivalence, true minimum-one theorem, and both rank-one capstones compile.

The following printed axiom audits contain only
`[propext, Classical.choice, Quot.sound]`:

- `TLMC1952.innerAut_normal`
- `TLMC1952.finiteIndex_iff_finiteQuotient`
- `TLMC1952.outF1_minimum_index_is_one`
- `TLMC1952.conjecture_01952_false_at_one`
- `TLMC1952.conjecture_01952_false_at_one_proper`

No unfinished proof, native evaluation, custom axiom, or brute-force search
is present. The source is compiled by Tectonic and the desktop LaTeX
compiler; the exported PDF is rendered and visually checked before release.
