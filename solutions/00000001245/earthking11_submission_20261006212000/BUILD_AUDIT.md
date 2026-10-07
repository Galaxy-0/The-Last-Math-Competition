# Verification record

Verified locally on 2026-10-06 with Lean 4.33.1 and the pinned Mathlib revision.

The root reviewer read the full Lean source and independently ran `lake build`
from this project's own `.lake` build directory. Result: success (3007 jobs;
dependencies largely reused, Main built in 2.6 seconds).

The following printed axiom audits all report only
`[propext, Classical.choice, Quot.sound]`:

- `TLMC1245.localOutput_rule255`
- `TLMC1245.rule255_falseWord1_goe`
- `TLMC1245.rule255_zero_is_minimum`
- `TLMC1245.infimum_minimum_densities_eq_zero`
- `TLMC1245.conjectured_value_ne_actual_infimum`
- `TLMC1245.rule133_falseWord2_has_preimage`

There is no unfinished proof, native evaluation, or custom axiom in the
submitted Lean source. Finite kernel reduction covers only the eight local
neighborhoods and the concrete rule-133 patch; there is no long brute-force
computation.

`solution.tex` was exported using Tectonic. The PDF is checked by PDF metadata,
text extraction, and rendered-page visual inspection before publication.
