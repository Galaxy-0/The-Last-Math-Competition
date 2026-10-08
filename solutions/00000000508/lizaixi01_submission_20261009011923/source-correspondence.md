# Source correspondence: 00000000508

Exact assigned source: `original.md`. Independently checked SHA256:
`1066988073f5e8125e865edccdd81c0b53ae2b0a15753331a0e50cd70eeb21bc`.
The English and Chinese statements have the same numerical notation and
antichain conclusion. Neither specifies the position order explicitly.

| Source role | Exact Lean object or theorem | Correspondence |
|---|---|---|
| Graded Betti number `β_{k,k+d}` | `β : ℕ → ℤ → ℕ`; entry `β k ((k : ℤ) + d)` | Homological degree is natural, total and shifted degree are signed integers, Betti values are natural multiplicities. No conjectured property is imposed on the table. |
| Extremal Betti number | `TLMC508.RawExtremal` | Exactly the BCP99 nonzero condition and all three vanishing-region inequalities. Extremality is not defined to mean antichain. |
| Standard diagram position `(k,d)` | `ℕ × ℤ`, usual product `≤` | Comparison means both `k ≤ l` and `d ≤ u`. This differs from comparing raw indices `(k,k+d)`. |
| Nonzero support in that diagram | `TLMC508.ShiftedSupport` | Entry is nonzero at total degree `k+d`; no finite-support assumption is needed. |
| Positions of extremal numbers | `TLMC508.ExtremalPositions` | The set consists of points satisfying the original raw definition after the signed shift. |
| Main antichain conclusion | `TLMC508.extremal_positions_antichain` and `TLMC508.exact_raw_definition_antichain` | Unconditional for every numerical table. Distinct extremal positions cannot be comparable. |
| Definitional bridge | `TLMC508.rawExtremal_iff_maximal_shiftedSupport` | Both directions are proved, with integer total-degree arithmetic and a support point `(l,r-l)` in the reverse direction. No bridge is a hypothesis. |
| Structural consequence | `TLMC508.distinct_extremal_corners_incomparable`; `TLMC508.shifted_degree_strictly_decreases` | Explicit pairwise incomparability; increasing homological degree strictly lowers shifted degree. Multiple corners remain possible. |

## Why every actual monomial ideal is covered

A standard graded minimal free resolution has numerical multiplicities
`β_{k,j}` in its free summands. These give a function of the above type.
The proved theorem holds for every function of that type, without any
condition on its origin. Applying it to such multiplicities requires no
theorem that their support has a special property. In particular, the
package never assumes a module-to-array antichain bridge or substitutes
a fabricated table for the table of a particular ideal. The conclusion
is wholly numerical and depends only on the exact definition of
extremality, so construction of graded Tor is unnecessary.

The theorem's generality also covers zero tables and infinite support,
but neither is a hypothesis used to make the ideal case vacuous. It
proves the full implication for every nonzero extremal entry.

## Exact standard definition and coordinate audit

Primary source: [Bayer–Charalambous–Popescu, *Extremal Betti Numbers and
Applications to Monomial Ideals*, introduction, p. 1](https://www.math.columbia.edu/~bayer/papers/Betti_BCP99/Betti_BCP99.pdf).
For the nonzero raw entry at `(i,j)`, the definition requires vanishing
at every `(l,r)` satisfying `l ≥ i`, `r ≥ j+1`, and
`r-l ≥ j-i`. The primary article also describes corners as `(l,m)`
corresponding to `β_{l,m+l}`. This supports the standard shifted
interpretation of the source's explicit `β_{k,k+d}` notation.

The source text alone does not spell out product order. Therefore the
scope is stated openly: the proof establishes antichain of `(k,d)`
diagram positions. It does not establish raw-index antichain of
`(k,j)`. The checked table with only `β_{0,2}=β_{1,2}=1` nonzero has
raw comparable positions `(0,2) ≤ (1,2)` and shifted incomparable
positions `(0,2)` and `(1,1)`. This is a numerical diagnostic, **not**
an alleged ideal or an actual monomial-ideal counterexample. Independent
semantic review must decide whether the standard diagram reading fully
matches the conjecture; the worker does not self-accept this choice.

## Mathematical and Lean correspondence

`proof.tex` Lemma 1 corresponds to the two directions of
`rawExtremal_iff_maximal_shiftedSupport`. The forward proof uses that a
distinct dominating integer point has strictly larger total degree.
The reverse proof maps a nonzero raw entry `(l,r)` to shifted point
`(l,r-l)` and contradicts the required larger total degree after
maximality forces equality. The set-level correspondence is an explicit
Lean theorem. Theorem 2 is the actual antichain conclusion, obtained
from Mathlib's `setOfPred_maximal_antichain`. Corollary 3 is
`shifted_degree_strictly_decreases`.

All declarations compile locally with the task's pinned Lean/Mathlib.
The independent `Audit.lean` records their actual types and reports only
the standard axioms `propext` and `Quot.sound`. There is no `sorryAx`,
custom axiom, native decision oracle, key bridge premise, or weakened
extremality region. The semantic files and logs are frozen for the
manager's independent build/audit. PDF rendering and acceptance are
deliberately left to the manager as required by this task.
