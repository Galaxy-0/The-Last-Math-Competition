# Verification record

The root agent read the complete Lean source and independently compiled
the published project on 2026-10-06 using `lake build`. Lean 4.33.1 and
Mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474` are pinned.

The two printed terminal theorem audits, `evalues_card` and
`raw_evalue_count_disagrees_with_formula`, contain only
`[propext, Classical.choice, Quot.sound]`. The project has no unfinished
proofs, native evaluation, custom axioms, or long brute-force search.

The semantic scope is explicitly raw scalar E-eigenvalues, not
equivalence classes modulo sign. The primary definition and odd-order
pair-count distinction were checked in Sodomaco's arXiv:1802.10173,
Definition 1.1 and Theorem 1.3. The formalization proves the exact actual
E-eigenvalue set; it does not claim a formal resultant-degree theorem.

The LaTeX source compiles with Tectonic and the desktop compiler, and
the exported PDF is rendered and visually checked before publication.
