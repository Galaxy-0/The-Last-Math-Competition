# Validation

The final full lake build succeeds, including Main. Nine printed axiom audits cover occurrence count, nontrivial equations, unification, universal variable factorization, most-generality, idempotence, both depths, support count and the complete counterexample. Only standard propext/Classical.choice/Quot.sound occur; no added axioms or sorryAx.

Counts and depth values use kernel-checked decide on actual finite sets and recursively defined terms. Most-generality is proved by arbitrary-unifier reasoning and term induction, not finite enumeration or an assumed certificate.

Tectonic compiled report.tex into a two-page report.pdf (36,601 bytes). Both rendered pages were visually checked with no clipping, overlap or box warnings. The built-in editor/compiler was attempted; its platform-directory failure was handled using the existing Tectonic compiler.

All text is UTF-8 LF, the scoped diff check passes, and public pins permit reproduction without local junctions. No shared cache extension was needed.
