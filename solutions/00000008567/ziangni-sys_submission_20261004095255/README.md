# Disproof of conjecture 00000008567

The unrestricted identity matrix cannot be paved to blocks of smaller norm. With epsilon=1/2, any row partition of I₂ has a block of norm at least 1, exceeding the required 1/4. The full Lean proof generalizes this obstruction to every positive dimension and covers both rectangular row restrictions and customary principal compressions.

Both original versions omit a zero-diagonal hypothesis. This disproves the stated unrestricted paving and hence its finite block-count bound; it is not a counterexample to the standard zero-diagonal Kadison–Singer theorem. The report explains this distinction explicitly.

The actual objects are Euclidean Hilbert spaces, orthonormal coordinate bases, identity matrices/maps, finite coordinate spans, continuous orthogonal projections, genuine row restrictions and principal compressions, finite disjoint covering partitions and actual continuous-linear-map operator norms. No block norms are supplied as presumed scalar data.

Read report.tex/report.pdf and lean/Main.lean. From lean/ with Lean 4.19.0:

```text
lake update
lake exe cache get
lake build
lake env lean -DwarningAsError=true Main.lean
```

The public Mathlib revision c44e0c8ee63ca166450922a373c7409c5d26b00b is pinned in Lake configuration. Ignored local dependency junctions are only validation convenience. No admitted facts, custom axioms or native decision procedures are used. Verification evidence and the original source are included.

The built-in LaTeX editor/compiler was attempted. Its existing platform-directory error was handled by successful Tectonic compilation; every final PDF page was rendered and visually inspected.
