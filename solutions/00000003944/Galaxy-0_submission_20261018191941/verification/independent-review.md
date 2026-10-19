# Independent semantic verification of Conjecture 00000003944 submission

Reviewed on October 18, 2026.

## Scope and conclusion

The counterexample is valid for the printed unrestricted statement: maximum degree has its usual graph-theoretic meaning, the palette is fixed at three labelled colours, a Kempe switch flips a complete bichromatic connected component, and the target is uniform on all proper colourings. The source states no large-palette assumption. The submission appropriately makes no claim about a modified conjecture imposing such an assumption or about mixing within an individual Kempe class.

The connected triangular prism with two leaves has maximum degree exactly five. Its 48 proper colourings split into two invariant events of size 24, distinguished by equality of the colours at vertices 0 and 4. Each bichromatic subgraph of the prism is a connected four-vertex path. A complete switch therefore either misses the prism or acts on its colouring by a global transposition, preserving that equality. This verifies the essential graph-theoretic obstruction independently of the finite computation.

Starting outside the event, any supported Markov evolution assigns it probability zero at every time, whereas uniform assigns it probability one half. Consequently total variation is at least one half and never reaches the standard one-quarter threshold. The report also gives a concrete uniform pair-and-seed chain whose symmetry and stochasticity make uniform stationary. Its claim is thus stronger and more precise than mere disconnectedness.

The final report extends one pendant leaf by a path to produce every order n ≥ 8 with maximum degree five. Its count 12·2^(n−6), half-event, and preserved invariant are correct. This excludes a finite-exception reading of asymptotic notation. The report explicitly distinguishes this mathematical extension from the formally verified eight-vertex instance.

## Lean correspondence

The entire Lean source was inspected. It defines the actual eight-vertex graph, proper colourings, inductive paths in bichromatic induced subgraphs, and a switch on exactly the reachable component. A kernel-checked finite lemma establishes invariance for eligible adjacency-closed subsets, and actual components are proved to satisfy this stronger condition. Partial paths are not substituted for full components.

The base-three encoding is proved surjective onto assignments and injective. Filtering all codes therefore enumerates actual colourings; the formal counts are 48 states and 24 event members. The finite matrix recurrence starts at a verified proper colouring outside the event. `event_gap` proves discrepancy exactly 1/2 at every time, and `counterexample` includes connectedness, maximum degree five, and failure of the event-based total-variation threshold for every supported rational stochastic kernel.

The formal probability scope is rational kernels. This includes the concrete chain's finite uniform random choices. The report states this boundary accurately; its elementary human proof also covers real probabilities. The particular 24-choice transition matrix and the unbounded-order graph family are not constructed as separate Lean objects. Neither omission invalidates the stated formal counterexample or the mathematical argument.

## Verification performed

- Read the full source conjecture, Lean code, LaTeX report, and reproduction instructions.
- Visually inspected all three PDF pages, and rerendered the final PDF after the unbounded-order paragraph was added; no clipping or layout defect was found.
- Independently executed `independent.py`. It verified the degree sequence, 48 proper colourings, two components of size 24, 240 directed legal transitions, and exact rational symmetry, stochasticity, uniform stationarity, and invariant support for the concrete chain.
- Reviewed the successful clean serial `VERIFY.sh` log: `lake build`, the axiom audit, `leanchecker Conjecture3944`, `leanchecker Audit`, and Python enumeration all passed. The audited dependencies are only `propext`, `Classical.choice`, and `Quot.sound`.

An additional independent direct compilation was terminated by the operating system during overlapping resource-intensive checks; it produced no Lean error. An additional checker session returned status zero, but because an interruption request was sent at its conclusion, this review relies on the completed clean serial verification log for the uninterrupted build/checker result. This resource limitation does not affect the independent source, mathematical, PDF, and Python reviews.

## Final reviewed artifact hashes (SHA-256)

- Source conjecture text: `336df81bebfa5d936cdd2ebf6c9e7df719754e67f55173262704da0276eb6645`
- Packaged `source.md` (same conjecture text with different terminal whitespace): `084412f9fce877afcc3df79fc4bbebefb7726804c170b2c40aca1f696b2934c6`
- `Conjecture3944.lean`: `0d150687961c3fd32d411108f9100f07caaba3b834ef31e6bab7691b2dafe98a`
- `main.tex`: `c6c3844d0563858c16c9a77efe35d2b425effe1b7578436c7f6333e3fcaeefbf`
- `main.pdf`: `c47ff9eceba38670539d63fd03820a5ce6b043848237c77684393f1a499cd7ef`

The submission passes semantic and report correspondence review. This verification is not an assertion of acceptance by competition maintainers.
