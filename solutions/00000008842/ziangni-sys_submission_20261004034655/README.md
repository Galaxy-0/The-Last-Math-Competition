# Proof of conjecture 00000008842

Proves that the domain of a maximal monotone operator is dense in its own closure and its graph is closed in the product norm topology.

The formalization covers arbitrary real normed spaces with continuous-dual-valued operators, including Banach spaces, and separately covers real inner-product-space operators, including Hilbert spaces. It also proves a general topological theorem for maximal compatible sets with closed relation sections.

The density clause is the actual DenseRange of the canonical inclusion from the domain subtype into the closure subtype. Maximality is defined by absence of a proper monotone graph extension; closedness is proved, not assumed.

## Reproduction

Lean 4.19.0 with pinned Mathlib:

    cd lean
    lake update
    lake exe cache get Mathlib/Analysis/InnerProductSpace/Continuous.lean Mathlib/Topology/Constructions.lean
    lake build
    lake env lean Main.lean

Compile report.tex with Tectonic. See VERIFICATION.md.
