# Disproof of conjecture 00000008413

At the prime-power parameter n=2, Singer parameters are (7,3,1). Every ambient group therefore has order 7 and is cyclic. No noncyclic abelian group can realize these parameters, contradicting the source's prime-power sufficiency assertion. A separate actual DihedralGroup cardinality theorem also excludes the named dihedral order 21 exception.

The complete argument is in report.tex and the two-page report.pdf. lean/Main.lean defines the standard perfect difference-set conditions using actual ambient group cardinality, block cardinality and unique ordered differences. The final theorem negates existential realization over all abelian ambient group types/structures, alongside a verified prime-power 2 witness. Nonexistence follows from a necessary ambient-group condition; no blocks need to be enumerated in a nonexistent ambient class. No result about the cyclic perfect-difference-set prime-power classification is asserted.

## Reproduction

With Lean 4.19.0 installed, from lean/ run:

```text
lake update
lake exe cache get
lake build
lake env lean Main.lean -DwarningAsError=true
```

Mathlib is pinned at c44e0c8ee63ca166450922a373c7409c5d26b00b; public manifest dependencies are pinned Git revisions. Local .lake build/cache junctions are ignored. Compile report.tex with Tectonic or a standard LaTeX engine. No executable auxiliary computation is required.
