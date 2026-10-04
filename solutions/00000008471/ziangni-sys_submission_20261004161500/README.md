# Disproof of 00000008471

On the compact singleton identity dynamical system every actual probability measure is Dirac. Every continuous observable therefore has exactly that invariant maximizing measure, the genuine equidistribution on the length-one periodic orbit. All observables are locked under the explicit source definition. Their complement is empty and is not dense in the nonempty continuous-function space, disproving the dense-open-complement conjunct.

Lean formalizes the full probability-measure classification, invariance, actual Bochner integral, quantified maximizing-measure set, weighted periodic-orbit measure, all-observable locking and actual Dense negation. The source does not exclude singleton systems. The report also explains perturbation persistence; no genericity claim needs to be refuted.

Reproduce with Lean 4.19.0 from lean/:

```text
lake update
lake exe cache get
lake build
```

Mathlib is pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b. Ignored local junctions reuse its cache. The full build prints six axiom audits. There are no admitted proofs, custom axioms or native decision procedures.

The complete report is disproof.tex/disproof.pdf. The built-in compiler was attempted and reported its platform-directory failure; existing Tectonic compiled the final one-page PDF, which was rendered and visually inspected.
