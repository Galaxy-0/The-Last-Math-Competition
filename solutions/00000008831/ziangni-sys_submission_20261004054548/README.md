# Disproof of conjecture 00000008831

On the genuine real Hilbert line, A(x)={0} and B(x)={1} are full-domain maximal monotone operators. At resolvent parameter one their reflected resolvents compose to x−2, while the conventional averaged DR map is x−1. Every orbit fails weak convergence.

The source has no zero-existence or feasibility hypothesis. The example explicitly has A(x)+B(x)={1}, with no zero. The submission refutes the unqualified convergence assertion and does not dispute convergence results with feasibility assumptions or assert results about the other conditional clauses.

Files: report.tex and report.pdf give the complete proof and correspondence; lean/Main.lean proves actual graph maximality, resolvent equations and uniqueness, reflections, both composition orders, averaging, every iterate and weak nonconvergence under continuous linear functional testing. verification/ preserves the original and validation evidence.

From lean/, with Lean 4.19.0 installed, run:

```text
lake update
lake exe cache get
lake build
lake env lean -DwarningAsError=true Main.lean
```

The public Mathlib dependency is Git-pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b. Ignored local cache junctions are not submitted. There are no admitted proofs, custom axioms or native decision procedures. No auxiliary numerical code is needed.

The saved LaTeX source is opened in the built-in editor. The compiler's existing platform-directory error is handled by compiling the delivered PDF with Tectonic; every final page is rendered and visually inspected.
