# Conjecture 00000003944: disproof

A connected eight-vertex triangular prism with two leaves has maximum degree five. Its proper three-colourings split into two invariant events of size 24 among 48 colourings. Every full-component Kempe walk started in one event stays at total-variation distance at least 1/2 from uniform on all colourings, so its mixing time at threshold 1/4 is infinite.

This addresses the printed unrestricted claim. No relation between palette size and maximum degree is stated in the conjecture. We fix a palette of three colours and use the standard meaning of maximum degree. It is not a counterexample to a different statement with an additional large-palette hypothesis.

The paper also gives arbitrarily large connected counterexamples at the same maximum degree by extending a pendant vertex with a path. Each new tree vertex contributes two colouring choices, so the invariant event remains half of all colourings. This unbounded-order extension is a mathematical argument in the paper; the Lean formalization is explicitly the eight-vertex member.

## Files

- `main.tex`, `main.pdf`: complete mathematical argument and formal correspondence.
- `Conjecture3944.lean`: self-contained standard-library formalization.
- `Audit.lean`: theorem and axiom audit.
- `independent.py`: independent complete enumeration and exact rational transition-matrix audit.
- `VERIFY.sh`: reproducible build and kernel checks.
- `build_pdf.sh`: PDF rebuild, without shell escape.

## Verification

Install Lean 4.31.0 (as pinned in `lean-toolchain`), then run:

```
./VERIFY.sh
```

There are no external Lean dependencies. Python 3 uses only its standard library. Rebuild the PDF with `./build_pdf.sh` on a standard TeX installation. The script also accepts an optional directory containing `pdflatex.fmt` for minimal installations.

### Main formal results

- `simple_graph`, `connected`, `degree_five`: genuine connected simple graph with maximum degree exactly five.
- `decode_encode`, `decode_injective`, `states_complete`: a bijective enumeration of all assignments, filtered exactly by properness.
- `state_count`, `opposite_count`: 48 colourings and invariant event of size 24.
- `kempe_invariant`: invariance under actual whole two-colour connected components, defined by an inductive path relation.
- `unreachable`: explicit proper colourings cannot be connected by legal moves.
- `uniform_normalized`, `uniform_mass`: uniform target is a normalized probability law with weight 1/48 at each proper colouring.
- `event_gap`: exact event discrepancy 1/2 at every time for any rational transition kernel supported on switches or holding steps.
- `never_mixes_at_quarter`, `counterexample`: no time satisfies the standard total-variation threshold of 1/4, including for stochastic kernels.
- `no_uniform_mixing`: no pointwise convergence to uniform.

The probability proof uses rational kernels. The ordinary chain choosing one of three unordered colour pairs and one of eight seeds uniformly is such a kernel. The paper supplies the elementary real-probability version of the same invariant argument and proves uniform stationarity for that concrete chain by involutivity. The Python check independently verifies the concrete kernel's exact row sums, symmetry, stationarity and invariant support. Its results are not assumptions in Lean.

All proof computations are kernel reductions (`decide +kernel`). The axiom audit contains only `propext`, `Classical.choice`, and `Quot.sound`, with no proof holes, native-decision axioms or custom axioms.
