# Verification

Run `lake build` in `lean/` using Lean 4.19.0. Mathlib is pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b; public transitive pins are in the manifest. Local cache junctions are ignored.

The formal proof evaluates the actual Radon integral for every normal angle and offset, using the unit-speed line parametrization. It proves Gaussian slice integrability and the squared-radius identity. Degree 0 is the total degree of an actual multivariable polynomial, and harmonicity uses actual partial derivatives. The angular factor and output degree are checked separately, then assembled into the surviving-even-mode theorem.

Principal theorem audits use only propext, Classical.choice and Quot.sound. There are no proof placeholders, custom axioms, native-decision shortcuts or unsafe proof code.

The PDF was compiled with existing Tectonic after the built-in LaTeX compiler's known platform-directory failure. Every rendered page was visually inspected. The report states the exact parity assertion addressed and distinguishes the alternative operators and parity conventions.
