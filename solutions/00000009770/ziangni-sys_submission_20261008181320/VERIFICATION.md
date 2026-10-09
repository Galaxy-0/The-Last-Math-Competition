# Verification

Run `lake build` in `lean/` using Lean 4.19.0. The project and transitive public dependencies are pinned in `lakefile.lean` and `lake-manifest.json`. Local cache junctions are ignored and are not needed by a fresh checkout.

The principal theorems print their axiom dependencies. Only `propext`, `Classical.choice`, and `Quot.sound` occur. There are no proof placeholders, native-decision shortcuts, custom axioms, or unsafe proof code.

The modulus is Mathlib's canonical positive square root of A* A; the trace norm is its real trace. Support is the actual range of the modulus, and the polar factors are the genuine supported projections. The diagonal atomic measures are linked to the matrix entries by their singleton masses. The final theorem refutes same-support necessity without claiming to refute compatible common polar factors.

The PDF was compiled with the existing Tectonic executable after the built-in compiler reported its platform-directory failure. All rendered pages were visually inspected for layout and legibility.
