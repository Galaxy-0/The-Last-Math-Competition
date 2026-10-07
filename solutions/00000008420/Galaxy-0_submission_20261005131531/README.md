# TLMC 00000008420: counterexample to the minimum-order clause

The system with point set `{0,1,2}`, one block `{0,1,2}`, and one parallel class is a Kirkman triple system. The permutation `(0 1 2)` preserves that resolution and is itself transitive. Its order is 3, less than the claimed minimum 15.

This is a counterexample to the conjecture as written, which does not exclude the trivial order-three system. It does not claim to refute the remaining conjuncts. In particular its full automorphism group is S3, not a cyclic group of prime order.

## Files

- `proof.tex`, `proof.pdf`: complete mathematical disproof, conventions, and explanation of the earlier rejected argument.
- `Counterexample.lean`: meaningful finite incidence and resolution definitions, explicit automorphism, cyclic transitivity and exact order, and refutation of the minimum-order clause.
- `lakefile.lean`, `lean-toolchain`: self-contained Lean 4 project; no mathlib dependency.
- `build-pdf.sh`: standard two-pass LaTeX build.
- `Audit.lean`, `verify.sh`: strict source replay and complete authored-theorem axiom audit.
- `conjecture.md`: original bilingual statement.
- `verification/`: successful compiler logs and upstream status snapshot.

## Build

With the pinned Lean toolchain installed:

    lake build
    lake env lean -DwarningAsError=true Counterexample.lean
    lake env lean -DwarningAsError=true Audit.lean

Or run `./verify.sh`.

With a normal LaTeX installation:

    ./build-pdf.sh

## Verification status

Verified with official Lean 4.31.0 (release commit `68218e876d2a38b1985b8590fff244a83c321783`): `lake build` succeeded, direct source elaboration with `-DwarningAsError=true` succeeded, and all eight theorem axiom checks succeeded. The only dependencies reported are the standard Lean axioms `propext` and `Quot.sound`; the exact-order theorem uses only `propext`. No admitted proofs, native evaluation shortcut, custom axioms, or kernel-check bypass are used. PDF compiled locally and both pages were visually inspected. Logs are included under `verification/`.

## Earlier submission and its error

Pull request 21 used the affine plane of order 3, which has 9 points, and a transitive group of translations. That does not establish that any one automorphism is transitive. Every nonidentity translation has order 3 and three orbits of size 3. The later audit removed that submission, noting that AGL(2,3) has no element of order 9. Our construction gives a single explicit 3-cycle and therefore does not rely on the rejected group-transitivity substitution.

- Earlier PR: https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/pull/21
- Audit commit: https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/commit/541cf4fbc7aef3e17085577f6403c11c09f31fe1
- Standard convention explicitly including KTS(3): Ezra Brown and Keith E. Mellinger, *Kirkman's Schoolgirls Wearing Hats and Walking through Fields of Numbers*, PDF page 3: https://personal.math.vt.edu/brown/doc/kirkman.pdf
