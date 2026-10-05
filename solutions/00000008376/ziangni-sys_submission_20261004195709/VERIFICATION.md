# Verification

- Final full `lake build` passed 1217 targets with no warnings.
- Twelve printed theorem audits use only propext, Classical.choice and Quot.sound. No sorry/admit, custom axioms, native_decide or unsafe declarations.
- Actual objects: max-plus tropical semiring, MvPolynomial evaluation, real finite-coordinate corner locus, complete monomial-attainment cell description, genuine permutation group action and stabilizer subgroups, diagonal-translation quotient and induced projective action.
- Point stabilizer is the full S3 with order six; the central cell is fixed setwise; the projective central point also has full S3 stabilizer. S2 has order two and cannot be isomorphic to the point stabilizer.
- report.pdf: two pages, 41011 bytes. Compiled once with Tectonic and both pages rendered and visually inspected. The built-in editor/compiler returned its known platform-directory error, so existing Tectonic was used without installation.
- Lean 4.19.0 and Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b. Public pins are unchanged. Local junctions and build artifacts are not submitted; no auxiliary computation is required.
