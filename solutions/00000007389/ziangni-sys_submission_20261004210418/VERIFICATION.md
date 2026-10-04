# Validation

The complete project lake build succeeded (1751 targets). Eight printed theorem audits contain only propext, Classical.choice and Quot.sound. No custom axioms, omitted proofs, native_decide or unsafe definitions are used.

Formalized objects include continuous linear equivalences, actual HasFDerivAt premises and chain rules, affine maps, transformed root residuals, inverse Newton corrections, recursive iterates, and tangent identity/composition rules. The analytic hypothesis at each visited point is explicit; covariance is derived rather than assumed.

The public Lean and Mathlib pins are in lean-toolchain, lakefile.lean and lake-manifest.json. Local cache junctions are ignored and are not dependencies of the submitted configuration. No shared cache changes were needed.

The built-in LaTeX compiler reported its known platform directory error; existing Tectonic successfully compiled the standalone source. Both final PDF pages were rendered and visually checked; no clipping or layout warnings remained.
