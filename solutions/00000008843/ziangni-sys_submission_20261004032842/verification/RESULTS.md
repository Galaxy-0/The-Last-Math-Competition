# Verification evidence

- Fresh complete project lake build under Lean 4.19.0 and pinned Mathlib v4.19.0 passed on the first attempt; output saved in lean-build.txt.
- Direct final Main.lean source check with -DwarningAsError=true passed; audits saved in lean-check.txt.
- Constant closed-convexness, all subgradients, additive-constant invariance and concluding theorem audits contain only propext, Classical.choice and Quot.sound.
- ConvexOn is the actual real convex function predicate; closedness is IsClosed of the actual epigraph subset of real product space. Subdifferential sets are defined through the global supporting inequality for every real y, and computed for every real x and slope.
- No auxiliary numerical computation is necessary; all inequalities are universally proved over real numbers.
- Tectonic final compilation passed without box warnings. Both A4 pages rendered at 1400px and fully visually inspected; clean layout, no clipping or overlap.
- Built-in LaTeX editor opened and compilation attempted; known standard platform-directory lookup failure. Actual PDF compiled successfully using Tectonic.
- Source metadata false/false, HEAD solution path empty, correct live all-state PR search []. Root rechecks before publication.
