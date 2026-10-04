# Verification and scope

The fresh complete project build passed (`lean-build.txt`). A direct full-source Lean check with warnings treated as errors passed (`lean-check.txt`). The six audited theorem dependencies consist only of propext, Classical.choice and Quot.sound. There is no admitted proof, extra axiom or native decision shortcut. No numerical auxiliary code is required for the exact universal real algebra and topology proofs.

The two-page A4 PDF compiled successfully using Tectonic (`pdf-build.txt`) without box warnings. Both pages were rendered with Poppler at1400pixels and inspected in full: clear equations and typography, no overlap/clipping. The built-in LaTeX editor opened; its compiler was attempted but returned the known platform standard-directory lookup failure. Tectonic generated the actual verified PDF.

`source.md` preserves both source languages; `eligibility.txt` records initial eligibility. The coordinator repeats live checks before publication.

Semantic scope: disproves necessity of strong monotonicity in the single-valued-continuity equivalence. All objects are actual real operator graphs and the actual inclusion. The maximal-monotone zero operator on R has solution p/lambda on the connected domain R×(0,infinity), jointly continuous, and fails every positive strong-monotonicity constant. Other source clauses are not addressed. No dependency cache writes were made.
