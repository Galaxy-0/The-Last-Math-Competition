# Verification

Fresh project lake build and direct whole-source lean check with warningAsError=true passed. Five principal printed axiom audits list only propext, Classical.choice and Quot.sound. No sorry, admit, native_decide or additional axioms occur in Main.lean.

The Lean source encodes actual feasible allocations, full bid domain, allocation-welfare maximization, Clarke-pivot payment definition, maximization of other-agent welfare with a feasible attaining allocation, true-valuation utilities, arbitrary unilateral bid updates, tie cases, actual coalition finite set/cardinality, and actual finite sum of coalition utility gains. The final statement includes admissibility, nonpositive unilateral gains with zero attainment, and the strict coalition-gain violation.

Configuration pins Lean 4.19.0 and Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b, with public transitive Git revisions in the manifest. No shared cache extension or lake clean was performed.

The built-in LaTeX editor/compiler was attempted and returned the known platform-directory error. Tectonic compiled the final two-page PDF without TeX layout warnings. Both final pages were rendered and visually inspected. All text files use LF bytes and git diff --check passed. Build products and local junctions are ignored and excluded from the commit.
