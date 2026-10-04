# Verification evidence

- Lean 4.19.0 and pinned Mathlib v4.19.0, complete build into an initially absent local verified-build directory via a temporary package option, restored to the standard build directory afterward.
- Fresh direct Main.lean check with warnings treated as errors, audit output in lean-check.txt.
- Every audited final theorem uses only propext, Classical.choice and Quot.sound.
- Independent Python exact D-A matrix, full eigenbasis rank 10, all 5760 embedded 3/4-cycle candidates (720+5040), nine sign components, bound 81>40.
- Tectonic 0.17.0 compiled report.pdf; two A4 pages, all visually inspected at 1400px. No clipping, overlap, broken glyphs or overfull boxes.
- Built-in LaTeX editor compilation attempted, but platform standard-directory discovery failed. Actual PDF generated successfully with Tectonic.
- Upstream metadata false/false, no upstream solution path, and direct all-state GitHub PR search for 00000002153 returned []. Root must recheck latest eligibility before publication.
- Recursive clean of the local build directory was rejected by automatic approval review; a fresh local package build directory was used instead.
