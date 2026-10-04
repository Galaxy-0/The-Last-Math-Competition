# Verification

- Fresh project lake build passed on the full source; replay success saved in lean-build.txt.
- Direct final Main.lean check with warnings treated as errors passed, with audits in lean-check.txt.
- Constructed-map surjectivity/injectivity proofs depend only on propext. Universal finite-group obstruction and final six-piece theorem use only propext, Classical.choice and Quot.sound.
- Genuine pieces are fibers of a labeling function, proved to cover and be mutually disjoint. Actual left multipliers and side covering/separation produce the tagged translation map; no numerical contradiction is assumed as input.
- Tectonic compilation passed with no box/layout warnings. Final PDF contains two A4 pages, both rendered at 1400px and fully inspected with no clipping, overlap, broken glyphs or formatting defects.
- Built-in LaTeX editor opened; its compiler failed standard platform directory lookup. The actual PDF was compiled successfully by Tectonic.
- No auxiliary computation needed for this general counting proof.
- Initial source eligibility: metadata false/false; HEAD solution path empty; live all-state GitHub PR search returned []. Root must recheck before publication.
