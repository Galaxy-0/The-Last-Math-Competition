# Conjecture 1079 local counterexample package

Original wording is retained verbatim. The paper and seven Lean source modules construct a genuine binary CSS LDPC family, with distance 5 and combined Tanner girth 4 at every positive block count. Uniform row/column bounds and unbounded length are proved. The necessary universal bound is refuted for natural log and every base at least 2. Source conventions, provenance and full target correspondence are explicit in source-correspondence.md.

Pinned Lean 4.33.0 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Reproduce with `lake build +Main` in lean/, then reload/audit the manager's independently fixed target contracts and replay with official leanchecker --fresh Main using the exact project library path. PDF reproduction uses the project's Tectonic 0.17.0, and all-page render comparison.

The manager's unchanged explicit check_submission.py invocation and independent source-bound semantic review live outside this frozen package under Phase1d verification/. This is a local development artifact; no submission eligibility, first solve or upstream acceptance is asserted. Known generalized Shor code and earlier Steane partial attempts are credited. No extra connectedness, increasing-distance or unspecified asymptotic-quality premise is assumed.
