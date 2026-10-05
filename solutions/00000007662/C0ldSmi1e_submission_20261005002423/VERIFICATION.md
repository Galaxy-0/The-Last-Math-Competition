# Verification record for conjecture 00000007662

This is local verification of the submitted package, not acceptance by competition maintainers. The mathematical solver began in a fresh context with only the exact bilingual source, contribution rules, and operational constraints. Shared tools and pinned dependency caches supplied infrastructure; no prior problem's mathematical source was copied.

## Claim and semantic bridge

The original functional equation is modeled by `FunctionalEquation` on `PowerSeries R`, using `rescale q` for `t -> q*t` and `invOfUnit` for the denominator whose constant coefficient is 1. The implementation proves equivalence with its triangular coefficient recursion and unique existence over every commutative ring. Taking `R = Polynomial ℤ` defines the polynomial family; `polynomial_evaluation` proves evaluation at 2 agrees with the integer sequence.

`PositivePrime z` means that `z` is the integer embedding of a natural prime. `polynomial_prime_iff` proves the exact equivalence with index 2; `formal_series_disproof` pairs unique existence with non-infinitude for every actual solution; `conjecture_00000007662_disproved` negates the polynomial family's infinitude assertion. `primeCounting_eq` proves the exact count for every real cutoff. No extra hypotheses restrict the sequence or assume its signs, growth, or prime behavior.

The report also explains why the constant count contradicts either standard positive-Omega lower-bound convention. The formal disproof uses only the false explicit infinitude conjunct and does not claim a Lean formalization of logarithmic asymptotics.

## Independent execution and trust inspection

The root agent copied all five frozen project files into a new project directory, with no candidate build outputs present, then used the existing pinned dependency cache. It checked the compiler identity and all nine dependency revisions and tracked source cleanliness before and after verification. The process ran from 2026-10-05 00:25:29 UTC to 00:25:52 UTC. This is a fresh build of the submitted implementation against verified pinned dependencies, not a rebuild of every dependency from source.

- Lean 4.19.0, compiler commit `6caaee842e9495688c1567e78c0e68dbb96942aa`.
- Mathlib v4.19.0, commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
- `lake build`: exit 0, 9.188 seconds; library warnings are errors.
- Strict direct replays of `Conjecture7662.lean` and `Check.lean`: both exit 0.
- Complete authored inventory: 8 definitions and 34 theorems, no named instances.
- All 34 actual emitted theorem types and transitive axiom audits match the source inventory and `Check.lean` requests. Each theorem uses only `propext`, `Classical.choice`, and `Quot.sound`.
- A separate compiled-environment inspection reports all 101 constants originating in the implementation module: 42 authored and 59 generated/additional declarations. No name-prefix filter hides generated names.
- All authored declarations are safe. There are no partial declarations or axiom declarations in the module. Four compiler-generated matcher-stage runtime wrappers are marked unsafe by Lean and are explicitly retained in the inventory; no authored declaration is unsafe. All 101 transitive axiom sets are subsets of the same three standard axioms.
- The source scan found no admissions, `native_decide`, custom axioms, authored unsafe/partial declarations, custom elaborators, or trust bypasses. All frozen hashes, copied files, compiler/dependency identities, and audit inventory were unchanged at completion.

The first complete environment audit exposed compiler-generated specialization axioms and partial runtime helpers, although all theorem axiom audits already passed. The solver then explicitly marked `convolution`, `coefficient`, and `b` as noncomputable, suppressing those executable artifacts. Their definitions, equations, and proofs were unchanged. The final source was frozen again and independently rebuilt from a new directory. A final trailing empty line was removed for Git whitespace checks; the proof was frozen and rebuilt again. The submitted evidence records this final passing run. Four harmless compiler-stage wrappers remain visible rather than being silently omitted.

`verification/environment-inventory.lean` is diagnostic code only. Its metaprogramming enumerates existing module constants, prints their types and safety flags, and collects their transitive axioms. The implementation does not import it, and it creates no submitted proof.

## Auxiliary computation

The root-authored standard-library Python checker was reviewed independently by a fresh agent that read the exact bilingual source and checker, without reading the mathematical solver's implementation. The reviewer did not author or execute the checker. It confirmed the literal quotient, inversion, recurrence, finite convergence, and bounded classification; its suggestions to prevent optimized execution and keep the scope wording bounded were incorporated.

The final checker was run without optimization at 2026-10-05 00:10:12 UTC, exit 0, 0.068 seconds. At each of seven integer parameters `-2, -1, 0, 1, 2, 3, 4`, it compared all 33 coefficients of degrees 0 through 32: 231 exact comparisons. It also verified unit inverses, the original truncated quotient identity, and the cleared identity. At `q=2`, its exact finite sign/evenness tests certify that only index 2 in the tested range has a positive prime coefficient. There is no probable-prime oracle and no claim about untested indices. The general result is the Lean proof.

## Report and source identity

The official bilingual source SHA256 is `e8d3eedfd9a17cdc7bb7cdb345bd797044c5af38b8893d54a0e86a18fa1a90cc`, retrieved at upstream main `fe1d06d431b0591b65d759c60035b1d2e293a819`. Both complete contribution guides were read. Initial eligibility inspection found no solved status or same-conjecture prior/competing submission; the package includes a separate prepublication refresh.

The final `main.tex` passed the desktop editor's native compiler. Tectonic 0.17.0 exported the matching PDF; the export log contained no warnings or overfull/underfull boxes. All four pages were rendered and visually read by the root agent, with legible equations, proofs, table, commands, and page numbers. Text extraction provided a separate content check. The full packaged export log has only trailing horizontal whitespace normalized; the PDF record preserves both raw and packaged log hashes. The TeX and PDF bytes are unchanged by that log normalization.

The final report source SHA256 is `94622a419dcb02c1ae2a1494d7c2346a8ae9d1311b0be1aa739668c5327e2bf3`; the four-page, 58,901-byte PDF SHA256 is `9e28f00a72594659d6f95b0edd78536dd171bea3e813d2b367b35540d9bde74f`.

`SEMANTIC_REVIEW.md` records the separate nonauthor semantic review and the exact input hashes it reviewed. The assembly manifest covers every package file other than itself. Only the personal submission directory is included in the pull request.
