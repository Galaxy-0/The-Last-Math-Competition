# Verification of conjecture 00000000374

This is a record of local verification and an independent model review. It is not a maintainer's review or a claim of repository acceptance.

Final validation passed on 2026-10-09: the coordinator's fresh portable replay completed all 43 commands; 137 compiled declarations were inventoried, comprising 122 safe mathematical declarations and 15 unreachable compiler execution definitions. All 41,623 constants in the safe declarations' type/value dependency closure were checked. There were zero unsafe proof dependencies and zero axiom declarations owned by either mathematical module. All 21 unit controls and six compiled negative fixtures passed. The independent semantic reviewer also rebuilt the final proof and reproduced the complete inventory.

## Mathematical correspondence

The exact English and Chinese statement is preserved in `ORIGINAL.md`. The final theorem negates the literal full-real-line conjunct for every one of the three specified arithmetic height conventions and both real/complex approximant domains. The formal sets count distinct algebraic numbers, include degree one and two, and use the source's strict inequality with constant one and real exponent `-tau`.

The source leaves `H` undefined. The report explicitly uses naive coefficient height, Mahler measure, and the primitive-minimal-polynomial formula for absolute multiplicative Weil height. It makes no claim about arbitrary height functions, logarithmic height, archimedean house, rescaling, or the separate Hausdorff-dimension assertions. No hidden irrational-target restriction is inserted.

The proof constructs the primitive integer minimal polynomial and proves its degree, irreducibility, vanishing, sign uniqueness, positive normalization and exact height identification. All finiteness and root inequalities are symbolic Lean proofs. No external mathematical computation or numerical search is required.

## Rebuild and dependency checks

The project pins Lean 4.19.0 and nine standard dependencies, including Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The portable `verify.py` creates a fresh project from the frozen source files and uses an existing cache of these pinned dependencies. It verifies every dependency's Git revision and tracked cleanliness before and after execution. “Fresh build” here refers to authored modules; it does not mean every standard dependency was rebuilt from source.

The verifier runs a full build and direct source replay with warnings treated as errors. It checks the actual final theorem and definitions through `Inspect.lean`, replays the helper's inspection, and runs the compiled declaration audit. All commands, exit codes, standard output and standard error are retained in the verification results.

## Proof assumptions and compiler implementation declarations

`Audit.lean` enumerates declarations by compiled module ownership in **both** `Counterexample` and `HeightRoots`, including private and generated declarations. The inventory records names, types, kinds, module ownership, direct references and transitive axioms.

Lean 4.19 generates unsafe execution helpers for ordinary inductives, pattern matching and finite-set operations. These compiler implementation declarations are not authored unsafe Lean source or mathematical assumptions. A blanket test that no compiled declaration is marked unsafe would misclassify them. The audit retains them explicitly rather than silently omitting them.

The proof safety requirement is that every safe mathematical declaration has only the standard foundational axioms `propext`, `Classical.choice`, and `Quot.sound`, and that **no unsafe constant is reachable through its type or value dependencies**, transitively. Compiler implementation exceptions are limited to exact reviewed identities under the frozen mathematical source and complete compiled inventory; there is no broad name-pattern exemption. Changed or additional declarations, including generated helpers, cause the portable comparison to fail. Authored mathematical sources are also checked for admitted proofs, custom axioms, unsafe code, native evaluation proofs and implementation overrides.

The two unused `deriving DecidableEq` clauses in the initial author draft were removed during verification. `naivePolynomialHeight` was explicitly marked `noncomputable` to suppress unnecessary executable specializations, including three compiler-generated specialization placeholders. No mathematical expression, proof body or theorem statement changed. The initial blanket-audit failures were retained in local working records; they are not reported as proof failures or successful audits. The final audit rejects every axiom declaration owned by either submitted mathematical module and uses the explicitly documented distinction above for the remaining execution definitions.

## Independent review and report

A fresh reviewer was given only this candidate's exact original, repository rules, candidate artifacts and standard dependencies. The review checked all definitions and quantifiers, the complete proof, and the entire final LaTeX report. It independently rebuilt copied source and replayed the critical/final axiom inspection. This is an independent model check, separate from maintainer acceptance.

The final report compiled in the built-in LaTeX editor and was exported with Tectonic. All three PDF pages were rendered and visually inspected. The export has no LaTeX layout warnings. The source/PDF identities and visual record are included under `verification/`.

## Verification controls and evidence

`test_verify.py` exercises integrity and rejection cases, including changed sources or dependency pins, missing or altered compiled declarations, malformed records and disallowed proof assumptions. Its compiled controls deliberately create invalid declarations in isolated projects for each mathematical module and require the audit to reject them. Expected failures in these test fixtures are successful controls, not part of the submitted proof.

The final execution records, exact source manifest, compiled inventory, independent semantic review, and report verification records in `verification/` identify the artifacts actually checked. Paths in command logs describe the local validation environment; the portable commands in `README.md` take replacement dependency and output paths.

Repository eligibility was checked against the original source, current rules and metadata, main-branch solution history, public PR/issue feedback and available public references. That check is bounded to its recorded observation interval. Only this personal submission directory is changed; a public result can arrive after any observation.
