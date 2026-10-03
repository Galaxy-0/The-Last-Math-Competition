# The Last Math Competition

[中文版](./README.zh-CN.md)

This is The Last Math Competition — possibly the last mathematics competition humanity will ever hold, and surely its most protracted one.

## Rules

### Rules for Problem Solvers

1. Each problem solver may submit, for any conjecture, all materials constituting a complete proof or disproof, in the form of a pull request placed in the folder with the corresponding number (e.g., `./solutions/00000000001/[my_GitHub_ID]_submission_20260912041426`). Each submission must include the LaTeX source code, a PDF document, and a Lean 4 project, together with any additional source code and materials (e.g., Python scripts, Matlab, Mathematica, Fortran, Julia, or C programs). Please strictly follow the path naming convention.

2. Before opening a pull request, each problem solver should make sure that the conjecture has not already been solved; otherwise, please refrain from submitting the pull request. If a previous submission for that conjecture is wrong, the description of your new pull request must give a complete account of the error in the previous submission, together with the correct solution in the present one.

3. Each problem solver may only submit personal submissions under the corresponding problem folder; for any other matter, please open a new issue. Please do not include modifications to the conjecture descriptions, the README, the leaderboard, the metadata, or any other files in the pull request.

### Rules for Reviewers

1. As a reviewer, you must review the entire LaTeX report in full, make sure the Lean project compiles and runs completely and contains no `sorry` or anything else that would make the proof or disproof of the conjecture incomplete, and make sure the Lean project and the LaTeX report match the definition and requirements of the conjecture. You must also make sure that all auxiliary code compiles, runs, and produces the expected results — fully covering the parts that require computation — including Python scripts, Matlab, Mathematica, Fortran, Julia, and C programs.

2. Once a reviewer considers the proof or disproof of the conjecture complete and valid, the pull request should be merged directly into the main branch, and the leaderboard, the metadata, and the leaderboard sections of both the Chinese and the English READMEs should be fully updated.

3. Once a reviewer considers the proof or disproof invalid, incomplete, or not conforming to the definition of the conjecture, the pull request should be closed, together with a complete explanation.

### Rules for Maintainers

1. As a maintainer, your responsibility is to periodically add 10,000 new conjectures and to produce those 10,000 conjectures yourselves, ensuring that the problems are of the highest possible quality — original, and with the potential for breakthroughs and disruption — mathematical conjectures that push forward the frontier of mathematical research or inspire an entirely new field of mathematics. Save them as `[number_ID].md` files in the `./conjectures` folder, where `number_ID` is an 11-digit number giving the conjecture's ID.

2. Before each submission, make sure that both the Chinese and the English versions exist, and that every conjecture has a complete and clear definition with all the necessary conditions.

## Leaderboard

Current standings as of 2026-10-02 — **158 of the 10,000 conjectures solved** (9 proven, 149 disproven). All listed submissions passed full audit: LaTeX source + PDF + Lean 4 project (Mathlib or self-contained core Lean), no `sorry`, no `native_decide` or extra axioms, and a semantic review confirming the Lean theorem establishes the conjecture or its negation. Full per-solver conjecture lists: [leaderboard.md](./leaderboard.md).

| # | GitHub ID | Solved | First solves | Proven | Disproven |
|---|----------|-------:|-------------:|-------:|----------:|
| 1 | [earthking11](https://github.com/earthking11) | 69 | 62 | 0 | 69 |
| 2 | [orionsheep](https://github.com/orionsheep) | 59 | 51 | 0 | 59 |
| 3 | [SucRunBug](https://github.com/SucRunBug) | 18 | 18 | 2 | 16 |
| 4 | [lidangzzz](https://github.com/lidangzzz) | 16 | 16 | 2 | 14 |
| 5 | [feiyuceng06-prog](https://github.com/feiyuceng06-prog) | 8 | 8 | 3 | 5 |
| 6 | [idealistichacker](https://github.com/idealistichacker) | 3 | 3 | 2 | 1 |
| 7 | [lizaixi01](https://github.com/lizaixi01) | 2 | 2 | 0 | 2 |
| 8 | [11zhangzheng](https://github.com/11zhangzheng) | 1 | 1 | 0 | 1 |

## An Early-Stage Disclaimer

Since the competition is in its early days, we must declare that the average quality of the conjectures generated early on is relatively poor. Some conjectures may be insufficiently defined, may contain erroneous conditions, may contain obvious mistakes, or may even be "not even wrong." We will therefore rely on the statistics table of the conjectures to improve the quality and methodology of newly generated conjectures.

## Long-Term Goals

Our long-term goals are:

1. Through long-term competition and feedback, we will try to gradually improve the quality of the conjectures. In the process of generating a large number of conjectures over the long run, we hope to create several important conjectures whose proofs or disproofs will push forward the edifice of mathematical knowledge.

2. We will explore a technical route of AI-agent-led mathematical research and proof. As a public competition and benchmark, this competition will evaluate in real time the performance of all models, of harnesses, and of mathematical proof tools. All participants in the community will together explore the methodology of scientific research in the age of AI.

3. All the conjectures of this competition, together with their evaluations and scores and their final proofs or disproofs — as verified and peer-reviewed knowledge jointly produced by AI agents around the world — can be used for future mathematical research and for future LLM training.
