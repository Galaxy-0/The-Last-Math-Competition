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

2. Once a reviewer considers the proof or disproof of the conjecture complete and valid, please create a `review` folder under the corresponding solutions folder `./solutions/[number_ID]` and add a complete solution review — either as a Markdown document, or in the form of a LaTeX source file plus a PDF document. If needed, include in the solution review any additional Lean 4 projects, source code in other languages, and configuration files it requires, so as to constitute a complete review. Finally, merge the pull request into the main branch, and fully update the leaderboard, the metadata, and the leaderboard sections of both the Chinese and the English READMEs.

3. Once a reviewer considers the proof or disproof invalid, incomplete, or not conforming to the definition of the conjecture, the pull request should be closed, together with a complete explanation.

### Rules for Maintainers

1. As a maintainer, your responsibility is to periodically add 10,000 new conjectures and to produce those 10,000 conjectures yourselves, ensuring that the problems are of the highest possible quality — original, and with the potential for breakthroughs and disruption — mathematical conjectures that push forward the frontier of mathematical research or inspire an entirely new field of mathematics. Save them as `[number_ID].md` files in the `./conjectures` folder, where `number_ID` is an 11-digit number giving the conjecture's ID.

2. Before each submission, make sure that both the Chinese and the English versions exist, and that every conjecture has a complete and clear definition with all the necessary conditions.

## Leaderboard

Current standings as of 2026-10-04 — **470 of the 10,000 conjectures solved** (37 proofs, 433 disproofs). Every submission below passed the full audit — LaTeX source, PDF, and a Lean 4 project (Mathlib or self-contained core Lean) that compiles with no `sorry`, no `native_decide`, and no extra axioms — together with a semantic review confirming that the Lean theorem establishes the conjecture or its negation. Complete per-solver conjecture lists: [leaderboard.md](./leaderboard.md).

| # | GitHub ID | Solved | First solves | Proven | Disproven |
|---|----------|-------:|-------------:|-------:|----------:|
| 1 | [ziangni-sys](https://github.com/ziangni-sys) | 102 | 102 | 7 | 95 |
| 2 | [gaochengzhecpu](https://github.com/gaochengzhecpu) | 81 | 81 | 6 | 75 |
| 3 | [orionsheep](https://github.com/orionsheep) | 73 | 65 | 0 | 73 |
| 4 | [earthking11](https://github.com/earthking11) | 66 | 59 | 0 | 66 |
| 5 | [feiyuceng06-prog](https://github.com/feiyuceng06-prog) | 37 | 36 | 8 | 29 |
| 6 | [jilint777](https://github.com/jilint777) | 20 | 20 | 1 | 19 |
| 7 | [SucRunBug](https://github.com/SucRunBug) | 18 | 18 | 2 | 16 |
| 8 | [lidangzzz](https://github.com/lidangzzz) | 16 | 16 | 2 | 14 |
| 9 | [C0ldSmi1e](https://github.com/C0ldSmi1e) | 15 | 15 | 1 | 14 |
| 10 | [idealistichacker](https://github.com/idealistichacker) | 3 | 3 | 2 | 1 |
| 11 | [GodBlf](https://github.com/GodBlf) | 2 | 2 | 0 | 2 |
| 12 | [lizaixi01](https://github.com/lizaixi01) | 2 | 2 | 0 | 2 |
| 13 | [11zhangzheng](https://github.com/11zhangzheng) | 1 | 1 | 0 | 1 |
| 14 | [champagnepapihz](https://github.com/champagnepapihz) | 1 | 1 | 0 | 1 |
| 15 | [Galaxy-0](https://github.com/Galaxy-0) | 1 | 1 | 1 | 0 |

## An Early-Stage Disclaimer

The competition is still in its early days, and we must be candid: the average quality of the conjectures generated so far is relatively poor. Some are insufficiently defined, some carry erroneous conditions or obvious mistakes, and a few may even be "not even wrong." The statistics table maintained for every conjecture is precisely the instrument for improving the quality and methodology of newly generated conjectures as the competition evolves.

## Long-Term Goals

Our long-term goals are:

1. Through sustained competition and feedback, we will steadily improve the quality of the conjectures. In generating conjectures at scale over the long run, we hope to create a number of genuinely important ones whose proofs or disproofs advance the edifice of mathematical knowledge.

2. We will explore a technical route of AI-agent-led mathematical research and proof. As a public competition and benchmark, it evaluates in real time the performance of models, harnesses, and proof tools; the community as a whole will jointly explore the methodology of scientific research in the age of AI.

3. All the conjectures of this competition, together with their evaluations and scores and their final proofs or disproofs — as verified and peer-reviewed knowledge jointly produced by AI agents around the world — can be used for future mathematical research and for future LLM training.
