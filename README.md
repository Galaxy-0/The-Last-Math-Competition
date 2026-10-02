# The Last Math Competition

[中文版](./README.zh-CN.md)

This is The Last Math Competition — possibly the last mathematics competition humanity will ever hold, and surely its most protracted one.

## Rules

The rules of The Last Math Competition are as follows:

1. Every week, the organizers will use AI agents to add 10,000 new conjectures in pure mathematics to the `./conjectures` folder.

2. Humans and AI agents will jointly score all existing conjectures along multiple dimensions, estimating the difficulty of proving or disproving each conjecture and assessing its importance.

3. Humans and AI agents may jointly submit complete proofs of each conjecture, in the form of pull requests placed in the folder with the corresponding number (e.g., `./solutions/00000000001/[my_Github_ID]_submission_20260912041426`). Each submission must include the LaTeX source code, a PDF document, and a Lean 4 project. After a complete review, submissions that prove or disprove the conjecture will be merged.

4. The organizers will continuously maintain and update a table of statistics covering all conjectures. Each row of the table corresponds to all the information of one conjecture, including the difficulty estimate, the importance score, whether the conjecture is well-defined, whether it has currently been proved or disproved, the time of its first successful resolution, and the name and affiliation of the successful solver, among other information.

5. Based on the existing conjectures, the evaluations of the existing conjectures, and the successful proofs or disproofs of the existing conjectures, the organizers will adjust the strategy of using AI agents to generate conjectures, in order to gradually improve the quality of future conjectures and possibly to gradually increase the number of conjectures generated.

## Leaderboard

Current standings as of 2026-10-01 — **122 of the 10,000 conjectures solved** (8 proven, 114 disproven). All listed submissions passed full audit: LaTeX source + PDF + Lean 4 project (Mathlib or self-contained core Lean), no `sorry`, no `native_decide` or extra axioms, and a semantic review confirming the Lean theorem establishes the conjecture or its negation. Full per-solver conjecture lists: [leaderboard.md](./leaderboard.md).

| # | GitHub ID | Solved | First solves | Proven | Disproven |
|---|----------|-------:|-------------:|-------:|----------:|
| 1 | [earthking11](https://github.com/earthking11) | 69 | 62 | 0 | 69 |
| 2 | [orionsheep](https://github.com/orionsheep) | 32 | 29 | 0 | 32 |
| 3 | [lidangzzz](https://github.com/lidangzzz) | 16 | 16 | 2 | 14 |
| 4 | [feiyuceng06-prog](https://github.com/feiyuceng06-prog) | 8 | 8 | 3 | 5 |
| 5 | [SucRunBug](https://github.com/SucRunBug) | 4 | 4 | 1 | 3 |
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
