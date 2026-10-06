# Prove conjecture 00000004930: two MDPs with equal optimal discounted values for every discount factor but average rewards 1 and 0

The conjecture asks for two MDPs with identical values for all discount factors but different average rewards, realized by a construction that concentrates the discount weights on transients.
- **MDP A.** One state, one action, reward 1.
- **MDP B.** From `start`, action `n` enters a countdown `n, n-1, …, 0`, then an absorbing sink. Reward is 1 off the sink and 0 on it, so all reward sits on transient states.
- **Values.** `optValue A β = optValue B β = (1-β)⁻¹` for every `β` (`optValue_A`, `optValue_B`). The supremum in B is approached by longer and longer countdowns.
- **Average rewards.** Under every history-dependent randomized policy, A's average tends to 1 and B's tends to 0. For `t ≥ 1` the state law of B depends only on the first action (`law_state`), so `E[r_t] → 0`, and Cesàro gives the rest.
- **Main theorem.** `Conjecture4930.conjecture4930`.
- **Scope.** The witness needs a countably infinite state space. For finite MDPs the separation is impossible (Blackwell), and so it is for a single fixed policy.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 300 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture4930/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000004930.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `Conjecture4930.conjecture4930`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000004930 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
