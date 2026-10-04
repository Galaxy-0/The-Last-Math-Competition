# Solution Review — Conjecture 00000005508 (PR 374)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004023252`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — bottleneck = first station to saturate; tied-bottleneck count = multiplicity of the minimal residual-capacity element and is "at most the logarithm of the station count" (disproof: 1 > log 1 = 0 for a one-station network).
- LaTeX: compiled from scratch in /tmp/tlmc-review5/scratch/pr-374 (pdflatex twice, exit 0, 1 page, no errors); shipped report.pdf is a real PDF with text identical to the recompile.
- Lean build: `rm -rf .lake && lake build` from a clean tree exit 0 ("Build completed successfully", 1731 tasks, zero warnings), toolchain leanprover/lean4:v4.19.0, Mathlib pinned at c44e0c8ee63ca166450922a373c7409c5d26b00b; `lake env lean Main.lean` exit 0; `#print axioms` shows only [propext, Classical.choice, Quot.sound]. (Mathlib artifacts were seeded from my own identical-revision build of the same manifest for PR 373 — package git revisions verified identical — with all remaining closure modules and Main.lean compiled in place from source; the Mathlib cloud-cache binary crashes under dyld on this macOS, so dependencies were source-built.)
- Forbidden content: grep over all .lean files for `sorry`, `admit`, `native_decide`, `axiom` declarations, `unsafe`, `@[implemented_by]`, `extern`, `skipKernelTC` — nothing found.
- Auxiliary code: none shipped ("No computational auxiliary proof is required") — none needed; I re-derived the arithmetic by hand: 1 − t < 0 iff t ≥ 1, bottleneck set {0} of size 1, log 1 = 0 in every base, so 1 ≤ 0 is false. Also verified the two-station illustration (multiplicity 2 > log 2 for bases e, 2, 10).
## Semantic audit
Conjecture (literal, EN+CN): "the number of tied bottlenecks is the multiplicity of the minimal element, at most the logarithm of the station count" / "并列瓶颈的个数为最小元的重数且重数不超过站数的对数". An exact bound with no restriction on the station count and no restriction to nondegenerate networks.

Lean encodings (namespace `BottleneckCounterexample`):
- `structure Network (n : ℕ)` with positive `capacity`/`traffic` on `Fin n`; `def residual N load i := N.capacity i - load * N.traffic i` (the residual-capacity vector of the statement); `def Saturated N load i := N.capacity i ≤ load * N.traffic i`; `def FirstBottleneck N i := ∃ threshold, 0 ≤ threshold ∧ Saturated N threshold i ∧ ∀ load < threshold, ∀ j, ¬ Saturated N load j` ("first station to saturate"); `def bottlenecks N := Finset.univ.filter (FirstBottleneck N)`; `def minimumStations N load` = filter of residual minimizers (the "multiplicity of the minimal element").
- Witness `def single : Network 1` (capacity = traffic = 1): `single_first` (saturates exactly at load 1, nothing earlier), `single_tied_count : (bottlenecks single).card = 1`, `single_minimum_multiplicity : (minimumStations single load).card = 1`, and `first_count_is_minimum_multiplicity` (the conjecture's identification convention holds for the witness — the two counts agree, so the counterexample does not exploit a mismatch between the two definitions).
- `def LogarithmicTieBound : Prop := ∀ n : ℕ, 0 < n → ∀ N : Network n, ((bottlenecks N).card : ℝ) ≤ Real.log n` — the universal exact bound; `theorem conjecture_5508_false : ¬ LogarithmicTieBound` via `single_violates : ¬(((bottlenecks single).card : ℝ) ≤ Real.log 1)` since `Real.log_one = 0`. `theorem single_violates_every_base (base : ℝ) : ¬(card ≤ Real.log 1 / Real.log base)` covers every genuine logarithm base (and the degenerate base-1 case reads 0/0 = 0, still false).

(i) Definitions faithful: stations, capacities, traffic coefficients, load, saturation, first saturation time, bottleneck set, minimal-residual multiplicity — exactly the objects the conjecture names. (ii) Hypotheses satisfied: a one-station network is permitted by the text; capacities/traffic are positive. (iii) Contradiction: multiplicity 1 ≤ log 1 = 0 is false, so the universal clause and hence the conjunction fails. (iv) Not vacuous: the objects are the conjecture's own; the identification and monotonicity clauses are left untouched, as the report states.

FLAG (non-blocking): the formal witness is the degenerate n = 1 edge case. Note two mitigations given in the report: (a) the bound fails for every logarithm base at n = 1; (b) even setting n = 1 aside, the illustrative two-identical-station network has tied-bottleneck multiplicity 2 > log 2 for bases e, 2, and 10 (and in general n identical stations give multiplicity n > log_b n for all n ≥ 2, b > 1), so the clause is not salvageable by an n ≥ 2 restriction; only the formalized witness is the singleton.
## Issues found
none blocking (degenerate n=1 witness flagged above)
## Verdict rationale
The conjecture's exact literal claim "multiplicity ≤ log(station count)" admits a one-station network, for which the multiplicity is 1 and the bound is log 1 = 0; the Lean project defines the conjecture's actual objects (network, residual vector, saturation, first-bottleneck set, minimal-element multiplicity) and refutes the universally quantified bound with only standard axioms, a warning-free build, and a faithful report. The degenerate-witness choice is disclosed and mitigated in the report itself.

## Disposition
APPROVED — merged into main (PR 374). Independent fresh rebuild of the Lean project (exit 0; only standard foundational axioms; no sorry/native_decide/extra axioms), LaTeX recompilation, auxiliary-script re-runs where shipped, independent recomputations, and a semantic audit confirming the Lean theorem establishes or refutes the conjecture as stated in both language versions.
