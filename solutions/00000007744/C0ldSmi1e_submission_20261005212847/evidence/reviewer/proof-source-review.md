# Independent proof-source review: conjecture 00000007744

Date: 2026-10-05. Verdict for the frozen Lean source, model, and supporting executions: **PASS**. The report and PDF were not yet supplied at this stage, so this is not a complete-artifact acceptance or publication clearance.

## Independence and exact inputs

The reviewer first read the exact bilingual conjecture and both current contribution guides and saved `source-preassessment.md` and `acceptance-criteria.md` before receiving candidate work. No selector rationale, previous solution/PR, other problem proof, or external mathematical history was consulted. Only the coordinator-authorized standard dependency package directory was reused, never its enclosing proof project.

The independently copied six frozen source/configuration files are in `fresh-proof/`. The checked SHA256 values are:

| File | SHA256 |
|---|---|
| Conjecture7744.lean | `05a5d6f205fa85d7f0d74eb6e20d7a1cd5346d4d870a697a861b4e333c1421cb` |
| Audit.lean | `5cd3baae128dafcca0c199d2466c8e0afe4fda598db560508923ec9f58d3afc5` |
| Check.lean | `36f83c3a3f3ff7585c3719d0cf13b1b2cefbc33f522f2f7c491bcda87ea129f6` |
| lakefile.toml | `84f37b7adb414c5343176d19e5c210c88c383b61e4e5d88174fbbb6a5d9897c7` |
| lake-manifest.json | `3ff7111b74eeb1e3c1181006d54a8a96719eb99f9380c1bbbe4b8bb3eb571c54` |
| lean-toolchain | `55e97be96000b5e9e290c9e74482e5e317861499a5540353ce845471bded8cea` |

All nine dependency repositories' revisions match the pinned manifest and their tracked working trees were clean. No candidate compiled output was copied into the review build. `fresh-input-verification.json` records the checks. Frozen file hashes were rechecked after the audit in both the author/coordinator project and the independent copy and remain unchanged.

## Fresh execution

The independent runtime is Lean 4.19.0 at `/private/tmp/tlmc310-runtime/lean-4.19.0-darwin_aarch64/bin`. `run_fresh_build.py` records every command, output, hash, and actual exit code in `fresh-build-execution.jsonl` and separate stdout/stderr files.

| Run | Actual exit code |
|---|---:|
| Runtime version | 0 |
| Fresh full `lake build` | 0 |
| Strict Conjecture7744.lean replay and fresh .olean | 0 |
| Strict Audit.lean replay and fresh .olean | 0 |
| Strict Check.lean replay and fresh .olean | 0 |

All strict runs use `-DwarningAsError=true`; the package configuration also enforces it. All stderr files are empty. The core proof module produces no warnings or diagnostics. The audit/inspection modules print the expected declarations and axiom lists.

## Model and definition review

Every source definition, theorem, and instance was read, and its compiled declaration type was checked. The 19 authored definitions have the following actual meanings, with no substitute observable or artificial probability model:

| Definitions | Semantic check |
|---|---|
| `RegularGraph` | Subtype of all Mathlib `SimpleGraph V` with every degree equal to d; no block-graph, connected-component, or chosen-graph restriction. |
| `quadraticTrace` | Actual matrix square of a scalar multiple of adjacency, then trace multiplied by b. |
| `uniformGraphs` | `PMF.uniformOfFintype` on the entire nonempty finite regular-graph subtype. The separate mass theorem gives equal mass at every graph. |
| `quadraticExpectation`, `quadraticFluctuation` | Genuine uniform-measure integral and its centered trace, multiplied by the real square root of the vertex count. |
| `quadraticLaw`, `zeroLaw` | Probability law obtained from the actual fluctuation and the real Dirac probability measure at zero. |
| `polynomialTrace` | `Polynomial.aeval` of a real polynomial at the actual scaled adjacency matrix, followed by normalized trace. |
| `polynomialExpectation`, `polynomialFluctuation`, `polynomialLaw` | Corresponding actual integral, centered scaled trace, and probability law for arbitrary real polynomials. |
| `jointFluctuation`, `jointLaw` | Actual vector of trace fluctuations for any finite polynomial list and its probability law. |
| `coordinateLaw` | Pushforward of a vector probability measure by the usual coordinate evaluation map. |
| `BlockVertices`, `blockGraph` | Finite product label sets and within-block complete graphs used only to show regular graph sample spaces exist at an unbounded family of sizes. |
| `lawVariance` | Mathlib variance of the identity random variable under the specified real probability law. |
| `claimedVariance` | Exactly the source's `4 - 12/d + 8/d²`, with d cast to the reals. |
| `RequiredSecondOrderLimit` | A necessary part of the source claim: existence of all finite-dimensional weak limits, plus the prescribed x² marginal variance. It deliberately omits additional Gaussian and covariance requirements, so disproving it suffices. |

The four instances furnish the finite regular-graph space, its all-subsets sigma algebra, the product vertex-set finiteness, and the nonempty regular-graph sample spaces. None assumes the desired contradiction or a limiting law.

The conventional uniform simple-graph interpretation is explicit and appropriate. The source does not specify a multigraph/configuration ensemble or require connectedness. A report must retain this stated interpretation and must not advertise a theorem for looped/multiple-edge adjacency matrices from this argument.

## Theorem-by-theorem semantic chain

1. `quadraticTrace_eq` uses the standard adjacency identity `(A*A) v v = degree v` and actual graph regularity to prove `b*a²*n*d`. The theorem is universal over every graph in the sample space.
2. `uniformGraphs_mass` verifies the actual uniform model.
3. `quadraticExpectation_eq` integrates the constant trace under that probability measure.
4. `quadraticFluctuation_zero` subtracts this actual expectation. `finite_quadratic_variance_zero` separately records the finite variance.
5. `quadraticLaw_is_pushforward` relates the PMF construction to ordinary measure pushforward. `quadraticLaw_eq_zeroLaw` proves exact equality of probability laws, not merely equality of variances.
6. `polynomialTrace_square`, `polynomialTrace_integrable`, and `polynomialFluctuation_square` connect the genuine polynomial process and expectation to the quadratic coordinate, with integrability on the finite sample space.
7. `polynomialLaw_is_pushforward`, `polynomialLaw_square`, and `jointLaw_is_pushforward` connect these genuine laws to the intended random variables and to x².
8. `jointLaw_coordinate` proves the coordinate marginal formula. `coordinateLaw_tendsto` uses Mathlib's continuous-pushforward theorem for probability measures, so the finite-dimensional limit implies the required scalar limit.
9. `blockGraph_regular`, `blockVertices_card`, `blockVertices_card_pos`, and `blockVertices_card_tendsto` establish actual admissible nonempty model sizes, positive size, and divergence to infinity.
10. `zeroLaw_variance` computes the variance of the real Dirac law. `quadraticLaws_tendsto_zero` proves weak convergence of the exact constant sequence of laws. `quadratic_weak_limit_variance` uses Hausdorff uniqueness of that weak limit to identify it with Dirac zero before computing its variance.
11. `claimedVariance_three` proves the source formula is 8/9. `no_claimed_quadratic_limit` derives the numerical contradiction.
12. `no_required_second_order_limit` formally projects the finite-dimensional x² law to its scalar marginal and invokes that contradiction. `conjecture7744_false` specializes to adjacency scaling 1 and empirical trace normalization 1/n.

This accounts for all 26 authored theorems. In particular, no unjustified interchange of a variance and a weak limit occurs. Although Mathlib defines real variance using the extended variance's `toReal`, that convention cannot manufacture the result here: the limit measure itself is proved equal to Dirac zero, which has a finite second moment.

## Labeling and asymptotic bridge

At d=3, `BlockVertices 3 k` has `4(k+1)` vertices. The block graph gives one cubic graph on each such label set; the sampled ensemble remains every cubic simple graph on it. The label set has the explicit ordinary bijection `(i,j) ↦ 4i+j` with a standard four-multiple vertex set. Label names impose no restriction on edges or graphs.

Any asserted all-admissible-size limit must retain the same limit along this unbounded subsequence, and finite-dimensional convergence implies marginal convergence. `RequiredSecondOrderLimit` is consequently a weaker necessary assertion, not an unrelated stronger conjecture. It is not defined as a bare numerical equality or by inventing a zero observable.

As a further independent diagnostic, review-only `ReviewerBridge.lean` compiled strictly with exit 0. It proves from the candidate's graphwise quadratic-law theorem that the same contradiction holds for **any sequence of finite label sets** whose cubic regular-graph spaces are nonempty; the product-label choice is dispensable. It also independently compiles the usual convergence reindexing step using `blockVertices_card_tendsto`. Both reviewer theorems have only the three standard logical axioms. Their outputs and hashes are retained separately, and neither modifies the frozen submission.

The proof refutes the prescribed positive variance, not the possibility of a degenerate Gaussian coordinate. No Kesten–McKay convergence theorem, other covariance count, or comparison to a GUE normalization is needed to negate this mandatory scalar consequence.

## Complete compiled inventory and axiom closure

The reviewer independently wrote and executed `InspectCompiled.lean`. It discovers declarations by owning imported module, rather than relying on the authored-name list or namespace suffixes alone. It records each full compiled type, body, direct dependencies, transitive dependency closure, axioms, unsafe/partial dependencies, and missing constants in `compiled-declarations.json`.

The inventory contains **83 declarations: 49 explicitly authored and 34 generated**. Among them are **75 logical declarations**, all with axiom dependencies contained in `{propext, Classical.choice, Quot.sound}`, with no unsafe, partial, or missing logical dependency. There are no locally declared axioms or axiom stubs. Every generated logical proof/equation body was inspected: they are reflexive defining equations, extracted graph symmetry/looplessness proofs, finite-set simplifier facts, finite/probability/measurability instances, and numeric/finite-index side conditions. None is a hidden admission.

The remaining eight entries are actual compiler runtime artifacts whose bodies were individually inspected, not merely accepted by a naming convention:

| Runtime entry (all prefixed `Conjecture7744.`) | Inspected body and classification |
|---|---|
| `blockGraph._cstage1` | Graph constructor with the exact same adjacency relation; extracted proof fields replaced by standard compiler `lcProof` erasure markers. |
| `blockGraph._cstage2` | Erased runtime graph constructor with `_obj`/`_neutral` compiler placeholders. |
| `blockVerticesFintype._cstage1` | Product of the two ordinary `Fin.fintype` enumerations. |
| `blockVerticesFintype._cstage2` | Runtime finite ranges and their multiset product. |
| `blockVerticesFintype._closed_1._cstage2` | Cached runtime finite-range lambda. |
| `regularGraphMeasurableSpace._cstage1` | Projection of top from the standard measurable-space complete lattice. |
| `regularGraphMeasurableSpace._cstage2` | Erased runtime projection of that same lattice. |
| `regularGraphMeasurableSpace._closed_1._cstage2` | Cached runtime lattice value. |

Lean's standard `Lean/Compiler/LCNF/ToLCNF.lean` explicitly documents its use of `lcProof` to erase nested proofs. The runtime closure data honestly retain this marker and unresolved erased compiler placeholders. **None of these eight entries, `lcProof`, or the erased placeholders occurs in any logical declaration's proof dependency closure.** Therefore these runtime data do not weaken the kernel-checked proof. It would be inaccurate to say that every compiler data entry is a logical declaration with only the three standard axioms; the narrower complete logical-closure result above is what was checked.

The independent compiled inventory SHA256 is `e272669442d23fd8b3cdad5a4111719dd0cfddfa7d59bf5a5cc59a8dfea3fd63`. Execution and summary evidence are in `compiled-inspection-execution.jsonl` and `compiled-review-summary.json`. Supplemental raw source scans found no admissions, native_decide, custom axioms, unsafe author code, external proof overrides, or implemented-by substitutions in the three frozen source modules.

## Auxiliary code and provenance

The finite enumeration script already passed the independent audit documented in `finite-support-review.md`, including a different exhaustive edge-mask enumeration. That computation supports finite examples only.

The author's historical `verify.py` was fully inspected. It checks pinned dependencies, authorized input hashes, the original five-file project inventory, whitespace, source tokens, and the 49 authored audit names. It is not a mathematical oracle. Because `Check.lean` was subsequently added by the coordinator, replay used a separate copy of the original five files and exactly two documented path substitutions: the project root and the output JSON path. No logic changed. The adapted run exited 0, produced empty stderr and exactly the original result hash `e4ceb60b8817084713fe27ba7305f7d835928ba52e723ce584522fa9f7e9641b`, and the author's original verification output remained unchanged. Original/adapted scripts, a unified diff, stdout/stderr, and the receipt are retained.

The author's `run.py` was inspected as an execution wrapper, together with all entries of `commands.jsonl`. It captures subprocess exit status and merged stdout/stderr, adds a source snapshot in its final version, and does not supply mathematical facts. Historical failed commands are honestly logged. Their earlier source snapshots were not retained, so this reviewer does not claim to reproduce those historical failures or to reconstruct their missing contemporaneous inputs. The final frozen sources were instead independently rebuilt and inspected as described above.

## Remaining gate

No blocking mathematical, formalization, execution, or source-provenance finding was identified in this frozen candidate. Full LaTeX report/source review, every PDF page, final artifact inventory, and any final distributable verifier still need their separate review before complete submission acceptance. No publication or repository mutation was performed by this reviewer.
