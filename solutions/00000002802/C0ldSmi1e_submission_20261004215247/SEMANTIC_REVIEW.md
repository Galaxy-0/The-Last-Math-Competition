# Independent semantic review — conjecture 00000002802

**Decision: PASS for the exact reviewed materials.** The formal development and report give a faithful disproof of the necessary implication from interior twice differentiability of the actual Cramér convex dual to a non-lattice underlying distribution. Consequently they refute the stated criterion. No mathematical or semantic correction is required for the reviewed bytes.

This reviewer authored or edited none of the proof, mathematical report, README, verification documentation, or execution/eligibility/PDF records. I read the exact English and Chinese conjecture, both complete current contribution guides, the earlier independent preassessment, every submitted Lean source and configuration file, the complete final LaTeX report, README and verification document, and the execution, PDF and eligibility evidence. I independently recomputed all 21 final input hashes listed below. This is independent internal scrutiny, not maintainer acceptance. Final staging, remote publication and any later changed bytes remain outside this review.

## Logical correspondence with both language versions

Let D denote the differentiability assertion and N the non-lattice assertion. The English equivalence entails D implies N. Reading the Chinese as D iff (N and its additional variance assertion) has the same necessary consequence; taking the variance phrase as an accompanying clause also has that consequence. Thus a lattice law satisfying D refutes the stated criterion regardless of the unspecified variance-functional phrase. The submission accurately limits its conclusion to this failed necessary implication. It neither purports to settle the converse nor assigns or separately proves a meaning for the variance or periodic-correction clauses.

The universal wrappers retain an actual probability-measure hypothesis, all real exponential moments, and nondegeneracy. Restricting a putative universal necessary implication to this subclass weakens that consequence, and the witness still refutes it. These restrictions are not attributed to the original source. The final `necessary_criterion_fails_all_three_readings` has the intended three negated necessary implications, and `explicit_counterexample` packages an actual measure with the required properties. The proof does not merely show that an independently chosen auxiliary function is smooth.

## Probability, lattice and convex-dual objects

`fairBernoulli` is the ordinary Borel real measure consisting of equal Dirac masses at zero and one. Its named probability instance proves total mass one; separate theorems prove the two singleton masses, almost-everywhere reduction to the two atoms, and failure of almost-sure constancy. This is the actual nondegenerate fair Bernoulli law. No additional bridge through a Boolean PMF is needed to identify it.

`LatticeLaw` means concentration almost everywhere on a translated integer lattice with positive spacing. The witnesses zero and one for the offset and spacing, with integer coordinates zero and one for the atoms, prove precisely that condition. Non-lattice is its negation. Positive spacing is explicit, and neither greatest-span conventions nor a numerical surrogate are used.

I inspected the pinned Mathlib `mgf` and `cgf` definitions: they are the real exponential integral and its logarithm. `integrable_exp_fairBernoulli` proves every required integrability hypothesis against the actual measure. The moment formula `(1 + exp t)/2` is derived using the integral's Dirac, scaling and addition identities. Its logarithm is therefore the actual cumulant function.

`cramerRate` is an EReal supremum over precisely the real tilts with an integrable exponential integrand. This restriction correctly avoids using the library's totalized value zero for a nonintegrable real integral and its logarithm. For the concrete law, every real tilt is admissible, and an explicit theorem identifies the restricted supremum with the full real-parameter supremum. The generic zero-tilt theorem proves nonnegativity for probability measures, so the finite-domain predicate does not conceal negative infinity.

## Computation of the actual supremum and its domain

The auxiliary `binaryRate` is introduced separately from the rate. For every real tilt, the logarithm-concavity proof gives an upper bound by that expression at every point of (0,1). I checked the positive arguments and weights: the weighted sum of exp(t)/x and 1/(1-x), with weights x and 1-x, is exp(t)+1. All logarithm identities have the necessary nonzero or positive hypotheses. The explicit tilt log(x)-log(1-x) attains equality. The two supremum inequalities prove equality of the actual EReal convex dual with the finite real formula; there is no assumed optimizer or substituted definition of the rate.

For x<0, negative tilts and the cumulant bound Λ(t)≤0 make the objective arbitrarily large. For x>1, positive tilts and Λ(t)≤t do the same. The Lean proofs choose a tilt separately for each arbitrary real threshold and use the order characterization of EReal positive infinity. These are statements about the same actual convex dual, not an independently assigned exterior value.

The finite formula gives (0,1)⊆E, and the exterior-infinity theorems give E⊆[0,1], where E is the effective domain. Interior monotonicity then proves int(E)=(0,1). The report correctly claims only this sandwich and interior equality. Neither endpoint values nor equality of the complete effective domain with [0,1] is claimed as a formal result.

## Distinct support readings and differentiability

The open-neighborhood definition of `topologicalSupport` is the standard real topological support of a measure. The atomic mass proofs and the open complement of {0,1} establish that the support is exactly {0,1}. Its ordinary real interior is empty. The literal certificate there is correctly labelled vacuous in the proof comments, report, README and verification documentation.

The convex hull of that support is separately proved to be [0,1], whose interior is (0,1). The effective-domain interior is also (0,1), by the preceding argument. Both are nonempty, with the explicit point 1/2. The substantive regularity statement applies to these nonempty interiors. No ordinary support is silently redefined as convex support.

Ordinary logarithm calculus proves `ContDiffOn ℝ ∞ binaryRate (Ioo 0 1)`. I checked the pinned notation: ∞ denotes smoothness of all finite orders and is distinct from the analytic order ω. Positivity of x and 1-x supplies the logarithm side conditions. The rate is equal to the EReal coercion of this smooth real function throughout the open interval; the proof never projects infinite EReal values to a totalized real value.

`RateC2On` is explicitly a stronger sufficient certificate. `RateTwiceDifferentiableOn` requires a real representative and differentiability of both it and its ordinary derivative on the region. The bridge from C² explicitly requires that the region be open and uses the library's ordinary-derivative theorem for open domains. On such a domain, equality with the actual finite rate holds on a neighborhood of each point, so this certificate describes the rate's own local twice differentiability. No equivalence between mere twice differentiability and C² for arbitrary functions is asserted. All three final regions are interiors and hence open, including the empty literal one.

## Formal verification and report agreement

I independently counted 62 source declarations: 13 definitions, 48 theorems, and one named probability instance. Every definition appears in the print audit, and every theorem and the named instance appears in the type and transitive-axiom audit. In particular, `fairBernoulli_isProbabilityMeasure` is not omitted as an implicit trust assumption.

I reviewed the actual independent build and Check output and the full structured execution evidence. The separate executor copied the nine frozen source/configuration files into a fresh project directory and shared only cached dependencies. The default build succeeded; all six source files, including Check, then passed direct replay with warnings treated as errors. I cross-checked that the emitted Check output equals `axioms.txt` and that both source and copied file hashes equal the frozen map. All 49 distinct axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`. My source screen and the executor's broader masked-code scan found no admitted proof, custom axiom, `native_decide`, or execution/kernel bypass. The nine manifest dependency revisions and tracked-clean states were checked before and after, as was the Lean compiler identity.

The execution record finished at 2026-10-04T21:42:42.258869+00:00, under Lean 4.19.0 and Mathlib v4.19.0. I reviewed those execution results; I do not claim to have independently rerun the separate executor's complete build. The exact submitted Check and reproduction commands permit the audits to be repeated.

The complete final report agrees with the definitions, inequalities, optimizer, infinity arguments, domain sandwich, support distinctions, regularity bridge and final quantifiers. Its description of omitted endpoints, unspecified clauses and formal scope is accurate. The source expressly specifies the convex-dual form; constructing an infinite independent process or re-proving the full Cramér large-deviation principle is unnecessary for this analytic counterexample, and no such formalization is claimed. No auxiliary numerical, simulation or symbolic code supplies a mathematical step.

I independently consulted Markus Fischer's primary lecture notes, *Large deviations, weak convergence, and relative entropy*, revised 20 June 2013, §2.3, pp. 6–7. They corroborate the integral-based convex dual and Bernoulli formula used here. This is an object-identification cross-check; no external result is imported as an unproved Lean assumption. [Primary source](https://www.math.unipd.it/~fischer/Didattica/WeakConvergenceRE.pdf).

## PDF and eligibility evidence

The final LaTeX, PDF and verification records have matching identities. The PDF is 4 pages and 66,515 bytes. The record documents successful native compilation and Tectonic export. I checked the saved export log for warning, error, box and missing-character diagnostics; none is present. I recomputed the four rendered-page hashes and checked that they agree between the author and coordinating agent's separate all-page visual-review records. Both report no clipping, overlap, missing glyphs or problematic page breaks. This review consumes their actual visual evidence and verifies its identity; it does not claim a third personal visual inspection.

The initial eligibility record covers 572 all-state PRs through PR576 and 45 classified topic leads. The final refresh covers 586 PRs through PR590, with all fourteen new full bodies classified by the corpus agent and independently by the coordinating agent. The 46 resulting topic leads are recorded as unrelated. All 45 prior lead identities and all 135 freshly fetched discussion responses match their earlier reviewed bytes. The fresh source and both full-guide hashes match the copies I read, metadata remains unsolved, and no current or historical solution-path or identifier match is recorded. The refresh is checked through 2026-10-04T21:45:03.708437+00:00. I reviewed these records, classification reasons and their consistency; I did not rerun their full remote-search workflow. Timestamp and GitHub indexing limitations are stated accurately.

The reviewed materials satisfy the mathematical and local verification obligations in the contribution guides. The intended package contains the required LaTeX source, matching PDF, complete pinned Lean project and verification material, and requires no mathematical auxiliary program. Publication must preserve these exact bytes and the prescribed personal-submission-only scope. The separate final package manifest and Git/remote checks are assembly and publication controls, rather than claims made by this semantic review.

## Exact final inputs

The following are package-relative paths. Every SHA-256 was independently recomputed from the corresponding frozen source path in `/private/tmp/tlmc2802-review-inputs.json`; all 21 matched. This table excludes this review itself and the later package manifest to avoid a circular identity claim.

| Package input | SHA-256 |
| --- | --- |
| `lean/Conjecture2802/Law.lean` | `5371b69f5e2c75a3db077507a6a0607f61978c8fe9898b22277412d3facc6707` |
| `lean/Conjecture2802/Formula.lean` | `17aea3d3c0448ae243de5107e86e74d620db36455fac8556777ed4514e0fd091` |
| `lean/Conjecture2802/Transform.lean` | `d484c5c1c66cbfee6b231fae2620991f56fd27acff2c0d19ba686ee650ea423d` |
| `lean/Conjecture2802/Regularity.lean` | `8254e9f00f4a574b4293f4d1b6fcaec9d3c81e626206b8aeee387022bbf258ea` |
| `lean/Conjecture2802.lean` | `9d3b1af90220e4469adac3b3c2a3eceb9509e5ffe069cf99d443bc08a56991ae` |
| `lean/Check.lean` | `e010117bd01a983ce5dec88e6b799e1ae031fa97ccbd80e081b5eadfb12b73f1` |
| `lean/lakefile.toml` | `139d77b2432e6fece9416bbea4ddeccffa7ee85e1a493fe16b63098c92b3d74b` |
| `lean/lake-manifest.json` | `bf70b08ac67109e303ee4a5cc7168b68799e60b8cb5fb88cb081185bac299bda` |
| `lean/lean-toolchain` | `55e97be96000b5e9e290c9e74482e5e317861499a5540353ce845471bded8cea` |
| `conjecture.md` | `b8ac469c25ef747b6574cd17d41043cc442caf35dbcacc4fe58c7d37f1b8a3eb` |
| `main.tex` | `ae973e03bee78c8198db83c2450d2d3119a2cad61c88bbb332d605071b70ca31` |
| `main.pdf` | `44a5e485183c7cd1df70ad4810e7c9e481c62552bf7e4c010bc5a1fed27fe94e` |
| `README.md` | `44f4777cb40b430630991972e04a75ba8c67d226ace4050802ea5c3426790d9c` |
| `VERIFICATION.md` | `b614625cf2160bda37838ad0cbcc33bff241be8b397c80771c739c75d5993a82` |
| `verification/strict-replay.json` | `b460b6cee5ac35801aa3a9548c39bf1f47be628db72294add14c7ba871155963` |
| `verification/build.txt` | `afe255d3406ea2429e02386b2ecd516067f64f3f1615dc8b5a17cb6f510635f5` |
| `verification/axioms.txt` | `94d0d8255f8b0d80f214acff0ea00252c322fbc6034fccbe9a0acbdd8c63c855` |
| `verification/pdf.json` | `e520b016bc50560be307470fba249b8fbd5127020f1a2a947c16dda855787726` |
| `verification/report.txt` | `fa3f27c45b750f2c2c6f5a1e4344b85873c43afc7f6d0aaf3445a26f6887b901` |
| `verification/prepublication.json` | `6341141c750c9960c23897cbde3b407884057b6a130e484c16a80519f18b8ab8` |
| `verification/eligibility.json` | `4e3663e955b0fa78415bdfabb5d43279d974470669ab3beacc3d2a23b76963f5` |

Additional read-only context was inspected outside the submitted package:

- `/private/tmp/tlmc2802-eligibility-current/upstream-README.md` — SHA-256 `cd54d17f51e08212ee9557ef74568f6f2c388279ac74339dc4a3bab7c283f27e`.
- `/private/tmp/tlmc2802-eligibility-current/upstream-README.zh-CN.md` — SHA-256 `ffedf1385079b9741fce4176c7aa1662720c29391116b34e5e78ba154b4fa244`.
- `/private/tmp/tlmc2802-semantic/preassessment.md` — SHA-256 `d54b20e6fe58962b2cbfe9e2450b598012524ea118fa2af295bf0dbbfc66f216`.
- `/private/tmp/tlmc2802-frozen-sources.json` — SHA-256 `170cf7efb5aade414ea11687a6da18ede287b8850dc734a4834f6eedaa0e3119`.
- `/private/tmp/tlmc2802-review-inputs.json` — SHA-256 `53d9ce5a8caefe9b9c7e603a593c70d30e78d82cd4e77ff73e9055a7c89a5420`.

Review completed at 2026-10-04T21:52:03.513479+00:00.
