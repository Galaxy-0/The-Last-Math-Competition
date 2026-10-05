# Independent semantic and frozen-artifact review: conjecture 00000000989

**Verdict: PASS under the disclosed standard positive-map interpretation and square-system convention.** No blocking mathematical, formal, report, or frozen-input integrity issue was found. This is independent internal review, not maintainer acceptance or publication eligibility.

Reviewer: nonauthor `review_989` agent, 2026-10-05 UTC. I supplied a candidate-free terminology preassessment before a proof existed. I did not author, edit, or repair the proof or report. After freezing, I checked the actual Lean source and compiled declarations; the author's correspondence served only as explanatory material.

The review and execution described below were completed before this file was saved. Saving was initially blocked by automatic approval review. After the user explicitly approved continued submissions and their required verification, I reconfirmed all 33 frozen input hashes at `2026-10-05T05:00:47.956574+00:00` and saved the completed review. The original execution times are retained; no earlier check is presented as newly rerun.

## Identities and coverage

Review manifest: `/private/tmp/tlmc989-review-inputs.json`

SHA-256: `8e35ae4ed1822a4b8c18d85a0ea570ef6ea1b4375ca441b31560c88d0875788a`

All **33 frozen inputs** matched their manifest hashes before review and after the independent checking commands. The manifest also remained unchanged. The original final integrity check was recorded at `2026-10-05T04:47:09.465609+00:00`; all 33 hashes were reconfirmed unchanged at the later save-time check above.

| Principal input | SHA-256 |
| --- | --- |
| Bilingual conjecture | `69eb8b98adec657b4781a539de86eca88f07ceeeb172a02fc6e593437bf2961d` |
| Complete English guide | `84cd9992c3b4027d90044109df969e22390051df4a5f7f21ca81138e5f717795` |
| Complete Chinese guide | `167c69fba1d5592feb55117da9a0151b0355ff6b2a0fb773115f367e58c59b47` |
| `Conjecture989.lean` | `9e6f1931a63c9b206a27162e375b9aafe24ffac320bb8a1bb5872254c6a1206c` |
| `Check.lean` | `c133470b2874789b19b2fa085d3078f0ab668c160662068eda5bd984ff1ff38f` |
| `lakefile.toml` | `f0903db69ccbd204a093c63283bd3d273254da8e19bf19d4832e3dd7f70ed049` |
| `lake-manifest.json` | `31911c673ba6abc5a3f0548f50bcf57bd4e27ba40873a4bb7f31c88500dc59b8` |
| `lean-toolchain` | `55e97be96000b5e9e290c9e74482e5e317861499a5540353ce845471bded8cea` |
| `main.tex` | `4fcc3b0b8bd08967d48aa61deaa83153cfe06a9aaaddfbabe662bcc8b4163a1a` |
| Frozen `main.pdf` | `9d71982a4eb875026270c3afcccbf02a6e66f80114df008021f2dd4c599cc894` |

I read the exact bilingual statement, both complete guides, all 229 lines of mathematical Lean source, the entire 142-line LaTeX report, audit source and project configuration, package README, verification narrative, author correspondence, preassessment, and every manifest-listed textual source, inventory, script, and log. Repeated JSON fields were checked against the separately read complete transcripts and inventories. I viewed both complete PDF page images and read the complete extracted text.

No other competition problem or previous mathematical submission was used in the review. The eligibility record was treated as operational context; metadata was not mathematical evidence. Publication eligibility remains a separate responsibility.

The required report, PDF and Lean project are present. The proof is symbolic and has no external numerical premise. Inspection programs were read and their relevant operations independently executed. No frozen input or repository file was modified.

## Interpretation and limitations

The accepted reading is a complex-linear map `M_d(C) -> M_d(C)`, with positive integer matrix side length `d`, and positive-map indecomposability. Both languages omit independent source and target dimensions, the dimension range and family indexing. The submission discloses its conventions.

**The checked Lean theorem concerns square systems. It does not quantify over independently varying rectangular source and target dimensions.** The report's broader elementary observation about maps between matrix algebras is mathematically valid by its argument, but that extra breadth is not attributed to the Lean theorem.

Decomposable means a sum of a completely positive map and output transpose composed with another completely positive map. Zero summands are permitted. This matches Müller-Hermes, *Decomposable Pauli diagonal maps and Tensor Squares of Qubit Maps*, arXiv:2006.14543v1, Section 1's initial definitional sentences. Section 2 fixes ordinary transpose and the input-first Choi convention. Those primary passages were independently checked during preassessment. [Definition source](https://arxiv.org/html/2006.14543#S1).

“Indecomposable” can denote other properties in other settings. Extreme rays, extreme points of specified normalized convex sets, and invariant direct-sum indecomposability are different predicates. Neither bilingual statement identifies those alternatives. The report distinguishes them explicitly. This review does not certify those alternate questions or eliminate the original editorial ambiguity. The positive-map interpretation is standard and faithful in this context; its use is not a circular stipulation of nonexistence.

“Extremal Choi rank” supplies no optimization class or definition of map extremality. Retaining the exact numerical rank condition is appropriate. The obstruction excludes all completely positive indecomposable maps under the chosen semantics before imposing rank. No unitality, trace preservation, nonzero-summand condition or alternate rank is introduced.

The central obstruction holds for every natural dimension. The conjecture specialization requires `d > 0`, so it does not exploit dimension zero or truncated subtraction. The family theorem requires a nonempty index type and permits varying dimensions. Excluding every nonempty family also excludes explicit ones without an artificial explicitness predicate. The helper theorem is universe-polymorphic; the final packaged existential uses `Type`.

## Semantic audit

1. **Actual complex maps and PSD.** `Mat d` is `Matrix (Fin d) (Fin d) Complex`; `MatrixMap d` is an actual complex `LinearMap`. `Positive` preserves `Matrix.PosSemidef`. `posSemidef_iff_quadratic` proves the Hermitian and nonnegative-real, zero-imaginary quadratic-form interpretation. The pinned library definitions of PSD, matrix rank and transpose equivalence were also inspected.

2. **Actual ampliations.** `block` extracts the stated block with its index first. `amplification` contains proved addition and scalar laws. `amplification_apply` gives the complete entry formula. `amplification_kronecker` proves `B ⊗ A -> B ⊗ Phi(A)` using genuine library Kronecker products. `block_kronecker_expansion` spans every block matrix by these products. Together these establish the actual ampliation on its full domain. Complete positivity quantifies over every positive finite level and every PSD input. Its implication to positivity is proved at level one.

3. **Actual transpose and map operations.** `transposeMap` is the complex-linear library transpose equivalence. Its entry theorem gives `A[j,i]` without conjugation. `decomposition_apply` exposes actual map addition and composition. `Decomposable` quantifies over actual maps of the same source and target using the cited output-transpose convention. `Indecomposable` means positivity and failure of that decomposition. No input/output convention conversion is assumed.

4. **Complete proof.** `amplification_zero` identifies the actual zero map's ampliation with zero; `zero_completelyPositive` uses the verified PSD zero theorem. `CompletelyPositive.decomposable` supplies the given map and zero as witnesses and proves their map equality. `not_indecomposable_of_completelyPositive` follows. The report uses the same argument. No unproved Choi or Kraus characterization is required.

5. **Genuine Choi rank.** Matrix units are actual library standard matrix units. The entry and sum theorems identify the unnormalized matrix `sum E_ij ⊗ Phi(E_ij)`. `choiRank` is its actual complex matrix rank, exposed as the complex dimension of the image of its multiplication map. The size and usual rank bound are proved. For `d > 0`, `rankCondition_iff_corankOne` proves equivalence of rank `d²−1` with rank plus one equal to `d²`. The rank convention agrees with Girard et al., *On the mixed-unitary rank of quantum channels*, Section 1, printed page 2, equations (1)–(3) and following text; its tensor factors are exchanged. [Rank source](https://cs.uwaterloo.ca/~watrous/Papers/MixedUnitaryRank.pdf).

6. **Final negation.** `ConjecturedMember` retains positive dimension, complete positivity, indecomposability and genuine Choi-rank equality. `no_conjectured_member` negates that conjunction. `no_nonempty_family` selects a member of any nonempty family and applies the individual obstruction. `conjecture989_false` packages the negated existential. There are no circular definitions, surrogate tags, hidden impossible premises, empty-family tricks or metadata dependencies.

## Independent execution

I read the frozen verifier in full and ran a reviewer-local copy with only its fresh-build and output directories relocated. It created `/private/tmp/tlmc989-semantic/fresh-lean` from the two frozen sources and three configuration files. No build directory existed beforehand, and **no candidate `.olean` files were copied**.

The permitted shared dependency cache and existing runtime were reused. Dependencies were not rebuilt from scratch; the normal Lean kernel, runtime and trusted cache remain the ordinary trust boundary.

Compiler: Lean 4.19.0, `arm64-apple-darwin23.6.0`, release commit `6caaee842e9495688c1567e78c0e68dbb96942aa`. Identity was checked before and after execution and after the full-name audit.

All nine dependency revisions matched the manifest, with clean tracked files before, after the build/audits, and after the final original review commands:

| Dependency | Revision |
| --- | --- |
| mathlib | `c44e0c8ee63ca166450922a373c7409c5d26b00b` |
| plausible | `77e08eddc486491d7b9e470926b3dbe50319451a` |
| LeanSearchClient | `25078369972d295301f5a1e53c3e5850cf6d9d4c` |
| importGraph | `e6a9f0f5ee3ccf7443a0070f92b62f8db12ae82b` |
| proofwidgets | `c4919189477c3221e6a204008998b0d724f49904` |
| aesop | `5d50b08dedd7d69b3d9b3176e0d58a23af228884` |
| Qq | `fa4f7f15d97591a9cf3aa7724ba371c7fc6dda02` |
| batteries | `f5d04a9c4973d401c8c92500711518f7c656f034` |
| Cli | `02dbd02bc00ec4916e99b04b2245b30200e200d0` |

Fresh execution ran from `2026-10-05T04:44:04.937277+00:00` to `2026-10-05T04:44:25.934674+00:00`.

| Check | Result |
| --- | --- |
| `lake build` | Exit 0; 7.222 s |
| Strict complete `Conjecture989.lean` replay | Exit 0; 1.513 s; no output |
| Strict complete `Check.lean` replay | Exit 0; 4.369 s |
| Both replays with `pp.fullNames` and `pp.universes` enabled | Exit 0; complete output read |
| Module-origin inventory | Exit 0; 7.466 s; 43 constants |
| Source inventory | 13 definitions/abbreviations, 22 theorems, zero authored named instances |
| Bypass scan | No hits |
| Final frozen-input hashes | All 33 unchanged |

The strict commands used `lake env lean -DwarningAsError=true`; the additional replays enabled `-Dpp.fullNames=true -Dpp.universes=true`.

The exhaustive environment audit selects actual originating modules, not namespace prefixes. Every constant has its full type, kind, safety and partial flags, and transitive axiom closure recorded. All 43 constants are safe and nonpartial, with no custom axiom declarations or runtime compiler constants. Their closures contain only `propext`, `Classical.choice`, and `Quot.sound`, or subsets thereof. The 22 theorem audits agree with the environment audit; all authored definitions are also covered.

The eight generated/additional constants are:

- `Conjecture989.Decomposable._proof_3`
- `Conjecture989.amplification._proof_1`
- `Conjecture989.amplification._proof_2`
- `Conjecture989.block.eq_1`
- `Conjecture989.choiMatrix.eq_1`
- `Conjecture989.choiRank.eq_1`
- `Conjecture989.matrixUnit.eq_1`
- `Matrix.kroneckerMap.eq_1`

The last is included despite its different namespace. The generated `RingHomCompTriple` proof is covered and is not an authored instance declaration. The complete fresh inventory matches the frozen types, kinds, flags and closures. Fresh build and `Check` transcripts match the frozen transcripts. Inspection metaprogramming supplies no submitted mathematical proof.

Evidence remains in:

- `/private/tmp/tlmc989-semantic/execution/`
- `/private/tmp/tlmc989-semantic/replay-verifier.py`
- `/private/tmp/tlmc989-semantic/final-integrity.json`

The execution directory contains `strict-replay.json`, `build.txt`, `axioms.txt`, `environment-inventory.lean`, `environment-inventory.txt`, `environment-inventory.json`, `full-names.json`, and both full-name replay logs. These paths describe the review environment, not portable requirements for building the submitted mathematical project.

## PDF validation

I independently exported a fresh copy of the exact frozen LaTeX using the existing Tectonic executable, without changing the frozen report:

```text
/private/tmp/tlmc310-pdf/tectonic --outdir /private/tmp/tlmc989-semantic/fresh-pdf /private/tmp/tlmc989-semantic/fresh-pdf/main.tex
```

Export exited 0, with no warnings or box diagnostics. The LaTeX hash remained unchanged. `pdfinfo` and Poppler rendering succeeded and confirmed two pages.

Fresh PDF SHA-256: `c50d364df7726599281b318fef80e2cc7dc4087b01fb5a7ffdf10998b46ad906`.

This differs from the frozen container hash, so binary PDF identity is **not** claimed. Complete extracted text is identical. Both page PNGs, rendered at the same 1600-pixel scale, are **byte-identical** to the frozen images:

| Page | Frozen and fresh image SHA-256 |
| --- | --- |
| 1 | `b95acac0291d151d07337bebe4473ca7c2be2b99ecf68beb24222e3c559a9520` |
| 2 | `ef0c82fd31e8d560e0db7c274f41338be1e237fdac4d72142abb1e76e4037c8a` |

Both full pages were viewed. Symbols, formulas, proof text, references, commands, margins and pagination are readable, without clipping, overlap or missing content. The complete source, extracted text and visual pages agree.

Evidence remains in `/private/tmp/tlmc989-semantic/fresh-pdf/comparison.json`, with export log, PDF information, complete text and rendered pages alongside it. The frozen native-editor compilation record was read; my independent verification was the fresh export, rendering and text comparison.

## Disposition

**PASS.** The frozen report and checked Lean project establish the negation under the disclosed standard positive-map, positive-dimensional square-system reading. Every preassessment semantic obligation is satisfied. No author revision is required on mathematical or artifact grounds.

The original terminology and domain omissions remain explicit limitations. This review does not certify external acceptance, current publication eligibility, or an unstated extreme-ray, extreme-point or direct-sum reinterpretation.
