# Internal semantic review: conjecture 00000009028

**Verdict: PASS for the frozen proof and report identified below.** The actual counterexamples and final quantified negations are correct. No source or report correction is required. The precise scope is the source's explicit lattice-evenness criterion, under the standard Gram-determinant convention; the report makes this scope visible.

This review was performed by a separate internal reviewing agent. It is not official maintainer acceptance, a competition `review/` decision, or a claim that the undefined portions of the source have been formalized. I read the complete five-file Lean source, all three project configurations, the complete report and README, the exact bilingual conjecture, relevant Mathlib definitions, primary mathematical references, and the completed execution records. I independently checked the recorded source identities and audit inventories. A separate verification agent executed the fresh build and replays; the coordinating agent performed the PDF compilation and visual inspection. Those activities are distinguished from my source and evidence inspection below. I did not modify proof or report files.

## Source interpretation and its limits

Both versions explicitly identify lattice evenness with even determinant. The ordinary characterization reading implies that every even lattice has even determinant. A2 disproves that necessary implication. Because “criterion” can also mean a sufficient test, the second witness independently disproves the sufficiency implication. Thus neither direction of the parity test survives.

The determinant convention is mathematically material: it is the determinant of the Gram matrix of an integer basis, also called discriminant, not the covolume. The report states this. [Nebe's author slides, pp2–4](https://www.math.rwth-aachen.de/~Gabriele.Nebe/talks/lat1op.pdf) explicitly use this determinant convention and define evenness through squared lengths in 2Z. [Elkies's lattice notes, pp1–3](https://people.math.harvard.edu/~elkies/M272.19/sep09.pdf) give the same evenness definition and the correct integral-Gram criterion: even diagonal entries. These definitions agree with the Lean predicates.

The theta weight/character text supplies no modular group, level, or character formula. The proof does not introduce arbitrary replacements for those missing analytic definitions. Its final proposition is named and described as the explicit lattice-evenness clause. Refuting that clause is sufficient against the proposed combined criterion under the literal standard reading explained in the report. This review does not certify a formal theta-series theorem or claim to settle different assertions obtained by adding unstated restrictions. In particular, no odd-rank, unimodularity, or prescribed-level assumption occurs in the source. The [Nebe–Sloane catalogue](https://www.math.rwth-aachen.de/~Gabriele.Nebe/LATTICES/A2.html) independently identifies the exact A2 basis and determinant. [Elkies's modularity notes](https://people.math.harvard.edu/~elkies/M272.19/nov11.pdf) include A2 at level 3, confirming its relevance to the theta context; that analytic fact is background, not a formal premise.

## Honest universal lattice class and parity

`IntegerEven t` means there exists an INTEGER k with t=2*k after casting to the reals. It does not use the vacuous real-number notion of divisibility by two. `IntegralLattice` quantifies over every pair of actual lattice vectors; `EvenLattice` quantifies over every actual vector's inherited self-inner-product. `gramMatrix b` consists of actual basis inner products, and `EvenDeterminant b` applies integer parity to its genuine determinant.

The necessity, sufficiency, and characterization predicates quantify over real inner-product spaces, finite real bases, and the bases' integer spans. This is a standard presentation of full Euclidean lattices. A `Basis (Fin n)` already forces finite dimension. The absence of a separate `IsZLattice` premise is not an omission: Mathlib's `ZLattice.Basic` proves that such an integer span is discrete and spans the full real space (`ZSpan.span_top`, the finite-basis discreteness instance, and `instIsZLatticeRealSpan`). The actual witnesses also instantiate these properties explicitly. A real basis restricts to an integer basis of precisely its integer span, so the computed Gram determinant is the lattice determinant described in the report.

Restricting the proposed criterion to integral positive-definite lattices cannot invalidate these counterexamples: both witnesses lie in that standard subclass, and all required properties are proved. The final negations have no extra assumptions on their witnesses. The predicates do not range merely over assigned Gram tables, named Boolean properties, or degenerate pairings.

## A2 witness

`A2.space` is the actual sum-zero plane inside `EuclideanSpace R (Fin 3)`. Its norm and inner product are inherited from that Euclidean space. `coordinatesEquiv` is the genuine real linear isomorphism (a,b) ↦ (a,-a+b,-b), with inverse given by the first coordinate and the negative third coordinate. No isometry from a coordinate-space norm is falsely assumed.

The mapped real basis has vectors (1,-1,0) and (0,1,-1). `A2.lattice` is their integer span in the plane, and `intBasis` is an actual integer basis. Both real dimension and integer rank are proved to be 2. Discreteness and `IsZLattice` concern the two-dimensional plane, not a false full-rank lattice claim in the surrounding three-dimensional space.

`lattice_coordinates` represents every actual lattice vector in integer coordinates. `integerPairing_eq_inner` proves the explicit integer pairing equals the inherited Euclidean pairing for every pair of lattice vectors. Consequently integrality is established without a finite sampling argument. The self-pairing is twice a²-ab+b² with integer a,b, proving evenness for all vectors. Positive definiteness is proved for every nonzero vector in the real plane, as well as for lattice vectors; it is not only a rational-coordinate positivity assertion.

The integer Gram matrix is defined using the actual integer basis and pairing. `gram_real` connects it to real basis inner products. Both matrices are computed as [[2,-1],[-1,2]], and both determinants are computed as 3. The negation of even real Gram determinant is proved by converting a supposed integer witness into 3=2*k over Z. Thus `a2_even` and `a2_determinant_not_even` genuinely concern the same lattice and basis.

## Diagonal witness and final implications

`Diagonal.plane` is the actual Euclidean plane y=z. `parametrization` maps (a,b) to (a,b,b), with its proved inverse. Its real basis vectors are (1,0,0) and (0,1,1). Their integer span is explicitly discrete and a full lattice in this plane, with real dimension and integer rank 2.

`plane_inner` computes the inherited pairing, and `integral_pairings` obtains integer coordinates for arbitrary lattice vectors from basis representations. The actual Gram matrix is diag(1,2), with determinant 2. Its evenness witness is the integer 1. The first INTEGER basis element is an actual lattice vector of squared length 1. `not_even` applies the universal evenness predicate to that element and derives the impossible integer equation 1=2*k. The plane's positive definiteness is separately verified.

`determinant_not_necessary` instantiates the universal necessity assertion with the A2 plane, basis, integrality, and evenness proofs. `determinant_not_sufficient` instantiates sufficiency with the diagonal plane, basis, integrality, and determinant proof. `both_directions_fail` proves their conjunction. `conjecture_false` negates the full stated parity characterization by extracting its necessity direction. These are genuine quantified negations over the actual lattice class, not simply arithmetic inequalities given conjecture-like names.

## Report and completed verification evidence

The complete report agrees with the formal constructions, integer-coordinate formulas, determinant values, rank statements, and quantified conclusions. Its general explanation of basis invariance and the correct even-diagonal test is standard background supported by the cited definitions; those general background facts are not claimed as new Lean theorems and are not missing premises of the counterexamples. The README accurately states the five replay commands, 28 printouts, and 47 declaration audits. No auxiliary numerical calculation supplies a mathematical fact.

I inspected the completed `strict-replay.json`, `build.txt`, and actual `axioms.txt`. The fresh independent project build and direct strict replays of all five Lean sources succeed, with warnings treated as errors during each direct replay. The copied project initially had no local build outputs. Lean is exactly version 4.19.0, commit `6caaee842e9495688c1567e78c0e68dbb96942aa`; Mathlib is pinned to `c44e0c8ee63ca166450922a373c7409c5d26b00b`. All nine dependency revisions match and tracked trees are clean before and after execution.

My separate checks matched all eight original and independent-copy source/config hashes to the records, matched all 28 requested definition/instance printouts, and matched all 47 actual type/axiom audits to Check (43 theorems and four instances). All axiom lists contain only `propext`, `Classical.choice`, and `Quot.sound`. The bypass scan has no hits. This review inspected those execution results; it did not rerun the compiler itself.

`pdf.json` records native and Tectonic compilation of the exact final report, two rendered pages, and the coordinating agent's inspection of both pages without layout defects. I inspected that record and verified the actual report and PDF hashes below. I did not personally repeat the visual inspection; the visual result is attributed to the recorded inspection.

The exact conjecture and both contribution guides are identified at upstream `4cc82278ba1e5becc4d20b1e2a68dede094e2b8d`. The guide bytes are unchanged from the versions already read during the immediately preceding review. The inspected eligibility evidence records unsolved metadata, no matching prior or pending submission, empty solution-path history, and 528 all-state PR records through #532; incidental topic matches are classified as other conjectures. This is timestamped evidence, not a guarantee against later submissions. Final publication eligibility and path-only package checks remain the coordinating task's responsibility. No official acceptance or merge is asserted here.

## Exact reviewed identities

All hashes are SHA-256. `lean/` labels identify the intended package location and correspond to the reviewed scratch project and verified independent copy. Other labels identify the report, upstream-source copies, or verification records inspected.

| File | SHA-256 |
|---|---|
| `lean/Conjecture9028/Definitions.lean` | `6dcb13785c35a6596401955f95bcc42cff81034ff62c3f57f3b0b52ed35ce56a` |
| `lean/Conjecture9028/A2.lean` | `5730496c7651c588bae7d0b9ff7c6dfd332bd2fb6a0b74266d6bb3674199ef24` |
| `lean/Conjecture9028/Diagonal.lean` | `6f2c26261b1e073f4e0ab5a300444b944ce37178b66b594a3771de2d78b3aa6f` |
| `lean/Conjecture9028.lean` | `c36e61407881f7ffd7d6bab90a3c9bcd85dbb0da04a27553b0d156972739400d` |
| `lean/Check.lean` | `33ccd97107fe2809abc12e05b0a1f6715f17737d0dc22b4f37cf0a9a6ddc685c` |
| `lean/lean-toolchain` | `55e97be96000b5e9e290c9e74482e5e317861499a5540353ce845471bded8cea` |
| `lean/lakefile.toml` | `68b4ea56b506c0005e3902a9f28fbe6710aa2997b14c97d6b71efe4341ea10ea` |
| `lean/lake-manifest.json` | `39f4c889b4307cb6a6bc426e156cf82a864eaf3024dce915f2ddef3b79973a5e` |
| `main.tex` | `2878be51e6beb7f833cfc2b677684513be665c7873cf15885cea352ebc881d6b` |
| `main.pdf` | `e346575e824ce789efc2f57e42cb67a15d599ba21b987712696cd04b3387d0bb` |
| `README.md` | `102aa2c2ea04af0d39ead7d847eee72c0a12f29724431bef7ba416d3f1113df0` |
| `conjecture.md` | `db93326723e787438ef03c494bc77f410e29b766a7491676f3c49dbcbfe13bcb` |
| `upstream README.md` | `f7df38cc270f58a323726aaa98535a26a447a59b801a89dca371460e2f852186` |
| `upstream README.zh-CN.md` | `2b044eeb742eb45a4607e55edd82471e975f8c01e376ba5313c128fcf0d301ae` |
| `strict-replay.json` | `aab727e48962ab6000a1d04252ef85864c3dfdbf046fdef108013ae09a3d3cc4` |
| `build.txt` | `454f9d6e1cdc44b1183f72e94fd85b61266868c08b8cd0b7548b0f3351c18a94` |
| `axioms.txt` | `a11b9d44683f40f17b31ee575d3b5f2c5189c380d848f7129415f15695e6939c` |
| `pdf.json` | `30749062965200d73d3eeeb9a47518eeeeb6a87a2b58552f55b77185e2af01a9` |
| `eligibility.json` | `07a93f44670fa91348023a741ad74a0e90f0a38135868d741eb8b725e78df6a3` |

Review completed: 2026-10-04T17:45:02.101502+00:00.
