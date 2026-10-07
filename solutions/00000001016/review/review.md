# Solution Review — Conjecture 00000001016 (PR 661)

**Submission:** Jackmeson1 — `solutions/00000001016/Jackmeson1_submission_20261005083709`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- Conjecture read in full (English + Chinese) from `conjectures/00000001016.md`; shipped `conjecture.md` is byte-identical to it (`diff` clean).
- LaTeX read in its entirety; independently rebuilt with `latexmk -pdf -interaction=nonstopmode` in a scratch dir (exit 0). Shipped vs rebuilt text compared with pypdf after whitespace normalization: content matches; only cosmetic spacing and math-glyph ToUnicode extraction artifacts (`is 0`/`is0`, `[84 ,12]`, a `⋅`/`∑` glyph mapped differently), 2 pages in both.
- `lake build` from a clean `.lake` (shipped build artifacts removed; `.lake/packages` symlinked to the prebuilt pool): **Build completed successfully (8708 jobs), 0 errors, 0 warnings**, toolchain `leanprover/lean4:v4.33.1`, Mathlib v4.33.1 rev `0df444a360`.
- `#print axioms` run fresh (`lake env lean AuditCheck.lean`) for `conjecture_1016`, `no_selfDual_84_12`, `two_mul_finrank_of_selfDual`, `finrank_add_finrank_dual`, `dotForm_nondegenerate`: every one depends only on `propext`, `Classical.choice`, `Quot.sound`. Grep for `sorry`/`native_decide`/`admit`/`implemented_by`/`extern`/`unsafe`/`axiom`: only prose hits in README/tex (`Axioms.lean` is just a `#print axioms` audit file).
- Aux code: `verification/axioms.txt` and `verification/build.txt` match fresh reproduction (same theorem set, same success line, 8708 jobs). Note: the `verification/SHA256SUMS.txt` entry for `conjecture.md` does not match the shipped file (13/14 entries OK) — a stale-manifest hygiene issue only, since the shipped copy is byte-identical to the official conjecture and the Lean sources were rebuilt and verified from scratch.
- Metadata: `metadata.csv` lists 00000001016 as unsolved; submission adds only its own folder.
- Independent numeric sanity checks: Griesmer bound for k = d = 12 is 12+6+3+2+8·1 = 31 (as the report states); the diagonal triple of the extended binary Golay code has minimum distance 3·8 = 24, confirming the report's remark that under a nonstandard self-orthogonal reading a self-orthogonal [84,12,24] code would exist.

## Semantic audit

The official conjecture states: the [84,12,12] binary extremal self-dual code (a "candidate at the Griesmer boundary") does not exist; moreover every [84,12] binary self-dual code has no automorphism of order 11 and has minimum distance at most 11. Read with the standard coding-theory notation ([n,k] / [n,k,d], self-dual = C = C⊥ for the standard dot product), the class of binary self-dual codes of length 84 and dimension 12 is empty: the dot product on F_2^n is nondegenerate, so dim C + dim C⊥ = n and self-duality forces dim C = n/2 = 42. Hence claim (1) is a genuine non-existence theorem and claims (2), (3) hold vacuously.

The submission proves exactly this. The Lean development defines the real objects — `BinaryCode n` as a `Submodule (ZMod 2) (Fin n → ZMod 2)`, `dual` as the orthogonal complement for the actual dot-product bilinear form, `minDistance` as the infimum of Hamming weights of nonzero codewords, automorphisms as coordinate permutations preserving membership — and proves nondegeneracy of the dot product and `finrank C + finrank C⊥ = n` (via Mathlib's `LinearMap.BilinForm.finrank_orthogonal`) rather than assuming them. The capstone `C1016.conjecture_1016` is the conjunction of the three claims with quantifier structure matching the bilingual text exactly; the proof discharges (1) by the dimension identity and (2)–(3) from the proven emptiness of the class. This is a formalization of the conjecture's own objects, not a toy surrogate and not an assumed contradiction.

The vacuity of (2)–(3) is a property of the conjecture as written (an LLM-generated statement whose parameters are internally inconsistent — the "Griesmer boundary" description is also spurious, since the bound for k = d = 12 is 31, not 84), not a loophole manufactured by the submitter; the report and README disclose it prominently, prove the strongest honest reading, and correctly decline to substitute a self-orthogonal reading that the text does not state. The mathematics was independently verified: nondegeneracy of the F_2 dot product, the dimension count, the Griesmer sum, and the triple-Golay self-orthogonal example all check out.

Build, axioms, checksum-of-conjecture, PDF parity, and the aux verification outputs all reproduce. No obstruction to approval was found.

## Issues found

None blocking. Two non-blocking notes: (a) the shipped `verification/SHA256SUMS.txt` is stale for `conjecture.md` (the shipped copy is nonetheless byte-identical to the official conjecture); (b) the vacuous truth of claims (2)–(3) follows from the conjecture's own impossible parameters and is fully disclosed by the submitter.

## Verdict

APPROVED. A faithful Lean formalization of all three literal claims about the conjecture's own objects, with the non-existence of any binary self-dual [84,12] code proved from the nondegeneracy of the dot product (dim C = 42 ≠ 12) and the remaining claims discharged honestly over the empty class; clean rebuild, standard axioms only, PDF and verification artifacts reproduce, and the mathematics is correct as stated.
