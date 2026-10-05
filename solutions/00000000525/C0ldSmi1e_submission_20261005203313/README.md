# Disproof of conjecture 00000000525

For `f = x² + y³` in characteristic 5, the Lean project proves the full origin-local F-pure threshold is at most `4/5`, hence is not `5/6`. It also proves the corresponding global bound over the prime-field polynomial ring. Since 5 is prime and `5 % 3 = 2`, this refutes the exact-value conjunct and therefore the original conjunction.

This submission does not claim an exact threshold, a value for the characteristic-zero log canonical threshold, or that the separate limiting assertion is false. The final negations hold for every real candidate limit value.

## Read and reproduce

- `original_conjecture.md` preserves the exact bilingual source.
- `report.tex` and `report.pdf` give the argument, standard definitions, semantic scope, and verification summary.
- `lean/Conjecture525.lean` contains every mathematical definition and proof.
- `lean/Audit.lean` checks all compiled declarations originating in the proof module.
- `lean/Check.lean` prints every authored definition and every authored theorem's type and axiom dependencies.
- `verification/` contains the coordinator's independent execution tool and its frozen source/declaration inventories.
- `evidence/` preserves author, coordinator, independent-reviewer, and document validation records. Historical paths describe the actual local runs.
- `SHA256SUMS.json` fingerprints every other file in the final submission.

With Lean 4.19.0 available, run from this submission folder:

```sh
cd lean
lake exe cache get
lake build
lake env lean -DwarningAsError=true Conjecture525.lean
lake env lean -DwarningAsError=true Audit.lean
lake env lean -DwarningAsError=true Check.lean
```

Keep the committed manifest. It pins Mathlib v4.19.0 at `c44e0c8ee63ca166450922a373c7409c5d26b00b` and all eight transitive packages. `lake exe cache get` is an optional dependency-cache download; it is not a mathematical oracle. Project proof sources are compiled locally. Lean's full compiler revision used for validation is `6caaee842e9495688c1567e78c0e68dbb96942aa`.

The top-level theorems are:

```text
Conjecture525.local_conjecture_false
Conjecture525.global_conjecture_false
```

Both take an arbitrary real `L` and negate `ConjectureAt` for the relevant prime-field threshold family. The characteristic-zero invariant is not defined to equal an arbitrary placeholder; the result works for every possible real value of that invariant.

## Exact mathematical scope

The proof uses genuine `MvPolynomial (Fin 2) K`, genuine ideals, and the real supremum over all Frobenius levels. The identity putting the fourth power in `(x^5,y^5)` is propagated to every level using Frobenius. Nonemptiness, upper bounds, and equality of the `e ≥ 0` and `e ≥ 1` defining sets are checked.

The global definition is the standard infimum of local bracket-power thresholds over all maximal ideals containing the polynomial. It includes non-rational closed points. The report cites its conventional identification in F-finite regular rings; the final family uses `F_p[x,y]`, where those hypotheses hold. The equivalence with a test-ideal definition is not itself formalized in Lean. Lean directly defines and reasons about this standard full characterization. No equality between origin-local and global thresholds is assumed: the needed global-to-origin inequality is proved.

The algebraic bound also holds for the displayed expressions over any characteristic-five field. The cited global identification is not asserted for arbitrary non-F-finite fields.

## Verification evidence

The coordinator's fresh build and strict replays passed, with 45 actual commands recorded in `evidence/coordinator/execution-records.json`. It checked all nine dependency identities and clean tracked source before and after execution, source/configuration hashes, and the full compiler revision.

The source inventory contains 48 authored declarations: 15 definitions/abbreviations and 33 lemmas/theorems. Independent compiled-environment enumeration finds exactly 63 declarations, including all 15 generated declarations. All 63 are safe logical declarations. No compiler-runtime exclusion, axiom declaration, partial dependency, unsafe dependency, or missing dependency is used. Axiom dependencies are limited to the standard Lean foundations `propext`, `Classical.choice`, and `Quot.sound`. No admissions, `native_decide`, custom axioms, or kernel bypass appear in the proof.

An independent reviewer rebuilt the project from source, replayed all three modules with warnings as errors, independently executed the full environment inspection, and read every generated declaration's type and body. The complete review and actual logs are included under `evidence/reviewer/`. `Audit.lean` and the extra environment harness are inspection tools; they do not create mathematical proof assumptions.

There is no auxiliary numerical computation: all mathematical calculations are checked Lean terms. Python programs in the evidence run commands, verify identities, and freeze hashes. Their historical absolute paths are preserved honestly; isolated path-adapted independent replays are documented by the reviewer. The retired Lake configuration and `Probe.lean` are development evidence outside the submitted Lean project. Early unlogged failures are described in author provenance; subsequent failed and successful commands retain their actual outputs and exits. Final passing runs are distinguished from these development attempts.

The coordinator's fuller independent audit can also be rerun with Python 3.11+ from this folder, after resolving the pinned dependencies above. Supply the actual Lean binary directory and choose new output directories:

```sh
python3 verification/independent_verify.py --ready \
  --source lean \
  --build-dir /tmp/tlmc525-independent-recheck \
  --evidence-dir /tmp/tlmc525-independent-recheck-evidence \
  --lean-bin /absolute/path/to/lean-4.19.0/bin \
  --packages lean/.lake/packages \
  --audit-names verification/audit-names.json \
  --frozen-sources verification/frozen-sources.json
```

This tool fails if the build directory already exists, if the frozen source hashes differ, or if any trust, identity, coverage, or execution check fails. Its generated environment harness is saved with the new evidence. No prior authored build output is copied.

The report was compiled in the desktop LaTeX editor, exported from the same source, and rendered for review of every page. Export and render identity records are under `evidence/document/`; an initial missing-font export failure and its layout warnings are preserved separately from the successful final export.

These are local verification and independent agent-review results. Maintainer acceptance is a separate repository decision.
