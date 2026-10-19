# Independent verification of the submission for Conjecture 00000007753

Reviewed on October 18, 2026.

## Scope and mathematical validity

The submission disproves the exceptional-parameter cardinality bound, a necessary clause of the conjecture. At the permitted index n = 1, the divisor-product definition reduces to Φ₁,c(X) = X² − X + c. The distinct integer parameters −2 and −6 yield (X − 2)(X + 1) and (X − 3)(X + 2), respectively. Both factorizations are nontrivial over Q, contradicting the claimed upper bound 2^(1−1) = 1.

The source does not specify a coefficient field. The report explicitly uses the ordinary rational-polynomial interpretation; its witnesses and factorizations are integral as well. It does not rely on the separate, ambiguous wording about the Galois group of an evaluated special value. The n = 1 divisor/Möbius specialization is explained mathematically in the report rather than implemented through a general dynatomic-polynomial library.

## Formal semantic review

The Lean code was read in full. Its coefficient-list representation implements ordinary rational polynomial addition and multiplication, with trailing-zero normalization for polynomial equality. General evaluation lemmas prove that evaluation respects multiplication and normalization. A rational root then rules out every possible polynomial inverse, establishing nonunit factors rather than merely certifying numerical identities.

The theorem `TLMC7753.exceptional_parameter_bound_false` formally negates a list-cover cardinality upper bound of 2^(1−1) for reducible `firstDynatomic` polynomials. The theorem identifying `firstDynatomic` with the coefficient list [c, −1, 1], both factorizations, nonzero status, nonunit factors, and distinctness of the two parameters were checked. A covering list of length at most one forces any two members to coincide, so this is a genuine cardinality contradiction.

## Reproduction checks

Independently executed with Lean 4.31.0:

- Direct compilation of `lean/Main.lean`.
- `lake build`.
- `lake env lean Audit.lean`.
- `lake env leanchecker Main`.
- `python3 verify.py`.

All commands succeeded. The audited theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`; no custom axioms or proof holes are used. Closed arithmetic uses kernel-checked `decide +kernel`. The Python check reproduces the two coefficient products using exact rational arithmetic and is not needed for trust in the Lean proof.

The entire LaTeX report was read and both rendered PDF pages were visually inspected. The report accurately describes the proof and its formal scope, and the PDF is readable without clipped content.

## Reviewed artifact hashes (SHA-256)

- Source conjecture text: `fe08ade93a5412bb2bf3d0317579b8a043dd5cc73d3c05bf19d548aaeb7bfc62`
- `lean/Main.lean`: `62c56e3bd819dac60755690d31e3886ff09b0ee72403b7601e3c0de1927d1479`
- `solution.tex`: `3034f787092a98213a6c96650eb2c10ae25c4c26a40d01a16bae97ccf44b819e`
- `solution.pdf`: `38f199815471330586768a059da731ab88bab0cfbcc476553c265b3470c9db8f`

## Conclusion

The reviewed submission supplies a valid disproof of the stated exceptional-parameter bound, with a matching kernel-checked Lean proof and explanatory report. This verification is not an assertion of acceptance by the competition maintainers.
