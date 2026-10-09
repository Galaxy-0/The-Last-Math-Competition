# Source correspondence for 00000002207

Original bytes: `00000002207.md`. SHA256: `0016cb2bf81d535588320e63545be9089d320a430edb18bbe792983b12efb23a`.

English original: “Conjecture: The proportion of 2-generated ideals of a Bezout domain is 1 under finite-quotient-field conditions (2-generated Bezoutization).” Chinese original: “猜想：Bezout 域的 2-生成理想的比例在有限商域条件下为 1(2-生成 Bezout 化)。”

## Explicit interpretation

The usual commutative-algebra meaning of quotient field / 商域 is the field of fractions of a domain. Finite is read as finite cardinality of that field. The source does not specify a base field, so finite extension degree is not assumed; it does not state residue fields or finite quotient-ring conditions. Those genuinely different assertions have not been substituted. This interpretation is explicit and remains subject to independent original-first semantic review.

Two-generated is the standard existential generator-pair property, permitting repetition and redundant generators. It does not assert that the minimal number of generators is exactly two. The Lean predicate uses an ordered pair of elements as an existential witness but counts ideals only: `∃ a b : R, I = Ideal.span ({a,b} : Set R)`. Thus `(0,0)` and `(1,0)` count as valid presentations of the zero and whole ideals.

The source gives no sampling exhaustion. The actual fraction-field finiteness derives a finite ideal set, so the package uses the ordinary cardinal ratio of its two-generated subset to all actual ideals. The proof that every actual ideal qualifies is stronger than any choice of nonempty finite ideal sample and leaves no asymptotic density bridge missing.

## Full original object and hypothesis correspondence

| Source item | Actual Lean object or assumption | Formal conclusion |
|---|---|---|
| Bezout domain | `[CommRing R] [IsDomain R] [IsBezout R]` | The original wrapper retains these original premises. |
| Quotient field | `[Field K] [Algebra R K] [IsFractionRing R K]` | The actual domain algebra map is injective. |
| Finite field condition | `[Finite K]` | `Finite R` is derived by `finite_domain_of_finite_fraction_field`. |
| Actual domain | Existing ring structure, not an arithmetic proxy | `isField_of_finite_fraction_field` constructs inverse witnesses and proves `IsField R`. |
| Actual ideals | `Ideal R` | `ideal_eq_bot_or_top` classifies every ideal; `finite_ideals_of_finite_fraction_field` derives their finiteness. |
| Two-generated ideals | `TLMC2207.TwoGenerated R I` | `all_ideals_two_generated` proves actual pair-span equality for each actual ideal. |
| Denominator | `Nat.card (Ideal R)` | `ideal_card_eq_two` and `ideal_card_positive` prove it is exactly two and positive. |
| Numerator | `twoGeneratedCount R`, filter cardinality of actual ideals | `twoGeneratedCount_eq_ideal_card` and `twoGeneratedCount_eq_two` prove it equals the ideal count and is two. |
| Proportion equals one | Rational `twoGeneratedProportion R` | `original_proportion_one [IsBezout R]` proves the complete finite-cardinal ratio equals one. |

The count/proportion definitions need a `Finite (Ideal R)` instance to obtain an enumeration. In each source theorem that instance is constructed in a `letI` from the original hypotheses, not added as an assumption. No arbitrary Fintype object, extra finite-domain hypothesis or unproved ideal-generation connection replaces the original statement. Proof irrelevance removes dependence on the particular finite proof. `Nat.card` is intrinsic and independent of enumeration.

Mathlib's actual `IsBezout` means that every finitely generated ideal is principal. The field argument proves the desired result for all commutative integral domains with finite fraction field, so this original premise is mathematically redundant; retaining it in `original_proportion_one` is an explicit implication to the complete source. It has not been replaced by a custom axiom.

## Lean-to-report correspondence

The first PDF page states all original hypotheses, the finite ratio definition, exact ideal counts and the full proof. The second page gives the Lean hypothesis map, definitions, theorem names, interpretation limits and source provenance. The proof first derives finite R from finite K and then proves inverses by finite injective-multiplier surjectivity. The actual field structure is compatible with the original ring operations. All ideal classification and span conclusions apply to that same actual `Ideal R`.

The nontriviality of a domain distinguishes bottom from top, and `Ideal.equivFinTwo` gives the exact cardinality two. A concrete `IsFractionRing (ZMod 2) (ZMod 2)` theorem is also compiled, so the premises are not an impossible-hypothesis shortcut.

## Provenance and verification limits

Reused complete bridge: `run2207-scout-v1`, same native worker `/root/run2207`, scout result SHA256 `0ebd477acf4abce670a03ce210c4f7e1634a23e221372f4cd8f4eb02f6bdcd52`; scout Bridge SHA256 `6eebfada0af91e885d76caa17dd4b6e25ea290f8e7f6a291a3cb118601380c30`. Scout files stayed frozen. The author added exact intrinsic cardinalities, separately named ideal classification and numerator counts, the finished proof document and source correspondence.

Focused author Lean compilation passed. Printed theorem axiom sets contain only `propext`, `Classical.choice` and `Quot.sound`, with no `sorryAx` or local axiom declarations. This author observation is not deterministic acceptance: root owns target contracts, a private clean build, fresh kernel replay, independent semantic/PDF review and final promotion. No submission or eligibility assertion is made.
