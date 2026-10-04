# Independent adversarial review: 00000008656

Verdict: **PASS for the stated orbit-uniqueness conjunct.**
Reviewer: `/root/solve_4001_7000`, 2026-10-03.

Reviewed SOURCE.md (both language versions), the complete main.tex, and
the complete lean/Main.lean. The package has no README.md; this is a
packaging note, not a mathematical defect. PDF rendering was not audited.

## Actual free group, not a surrogate

`Group` specifies the ordinary associative multiplication, two-sided
identity, and two-sided inverse laws. Words are all finite lists of signed
basis letters. `WordRel` is exactly the equivalence/congruence generated
by cancelling a signed letter followed by its flipped sign. Its constructors
do not impose commutativity, exponent two, or any unrelated relations.
The quotient operations are proved well-defined; inverse words reverse
order as well as flipping signs. All group axioms are proved on the quotient.

The universal property is substantive: arbitrary assignments into arbitrary
groups have an evaluation homomorphism, relations preserve evaluation, and
every homomorphism agreeing on generators equals it. The uniqueness proof
handles negative letters through preservation of inverses. This universal
property confirms the quotient really is F(A). It is not merely a group
with a chosen involution. The rank-two basis is genuinely Fin 2.

## Full orbit and length semantics

`Automorphism` consists of group homomorphisms supplied with a two-sided
inverse function. Inverse homomorphism preservation need not be an extra
field: it follows from bijectivity and multiplication preservation. This
is exactly the full automorphism concept, and `InOrbit` quantifies over
every such automorphism, not only the exhibited sign-change map.

The sign-change map preserves the order of letters and flips every basis
sign. It preserves concatenation and cancellation and is involutive, so
it is a genuine automorphism. It is correctly distinguished from inversion
of arbitrary group elements, which would reverse multiplication.

`MinimalWord` compares the displayed word to every finite word representing
every element of the full automorphism orbit. This is stronger than the
usual comparison restricted to reduced words. No uniqueness/normal-form
theorem for arbitrary reduced words is needed for this counterexample:
any word shorter than a one-letter word is empty, hence represents the
identity; injective automorphisms fixing identity cannot send the nonidentity
generator there. Both displayed one-letter words are also explicitly
proved reduced. Thus the stronger comparison supplies the necessary bridge
to usual reduced-word length without assuming that raw length is invariant
under free cancellation.

Evaluation into the additive integer group, obtained from the actual free
universal construction, gives 1 on a and -1 on a inverse. It proves both
nonidentity of the starting generator and inequality of the two quotient
group elements. `UniqueMinimum` requires equality even only as group
elements, so its failure also refutes literal uniqueness as a reduced word.

## Source scope and reference

Both source languages assert a unique minimal representative within the
orbit. They give no quotient by signed basis permutations and no canonical
tie-breaking rule. The paper correctly records that limitation. It makes
no conclusion about the other algorithmic-complexity clauses.

The cited primary paper was independently opened and read, particularly
Section 1 on the collection of minimum-length automorphic images:
https://shpilrain.ccny.cuny.edu/orbit.pdf . It supports the ordinary orbit
and length interpretation used here. The elementary counterexample does
not rely on an external theorem from that reference.

## Independent execution and fingerprints

Command, from the reviewed package's lean/ directory:

`tools/lean-4.19.0-windows/bin/lean.exe -DwarningAsError=true Main.lean`

Independently executed by this reviewer: **exit 0**, approximately 0.529 s.
Both printed main dependencies contain only `propext` and `Quot.sound`.
No admitted proof, custom axiom, or external computation oracle is used.
No author source was modified, and no GitHub operation was performed.

Main.lean SHA-256:
`78e57bf25ba784d6e8963cbc98f06d9cddaf71591bf646a5fe8cc7b24f2f20e7`.

main.tex SHA-256:
`bd7591f211f50cdaa434ed176f4e92d9fd2deb48c902113e426ba711cd940dc3`.
