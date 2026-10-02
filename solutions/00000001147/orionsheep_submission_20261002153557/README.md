# Disproof of TLMC conjecture 00000001147 (triangular H2 dimension two)

**Original statement (quoted verbatim).** "Definition: A triangular Lie algebra is a subalgebra of triangular matrices. Conjecture: The dimension of the second cohomology of a triangular Lie algebra is two; and the dimension is realized by one contribution each from the outer derivations and the center. (triangular H2 dimension two)"

## Object consistency

The definition as stated quantifies over *subalgebras of triangular matrices*. Our counterexample is

$$\mathfrak{aff}(1) = \left\{ \begin{pmatrix} a & b \\ 0 & 0 \end{pmatrix} \right\} \subset \left\{ \text{upper triangular } 2\times 2 \text{ matrices} \right\},$$

with basis $H = \begin{psmallmatrix}1&0\\0&0\end{psmallmatrix}$, $E = \begin{psmallmatrix}0&1\\0&0\end{psmallmatrix}$ and bracket $[H,E]=E$. It is literally a subalgebra of triangular matrices, so it is a triangular Lie algebra under the definition quoted above. (Note the conjecture does hold for the 3-dimensional Heisenberg algebra — also triangular — so the value 2 is attained by some triangular Lie algebras but is not universal.)

## Counterexample computation

Chevalley–Eilenberg cochains of $\mathfrak{aff}(1)$ (any coefficient field; ranks are field-independent, and we compute over $\mathbb{Z}$):

- $\dim C^1 = 2$; $\dim C^2 = \dim \Lambda^2\mathfrak{g} = 1$ (basis $H^*\wedge E^*$); $C^3 = 0$ since $\dim\mathfrak{g}=2$.
- $\delta^1 f(x,y) = -f([x,y])$, so $\delta^1 f(H,E) = -f(E)$: taking $f = E^*$ shows $\delta^1\neq 0$, and since $C^2$ is 1-dimensional, $\delta^1 : C^1 \to C^2$ is surjective. Hence $B^2 = C^2$.
- $Z^2 = \ker(\delta^2) = C^2$ because $C^3=0$.
- Therefore $H^2 = Z^2/B^2 = 0$, i.e. $\dim H^2(\mathfrak{aff}(1)) = 0 \neq 2$.

The secondary clause ("realized by one contribution each from the outer derivations and the center") also fails here: $\dim \mathrm{Out}(\mathfrak{aff}(1)) = 1$ and $\dim Z(\mathfrak{aff}(1)) = 0$, yet $H^2$ is zero-dimensional.

For contrast, the Heisenberg algebra $\mathfrak{n}_3 = [x,y]=z$ (strictly upper-triangular $3\times 3$, also triangular): $\dim Z^2 = 3$, $\dim B^2 = 1$, $\dim H^2 = 2$ — the conjecture's value there, confirming non-universality.

## Files

- `reproduce.py` — exact-arithmetic (Fraction) generic CE cohomology computer; run `python3 reproduce.py`. Output: `dim H^2(aff(1)) = 0`, `dim H^2(n_3) = 2`.
- `main.tex` — full write-up.
- `lean4/Main.lean` + `lean4/Check.lean` — formal computation in bare Lean 4 core (`Nat`/`Int`, no Mathlib): cochains, differential, surjectivity $B^2=C^2$, triviality of $H^2$ (single cohomology class, `cobdy_all`), and the impossibility of four pairwise distinct classes (`no_four_classes`, which is what $\dim H^2 = 2$ would require over any field).

## Axiom audit

`#print axioms` for every theorem (`Br_HE`, `d1_surj`, `d1_add`, `no_strict_inc`, `cobdy_all`, `no_four_classes`, `main`): **does not depend on any axioms** (no `sorryAx`, no `Classical.choice`, no `propext`, no `Quot.sound`). Zero `sorry`. Note: `Quotient`, `omega`, and `Fin` literals were deliberately avoided because in this toolchain (v4.33.1) each of them drags in axioms (`Quot.sound` / `propext`).

## Verdict

Conjecture 00000001147 is **FALSE**: $\dim H^2(\mathfrak{aff}(1)) = 0 \neq 2$.
