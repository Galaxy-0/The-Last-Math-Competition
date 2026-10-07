# Disproof of conjecture `00000001245`

## Claim

The conjecture states that the infimum, over elementary cellular automata,
of the minimum densities of Garden-of-Eden output words is `1/4`.

## Standard definitions used

An elementary cellular automaton (ECA) is a Wolfram rule number
`r : Fin 256`. Its output at a site depends on its left, center, and right
input bits. The neighborhood `l c r` is indexed by `4·l + 2·c + r`, and the
corresponding bit of the Wolfram code is the output. Configurations are all functions
`ℤ → Bool`. A nonempty finite word is a Garden-of-Eden (GoE) word if there is
no such configuration whose image contains that word at any translate.
Density is the proportion of `true` symbols in the word.

For each ECA, a minimum GoE density is included only if its GoE density set
has an attained minimum. Rules with no GoE words therefore contribute no
minimum value; they are not assigned an artificial density. The global
quantity is the infimum of this set of per-rule minima.

## Counterexample

Rule 255 has all eight local outputs equal to `true`, so its global map sends
every bi-infinite configuration to the all-true configuration. The one-letter
word `false` consequently has no global preimage. Its density is `0`, and all
GoE-word densities are nonnegative. Thus rule 255 has minimum GoE density `0`.
The set of all defined per-rule minimum densities is nonempty, bounded below
by `0`, and contains `0`. Thus its greatest lower bound is both at least `0`
and at most the element `0`, hence exactly `0`, not `1/4`.

This disproves the full ECA-range infimum claim. The proof does not rely on
rule 51, whose bijectivity only makes its own GoE set empty.

## Correction to closed PR #174

PR #174 treated GoE status as absence of a *period-two cyclic* preimage. That
is not the standard definition, which quantifies over all bi-infinite
configurations. In particular, the proposed rule-133 witness `00` has the
standard preimage patch `1011`: the adjacent input neighborhoods are `101`
and `011`, and rule 133 maps both to `0`. The Lean development defines the
global map on `ℤ → Bool` configurations and verifies this preimage directly.

## Lean contents

`lean/Main.lean` defines the 256-rule truth table, local and global maps,
finite-word preimage, GoE property, density, attained per-rule minimum, and
the infimum over defined minima. It proves the rule-255 counterexample,
nonnegativity, the empty-set convention, the global infimum, and the rule-133
preimage correction. It contains no `sorry`, `native_decide`, or custom axiom.
