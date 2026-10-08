# Counterexample to 00000009543

The singleton identity-channel family on complex2x2 matrices is CPTP and its span contains the identity. Nevertheless it fails one-use finite-ensemble symmetrization for two orthogonal pure density matrices: every distribution on the singleton has weight1, so symmetrization would equate the distinct inputs. All-block symmetrizability requires the one-use condition, so the claimed sufficient direction is false.

The PDF and LaTeX source give the complete argument and its scope. The Lean project checks all ancillary block amplifications, density matrices, genuine finite probability distributions, channel-span membership and failure of the full one-use condition. No capacity claim is needed.

Run `lake build` inside `lean/` with Lean4.19.0. Mathlib and all transitive dependencies are publicly pinned. The definition reference is [Ahlswede et al., ISIT2010, Definition11](https://mediatum.ub.tum.de/doc/1070709/758380.pdf).
