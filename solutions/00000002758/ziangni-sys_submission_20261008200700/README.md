# Disproof of conjecture 00000002758

In the actual group algebra Q[C2], both {1,g} and {1,(1+g)/2} are genuine
bases closed under multiplication. The second contains a nonidentity
idempotent, so their multiplication structures are nonisomorphic; no
algebra automorphism maps one basis onto the other. C2 has no distinct
isomorphic subgroup pairs. The explicit definition does not require units.

Complete report: proof.tex and compiled proof.pdf. Lean project: lean/,
Lean 4.19.0, Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b.
Reproduce: cd lean; lake update; lake build. Report: tectonic proof.tex.

Validation: one successful final full lake build after draft import and
coefficient-evaluation fixes. Six final audits use only propext,
Classical.choice and Quot.sound. The one-page PDF was compiled, rendered
and visually inspected at original resolution. Local dependencies and
build products are ignored and excluded from the submission.
