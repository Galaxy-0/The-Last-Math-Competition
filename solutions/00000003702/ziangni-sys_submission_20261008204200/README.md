# Disproof of conjecture 00000003702

Growing disjoint unions of K2 edges have actual normalized spectrum 0 and 2,
each with multiplicity half the vertex count. Their genuine empirical
probability measures are constantly (delta_0 + delta_2)/2, so converge
weakly but have zero mass on a neighborhood of 1. Their limiting support
is not the full interval [0,2]. The report explicitly distinguishes
literal support equality from the valid containment statement.

Complete report: proof.tex and compiled proof.pdf. Lean project: lean/,
Lean 4.19.0, Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b.
Reproduce: cd lean; lake update; lake build. Report: tectonic proof.tex.

Validation: one successful final full lake build after draft sum,
normalization and constant-function fixes. Eight audits use only
propext/Classical.choice/Quot.sound. PDF compiled, single page rendered
and visually inspected. Actual graph degrees, neighbor-sum operator,
complete Basis/eigenvalue multiplicities, empirical measures and weak
probability-measure topology are certified. Standard support is defined
explicitly by open neighborhoods. Local junctions/builds are ignored.
