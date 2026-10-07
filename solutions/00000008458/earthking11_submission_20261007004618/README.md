# Disproof of conjecture 00000008458

Under the single-width reading stated by the conjecture, its second clause is inconsistent with its definition. The definition says that a quasi-alternating link has Khovanov homology width 1. The asserted smallest quasi-alternating nonalternating link is itself quasi-alternating, while the same clause assigns it homological width 2. Thus one and the same width would equal both 1 and 2.

The conclusion concerns the conjecture as written: it does not distinguish reduced and unreduced Khovanov homology or introduce two different width invariants. If those were intended, the statement would need to identify them separately; that alternative reading is outside this disproof.

The Lean formalization represents links by an arbitrary type, width by a natural-number-valued function, and alternation by an arbitrary predicate. It proves the source claim false from the width definition and the existential content of “the smallest ... has ...”; no facts about link classification or crossing numbers are assumed.

To reproduce the verification:

```text
cd lean
lake build
lake env lean Check.lean
```

See `BUILD_AUDIT.md` for the verified toolchain, build result, and axiom audit.
