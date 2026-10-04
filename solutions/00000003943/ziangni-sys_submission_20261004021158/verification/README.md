# Author verification

- Lean 4.19.0 `lake build`: passed.
- `lake env lean -DwarningAsError=true Main.lean`: passed. Standard axiom audit is in `lean-audit.txt`.
- Python: passed for 1,100 labeled simple graphs, 10,313 matchings, and 20,877 augmenting paths through five vertices; checked tight disjoint-edge examples through 100 vertices.
- Tectonic: produced the 3-page A4 PDF. All pages rendered with Poppler and inspected visually; no clipping or overlap. The final build has no overfull boxes; harmless underfull bibliography warnings remain.
- Native editor: opening the `.tex` source was queued in Codex. Native compilation was attempted but failed with `Unable to find standard directories for platform`. The delivered PDF was compiled with Tectonic instead.
- Original metadata: neither proven nor disproven. No upstream solution path. Exact-ID live open/closed GitHub PR search returned `[]` immediately before the commit; see `pr-search.json`. Root must recheck before publishing.

The count is augmenting paths actually selected by the classical iterative matching algorithm. Search operations and enumeration of all candidate paths are different quantities. This semantic scope is stated in the report rather than left implicit.

Formalization scope: actual graphs, matching disjointness and capacity, alternating simple-path edge extraction, remove-and-insert toggle cardinality, and a sequence of valid matchings linked by those updates. All intermediate matching invariants are stored in the run records. The report proves the standard fact that toggling any simple augmenting path preserves validity; the Lean theorem does not separately construct that matching. Its run bound applies to every actual algorithm run and even every partial run.

Independent mathematical and semantic review is pending; this file records author verification only.
