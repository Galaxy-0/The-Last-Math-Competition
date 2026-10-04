# Parent review of conjecture 00000002311

Verdict: PASS for a disproof of the source through its tightness clause.

Reviewer: the coordinating AI agent that delegated this problem. This is an internal review
within the same workflow, not an external or independent peer review. No source file was
changed in review.

1. Source and reading. Both languages make two assertions: a lower bound c/|Omega| with
   c = 1/2 for the derangement proportion of a transitive group, and tightness of "the
   corrected constant", verified by Frobenius groups. The only constant the source names is
   1/2. The draft reads the statement as the conjunction and refutes the tightness clause in
   three precise forms. The paper states that the bound itself is true and says what an
   alternative reading of "corrected constant" would mean. The reviewer of the earlier attempt
   objected to the missing general fact, not to this framing; this draft supplies that fact.
2. Objects. Groups and actions are Mathlib's `Group` and `MulAction`; transitivity is
   `MulAction.IsPretransitive`; the derangement set and proportion are defined directly from
   the action. `IsFrobenius` is the standard permutation-group definition (transitive, degree
   at least two, only the identity fixes two points, point stabilisers non-trivial). It was
   checked that S3 on three points satisfies it and that it forces faithfulness.
3. Cameron-Cohen. The proof was rechecked by hand: sum of fix = |G| and sum of fix^2 >= 2|G|
   by Burnside on Omega and on Omega x Omega, then (fix - 1)(fix - n) <= n on derangements and
   <= 0 elsewhere. The Lean proof uses Mathlib's Burnside lemma for both actions and an
   explicit equivalence between fixed pairs and pairs of fixed points.
4. Frobenius count. In a Frobenius action every non-identity element has 0 or 1 fixed points,
   so the first Burnside identity gives exactly n - 1 derangements. Checked by hand.
5. Final statements. `LowerBound c` quantifies over all finite groups with a transitive action
   on a finite set of at least two points. `Conjecture` is `LowerBound (1/2)` together with
   the disjunction of the three tightness readings at 1/2; `conjecture_false` refutes each
   disjunct. `corrected_statement` shows that the same predicates hold at c = 1, so they are
   not vacuous.
6. Earlier submission. The account of PR #190 matches the public pull request and the
   reviewer's comment and is limited to them. `acknowledged_prior_prs` is [190].
7. Limits, stated in the paper: degree one is excluded; the Frobenius property is defined in
   the file; a reading of the tightness clause that does not concern the size of the constant
   is not addressed; the remark on stabiliser orders and sharply 2-transitive groups is not
   formalised.
8. Evidence. `validate_draft.py`: fresh build with warnings as errors, only `propext`,
   `Classical.choice`, `Quot.sound`, four PDF pages, no TeX warnings. All four rendered pages
   (prefix 87422f742b33) were opened and inspected: no clipping, overflow or missing glyphs;
   the last page holds only the reproduction section.
