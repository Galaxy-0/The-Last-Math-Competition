# Independent internal semantic review: conjecture 00000001227

**Verdict: PASS for the complete stated criterion under the explicitly disclosed conventional finite, simple, undirected, impartial normal-play interpretation.** No unresolved mathematical, formalization, report-correspondence, auxiliary-code, or PDF presentation defect was found in the final inputs identified below. This is independent internal scrutiny, not repository maintainer approval, official acceptance, or a merge decision.

**Reviewer signature:** `/root/review_1227`, independent internal semantic reviewer. **Date:** 2026-10-04 UTC.

I did not author the submitted mathematical proof, Lean implementation, report, or auxiliary script. I first assessed the bilingual problem and game conventions without candidate code, then reviewed the frozen candidate. I independently inspected the definitions, both matching-recurrence directions, the final theorem and complete report, read the execution and eligibility evidence, and reran the auxiliary computation. I identified a PDF command-ligature issue; the coordinator corrected it, and I inspected the corrected final source, text extraction and all three final rendered pages. I modified no frozen package input.

## Source, scope, and conventions

The exact English and Chinese source paragraphs agree on **every maximum matching** (最大匹配). The submitted `conjecture.md` is byte-identical to the reviewed source at upstream `fe1d06d431b0591b65d759c60035b1d2e293a819`, with SHA256 `367dec60edddf8dc09be05065adb5c20d192174b5402bffdc7b151cce38ce5eb`.

I read both complete current guides, including their full-report, complete-compilation, no-incomplete-proof-device, semantic-correspondence, and auxiliary-execution requirements. Their reviewed SHA256 values are:

| Guide at the pinned upstream revision | SHA256 |
| --- | --- |
| `README.md` | `cd54d17f51e08212ee9557ef74568f6f2c388279ac74339dc4a3bab7c283f27e` |
| `README.zh-CN.md` | `ffedf1385079b9741fce4176c7aa1662720c29391116b34e5e78ba154b4fa244` |

The short source omits explicit finiteness, simplicity, turn order and the losing condition. The report accurately discloses those conventions instead of attributing nonexistent words to the source. This is a defensible interpretation of the named finite game; this PASS does not establish an unspecified infinite-graph claim. Infinite play and draws require additional outcome conventions. The formal result adds no connectedness, bipartiteness, perfect-matching-existence, non-isolation or nonempty-graph hypothesis. Every finite size and every specified start are covered. With an empty vertex type there is no start to supply.

“Belongs to a matching” is correctly interpreted as endpoint saturation. “Maximum” means largest edge cardinality among all matchings, not inclusion-maximal. The source's introductory perfect-matching language is neither used to restrict graphs nor substituted for its explicit maximum-matching quantifier.

The historical caveat is handled accurately. The report acknowledges that the vertex criterion is known and that its attribution to Theorem 1.1 of Fraenkel, Scheinerman and Ullman's *Undirected edge geography* is corroborated by Gates et al., Theorem 2.8. It makes no novelty or new-extension claim and does not pretend that Lean proves the source's historical sentence. My initial primary-literature checks used [Fox and Geissler, §§1 and 5](https://arxiv.org/pdf/2108.09367), [Gates et al., §2.1](https://math.colgate.edu/~integers/yg4/yg4.pdf), and [Basu et al., §1](https://arxiv.org/pdf/1505.07485). The original 1993 full text was not successfully fetched, a limitation disclosed in the report's bibliography.

## Game semantics and winning strategies

`LegalMove G S v w` requires the current vertex to lie in `S`, the destination to lie in `S.erase v`, and an actual undirected adjacency. A residual set contains the current vertex and still-unvisited available vertices. Deleting the departed vertex and requiring the destination to remain in the successor set prevents revisits, including revisiting the initial vertex. Initially `Finset.univ` contains every vertex and the token is already at the supplied start; choosing the start is not counted as a move.

`Wins` is defined independently of matchings by well-founded recursion on `S.card`. At a valid position it asserts the existence of a legal successor for which `Wins` is false. Each recursive call removes a member of `S`, so the measure strictly decreases; its successor has a valid current vertex. At a position without legal moves the existential statement is false. The value assigned to invalid positions is irrelevant to the theorem, which requires validity; initial and legal successor positions satisfy that requirement.

This recurrence is a sound representation of finite normal-play winning strategies. Backward induction partitions positions: from a winning position one can choose a losing successor; from a losing position every legal move gives the opponent a winning position. Repeating the respective choices terminates and leaves the opponent without a move. Conversely, a losing position cannot supply a forcing first-player strategy, because every first move permits the opponent's winning continuation. The supplied formalization uses this standard outcome recurrence directly rather than introducing a separate datatype of history-dependent strategies. The report explains that interpretation, and `wins_iff_of_recurrence` proves uniqueness on all valid finite residual positions. Neither the definition nor its uniqueness proof assumes the matching criterion.

## Matching objects and both proof directions

`IsMatchingOn` uses actual unordered pairs (`Sym2 V`) belonging to `G.edgeSet`, with endpoints in `S`. Distinct matching edges cannot share any vertex. Graph-edge membership excludes loops, and using a finite set excludes repeated edge copies. `Saturates` is endpoint membership in some selected edge. `MaximumMatching` compares edge-set cardinality with every matching on `S`; `Essential` quantifies over every such maximum matching. The proof of maximum existence enumerates a finite powerset and includes the empty matching, so the essential condition is not made true by an empty collection of candidate maxima.

I checked the helper lemmas as well as the main recurrence. Moving a matching to a larger available set, erasing an unmatched vertex, erasing its unique incident matching edge, and inserting an edge between two unmatched endpoints all preserve the stated graph and disjointness constraints.

In the forward recurrence direction, essentiality of `v` provides an incident edge `vw` in a maximum `M`. Removing it gives a matching missing both endpoints on `S.erase v`. Every matching on that smaller set has cardinality strictly below `M`: equality would contradict essentiality of `v`. The removed-edge cardinality identity therefore makes the remainder maximum, witnessing nonessentiality of `w`. In the converse direction, a maximum matching on `S.erase v` missing `w` can be extended by `vw`. Any maximum matching on `S` missing `v` would then have cardinality both at most the former matching and at least one greater, a contradiction. Neither direction assumes the desired game equivalence or relies on bounded examples.

`wins_iff_essential` applies the independently established matching recurrence to the unique game recurrence. The final declaration `Conjecture1227.first_player_wins_iff_every_maximum_matching_saturates` specializes it to the complete finite vertex set and exactly the saturation quantifier advertised in the report. Its only representation instances are `DecidableEq` and `Fintype`; its graph and start are arbitrary. The separate isolated-start theorem agrees with the no-move-loss convention. The LaTeX proof follows these same arguments completely.

## Execution and trust evidence

I reviewed and cross-checked the supplied independent execution record rather than claiming to have personally repeated its whole Lean build. The record documents a fresh local build from the eight pinned source/configuration files, then strict warning-as-error replay of all five Lean files, all with exit 0. It identifies Lean 4.19.0, compiler commit `6caaee842e9495688c1567e78c0e68dbb96942aa`, Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`, and the other eight dependency revisions. Shared prebuilt dependencies were reused after source-revision/cleanliness checks; dependency sources were not rebuilt from scratch, as `VERIFICATION.md` explicitly states.

The source, independent-copy and frozen-source hash maps agree. The strict replay's `Check.lean` output is byte-identical to `axioms.txt`. All 21 authored declarations (seven definitions, fourteen theorems, no named instances) agree with the independently scanned declaration inventory. Every theorem's printed type matches the inspected source, and all transitive axiom lists contain only `propext`, `Classical.choice`, and `Quot.sound`.

I read the environment inspection harness: it enumerates constants by their actual originating implementation module, prints their full types and collects their axioms. It adds no proof. Its JSON and text records agree by declaration name, and its entire structured record agrees with the strict-replay record. All 30 constants, including nine generated constants, are safe, nonpartial and free of custom-axiom dependencies. The source contains no admitted proofs, `native_decide`, custom axioms or authored proof-bypass metaprogramming. The claims in the README, report and verification summary match this evidence.

## Auxiliary code and independent rerun

I read the full standard-library Python program and independently executed it with `--max-n 6`. Its edge-mask enumeration covers every labelled simple graph once. Its matching recursion branches on the least available vertex being unmatched or matched to each available neighbor, thereby enumerating every matching once; maximum size and the intersection of saturated sets are then calculated from those matchings. Its separate cached game recursion uses only adjacency, the current vertex and the visited set, marks the initial vertex visited, and returns false when there is no legal move. The two computations do not use each other's result.

My rerun returned exit 0 and exactly the supplied per-size counters: 33,868 graphs, 202,013 starts, 718,921 matchings, 104,357 maximum matchings, 1,470,549 cached game states, 6,391 disconnected graphs, 6,505 isolated starts and zero disagreements. The empty graph contributes one empty matching and no starts. My independent result record has SHA256 `da52d92394324d37646c6b119d63c88f8d9bbe9984e377f5bc85aa5162d3e9b2`. Timing/platform fields can differ between reruns; all mathematical counters matched. This is supplementary finite evidence, not the general proof, and the formal theorem does not assume it.

## Full report and all-pages visual inspection

I read the entire final `main.tex`, `README.md`, `VERIFICATION.md`, extracted report text and associated PDF evidence. I visually inspected each of the three final rendered pages and verified their hashes against `verification/pdf.json`. Page 1 contains the full scope, conventions, recurrence and matching definitions; page 2 contains both proof directions, the theorem and attribution; page 3 contains formalization correspondence, reproducibility instructions and references. All are legible and complete, with consistent numbering, intact formulas and table, and no clipping, overlapping text or missing glyphs.

The initially reported command-ligature defect has been resolved. The final page 3 and extracted text preserve literal ASCII `--max-n`. The final source and PDF hashes are recorded below; the PDF is 55,141 bytes and three pages. Native compilation and Tectonic export records report success, with no unresolved export warnings or box diagnostics. The reviewed final page hashes are `005ceb97664f4b547d11e44da0782b5b883b85b6a146d260ae66054784e9a467` (page 1), `affa12fd61be2dc83158a1575820e9a90a8af7e5a17ecac8fffa9236eb23a9c7` (page 2), and `749ef6a8cd8e668580f96e5299e83d0f1666ebafd385d0ccbb8a7db3d5ff540b` (page 3).

## Eligibility correspondence and review boundary

I inspected the initial eligibility summary, prepublication refresh and lead classifications for correspondence with the package's claims. They consistently identify this conjecture and unchanged pinned source/guides, unsolved metadata, 589 all-state PR records, 34 complete searches, 21 plausible leads read and refreshed, two upstream branches, and 34 local refs in the refresh. They report no prior submission or invalid submission for this conjecture, no remaining retrieval gap and an empty separate Discussions index. The initial 33-local-ref count and refreshed 34 count are explicitly different snapshots, not a contradiction.

These are time-bounded public-evidence findings, with the last live refresh recorded at `2026-10-04T23:33:41.881902+00:00`. I cross-checked the supplied operational evidence; I did not rerun its entire network search and make no claim about private or later work. Repository eligibility is distinct from the literature attribution and from this semantic PASS. Final submission-path scope, any later repository changes and maintainer acceptance remain the coordinator's or maintainers' responsibility.

## Exact reviewed package inputs

All 31 inputs were rehashed after the report correction and matched the final review-input manifest, whose SHA256 is `021f2ee5e38c6b536d0acc428caedc4dfdc72ef6ca43890271debaf313784e42`. The following identities apply to the proposed package's relative paths. This review and any subsequently created package-wide manifest are additional files, not inputs to their own hash list.

| Reviewed input | SHA256 |
| --- | --- |
| `lean/Conjecture1227/Matching.lean` | `d8a2c20fb776bde13391584fcb3cfb820ec0afb5e092f73c629d0de36f79053b` |
| `lean/Conjecture1227/Game.lean` | `b7246fd3d73c8b95d464e546e0de315d326763839cbd8861da2e3e23eb83dac5` |
| `lean/Conjecture1227/Main.lean` | `91c4cb7c7bd7655c564f991b9f626596483bc2ea99c1cc3fb6eebf2b2ea41ff0` |
| `lean/Conjecture1227.lean` | `bd649a36a1478a6aed7140ae600eb9f5d21e2dc32998aa1753e8a5a85dffc838` |
| `lean/Check.lean` | `b9ccdd21d1599e28b6aaaa839988a20f6876a1f669aa8e4f92eb21b36503c7e5` |
| `lean/lakefile.toml` | `4e353573f04376ad1970778eded3f1508f83960a49fe217960978f77725400f9` |
| `lean/lake-manifest.json` | `e51540cd47bee1a776c3b54442a76fc02870cce5587abc0b4734a7c00907b084` |
| `lean/lean-toolchain` | `55e97be96000b5e9e290c9e74482e5e317861499a5540353ce845471bded8cea` |
| `conjecture.md` | `367dec60edddf8dc09be05065adb5c20d192174b5402bffdc7b151cce38ce5eb` |
| `main.tex` | `d09f1892f3c7649c7ee2a129be42e418dc7ad9bc365035dcf327314e93f87d56` |
| `main.pdf` | `10aaf1e3bd20a8f18846b83b7b6104892e8746f4084eda9e6df3482aa15b8d0c` |
| `README.md` | `b4160d425034b04117aebfe89ab5f51a7f0ed1dfa2f05fe51249eca4b75cd922` |
| `VERIFICATION.md` | `d62144ae9808d02731907f2b26cb662cce50ac82c3e03209ce17999db79f5b76` |
| `auxiliary/check_vertex_geography.py` | `923e5aa0f29cbbd962c566f54b97054819f923b565d2198481c7cfab8b2c79f4` |
| `verification/strict-replay.json` | `ecc4a66d7901b4e63ab424e04f1df1dabf0236ddd2759a0cc9d2331d88c3db2a` |
| `verification/build.txt` | `06da0919130d12d187ff6d7a32329de803b8903dd2343451a95ac1126fc1a37c` |
| `verification/axioms.txt` | `a3c7fc2c97f47e12a6a505d4fdcef56280a3cca8924d2f1b64ae850d8dcadfaa` |
| `verification/pdf.json` | `1a9d2fdc8c3ae94202d125ba84f364e2264aaf23bf58154f9eeceb403e9b87a6` |
| `verification/report.txt` | `bfbebec01419df1ef33c474cd999985abfb5ae651c4cb9dd2fe56f58be1ed357` |
| `verification/environment-inventory.lean` | `54f34ba430e2ff661aa7175c03f9ee919b350cd3e61d87493c8eaad89b8f551a` |
| `verification/environment-inventory.json` | `ca1709efbf2fcf6d6be6ee4876c04a0183e5d2442263778b6426950b33f6816b` |
| `verification/environment-inventory.txt` | `0efcba03e74642588ac56b4d72060f2ab903bbcd75a28abef3fb37bd7c05880e` |
| `verification/sanity-results.json` | `2357d55719aa321a195034a8bfacb33947831448b3bd797d005a21b399482758` |
| `verification/sanity-output.txt` | `7c394dfde6293abb97e1449a7ad4b31d69c8dc146e43f6e4e064618225221584` |
| `verification/sanity-verification.json` | `a6b0e7714d181f6edba40354b9cbedbb8e53f8268cf82821484a0b309f4d4ff6` |
| `verification/native-compile.json` | `70ea4670f2f0dcd2243759cb014aee628dbb1d2f812f2fe04179b916c2ad21b4` |
| `verification/eligibility.json` | `b5c2d9bbd182d952f56bc7a2fcbf04ed00dd0d85c46420b986e2bb351ae04fce` |
| `verification/prepublication.json` | `211be370eda71987111609c211ca26fc3d8ad06159757e0abc1bd093587e81d4` |
| `verification/eligibility-leads.json` | `cd5b98718ae60b846a7c2f2152166e0fde73b87b5a4dfc98150adf9141abe01b` |
| `verification/audit-names.json` | `c5a629d266c64e62741864fb4bf41aa91aa072c348be84b1b1d55e956bda9700` |
| `verification/frozen-sources.json` | `855eafd33363fc09188919d32aebe622b95cb72606af6acf7f5fa98e26ee9079` |

**Signed:** `/root/review_1227` — independent internal semantic reviewer; not a repository maintainer approval.
