# Verification record: conjecture 00000001227

This records local validation and independent internal scrutiny, not maintainer acceptance.

## Mathematical scope

The complete maximum-cardinality matching criterion is proved for every finite simple undirected normal-play vertex-geography position. Matching edges are unordered graph edges; saturation is endpoint membership. The game outcome is defined separately by terminating legal-move recursion. Both source languages were inspected. The report discloses the standard game conventions and corrects the historical attribution without claiming a new theorem.

## Independent execution

Completed at `2026-10-04T23:30:14.426460+00:00`. The independent project copied only the eight frozen source/configuration files into a directory with no local build outputs. Shared prebuilt dependencies were reused after checking all nine pinned Git revisions and tracked-source cleanliness; dependency sources were not rebuilt from scratch.

`lake build`: exit 0, 4.564 seconds. All five Lean sources, including Check.lean, were replayed with `-DwarningAsError=true`, each exit 0. The project library also enables this option.

Lean version: 4.19.0; compiler commit `6caaee842e9495688c1567e78c0e68dbb96942aa`.

Mathlib revision: `c44e0c8ee63ca166450922a373c7409c5d26b00b` (v4.19.0). The other eight exact pins are preserved in lake-manifest.json and strict-replay.json. Compiler identity and all dependency revisions/cleanliness were rechecked after execution.

## Declaration and trust audit

All 21 authored declarations were inventoried: seven definitions and fourteen theorems, zero named instances. Every definition was printed, and all fourteen actual theorem types and transitive axiom lists were checked. Every theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`.

The independent environment harness enumerated all 30 compiled constants whose originating modules are submitted implementation modules: 21 authored and nine generated constants. Every constant was type- and axiom-audited. No unsafe or partial declaration, custom axiom, or nonstandard axiom dependency was found. The lexical source scan also found no admitted proof, native_decide, custom axiom, trust modification, or authored metaprogrammatic proof bypass.

The harness in verification/environment-inventory.lean is inspection tooling: its metaprogramming only prints existing types and collects axioms. It is outside the mathematical project and contributes no proof or theorem.

Frozen source/configuration hashes, the declaration inventory, and copied files remained unchanged throughout execution.

## Auxiliary computation

The standard-library Python script enumerates every matching using least-available-vertex choices and independently evaluates game trees from adjacency and visited vertices. Its author, the coordinator, and the semantic reviewer each executed the full bound. The coordinator execution counted 33,868 graphs, 202,013 starts, 718,921 matchings and 1,470,549 evaluated game states; zero disagreements. This includes 6,391 disconnected graphs and 6,505 isolated starts. At n=0, the graph and matching are empty and there are no starts.

This is finite sanity evidence only; no bound or computational result is assumed in the general Lean theorem.

Auxiliary script SHA256: `923e5aa0f29cbbd962c566f54b97054819f923b565d2198481c7cfab8b2c79f4`.

## Report

The final standalone LaTeX compiled successfully in the native editor, and Tectonic exported its matching three-page PDF with no warnings or box diagnostics. All three rendered pages were inspected by the coordinator; the independent semantic review separately checks every page. One draft title line-break syntax error was corrected before successful compilation. The independent reviewer then identified a LaTeX hyphen ligature in the copied Python command; it was suppressed, and the final source was recompiled, exported, and all pages reinspected. Extracted PDF text confirms the literal ASCII --max-n option. The first export needed a standard package download and was retried successfully with network access; the final export has no unresolved diagnostics.

LaTeX SHA256: `d09f1892f3c7649c7ee2a129be42e418dc7ad9bc365035dcf327314e93f87d56`.

PDF SHA256: `10aaf1e3bd20a8f18846b83b7b6104892e8746f4084eda9e6df3482aa15b8d0c` (55141 bytes).

## Eligibility and contribution scope

Initial audit: 2026-10-04T23:13:56.277812+00:00 through 2026-10-04T23:18:09.463577+00:00. Prepublication live refresh: 2026-10-04T23:31:55.149422+00:00 through 2026-10-04T23:33:41.881902+00:00.

The exact source, both current guides and metadata remain unchanged at upstream main `fe1d06d431b0591b65d759c60035b1d2e293a819`. Metadata is unsolved. All 589 all-state PR records, 34 complete English/Chinese identifier/topic/comment searches, 21 fully read and refreshed plausible leads, both upstream branches and 34 local refs revealed no submission or solution for this conjecture. The separate GitHub Discussions index is empty. No prior invalid submission requiring an error account was found. Temporary search throttling was resolved by successful retries; no retrieval gap remains.

Only this personal submission folder is included. No conjecture, official metadata, leaderboard, official README, or maintainer review folder is modified.

## Reproduction and evidence

Use the commands in README.md. strict-replay.json records commands, all return codes, outputs, identities and audit cross-checks; build.txt and axioms.txt preserve the corresponding logs. The complete environment inventory is supplied as source, JSON and text. pdf.json pins the report and inspected page hashes. Eligibility records describe public evidence and its time limits.

| Frozen Lean input | SHA256 |
| --- | --- |
| `lean/Conjecture1227/Matching.lean` | `d8a2c20fb776bde13391584fcb3cfb820ec0afb5e092f73c629d0de36f79053b` |
| `lean/Conjecture1227/Game.lean` | `b7246fd3d73c8b95d464e546e0de315d326763839cbd8861da2e3e23eb83dac5` |
| `lean/Conjecture1227/Main.lean` | `91c4cb7c7bd7655c564f991b9f626596483bc2ea99c1cc3fb6eebf2b2ea41ff0` |
| `lean/Conjecture1227.lean` | `bd649a36a1478a6aed7140ae600eb9f5d21e2dc32998aa1753e8a5a85dffc838` |
| `lean/Check.lean` | `b9ccdd21d1599e28b6aaaa839988a20f6876a1f669aa8e4f92eb21b36503c7e5` |
| `lean/lakefile.toml` | `4e353573f04376ad1970778eded3f1508f83960a49fe217960978f77725400f9` |
| `lean/lake-manifest.json` | `e51540cd47bee1a776c3b54442a76fc02870cce5587abc0b4734a7c00907b084` |
| `lean/lean-toolchain` | `55e97be96000b5e9e290c9e74482e5e317861499a5540353ce845471bded8cea` |
