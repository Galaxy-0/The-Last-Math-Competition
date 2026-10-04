# Disproof of conjecture 00000008244

Three alternatives at 0,2,3 and three voters at 0,5/4,7/4 on the real line induce distinct strict orders abc,bac,bca under negative squared-distance utility. The profile is single-peaked on a<b<c and single-crossing in the voter order. Its actual real dimension is one, but it has three agents and three distinct orders, exceeding the claimed bound 2^d*d=2.

The disproof targets the maximal-agent-count conjunct only. Lean verifies actual utility comparisons, strict total and distinct preferences, both complete profile properties, ordered locations, the median winner, actual Module.finrank and the bound failure.

Run lake build in lean/ with Lean 4.19.0. All public dependencies are pinned, including Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b. See report.tex/report.pdf and VERIFICATION.md.
