# BookDyadicVolume

Owner: Chapter25 task01a07c8d-49fa-7373-9948-022395d0119a.
2026-09-10 VERIFIED: check3 EMPTY20.77s, named build1 passed28.34s,
fresh standard-only audit in BookNoncollapseAxioms1. Claimee7507c4 released
after landing; current state remains in WORKING_STATUS.md. Frozen receipt:
E:/lean-tools/chapter25-book-20260910/book-noncollapse-completion.json.

Book strong-scalar proof, master05b.tex eq:scn-first-doubling-scale and
eq:scn-dyadic-ratio-order. Reuse actual FlowMetricBall.dyadic and the native
finite Nat.find argument exists_drop_lower with q=(2/3)^n. This yields the
book's D=3^n, including n=2, rather than the older D=2^(n+1).

The volume ratio comparison is <=. The book's strict inequality only applies
after at least one preceding strict step; j=0 must permit equality. This is
the exact inequality needed by the entropy argument.

Uniform small-ball positivity at the singleton terminal time comes from
CompactSlabVolume. This removes the older connectedness requirement without
assuming a new small-ball asymptotic or changing the scalar predicate.
No earlier chapter admission is used in this selection argument.

All acceptance checks pass. After rewriting the dyadic successor radius,
the two centers agree definitionally; an explicit rfl closes that final equality.
The field cancellation already closes with field_simp; no following ring is used.
