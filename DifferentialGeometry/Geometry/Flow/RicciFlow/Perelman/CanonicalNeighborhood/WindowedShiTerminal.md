# WindowedShiTerminal

Chapter25 source-only good-point derivative continuation. Initially unverified.
No compiler until the explicit shared-window handback.

Normalize by the actual source scalar. WindowedSourceCurvature supplies a compact
unit ball at every starting time in [-4,0], with one curvature bound throughout
that fixed window. Apply shi_bound_on_sliding_regular_window with duration one
and starting times approaching -1 as the terminal time approaches zero. The
constant shiLocalUniformBound 3 m K0 (sqrt K0) * K0 is independent of that endpoint.
Pass the bound to time zero using the proved actual curvature-jet norm continuity.

Retain Ioo(t-4/Q,t) subset D.regular explicitly. The book's ordinary closed and
closed-open intervals supply it from the witness window; an arbitrary carrier
does not. No earlier compactness or unproved terminal regularity clause is used.

## Verified 2026-09-11

Final saved check 2 EMPTY (22.9s), named build 1 passed (30.1s), SHA256 d4b95c89c98094d3a85f005ce2579d25d32b3bd1ed5090027551c7e3daeee6eb. The fresh WindowedGoodPointAxioms1 audit covers all23 publics in20.8s:22 standard-only; only book_good_point_derivatives inherits the named earlier Chapter23 model-curvature obligation. Frozen completion receipt: E:/lean-tools/chapter25-book-20260910/windowed-good-point-completion.json. This supersedes the initial unverified status above.

