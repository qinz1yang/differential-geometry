# FiniteHornInteriorMinimizers

Owner: Chapter25 continuation, claim 49cb8aeb-c926-4c84-a96f-3f93f627feff.
Verified stronger version: focused2 EMPTY (19.38s), named2 (26.74s; prior
placeholder warnings only), fresh audit2 (18.75s), both publics standard-only.
Receipts: E:/lean-tools/chapter25-terminal-local-20260909/.
The same minimizing curve also records the length of every subinterval.

Choose the center inside one quarter of an endpoint ball captured in subend0.
A ball of radius R below the center's endpoint distance stays in that tail
and has endpoint distance at least r_E(center)-R>0. The checked radial annulus
therefore makes it compact in W. For an interior target, take R halfway between
its center distance and r_E(center), and a positive near-minimizer tolerance
below the remaining gap. All prefixes stay in this compact ball; the existing
smooth-minimizer producer applies without original-metric completeness.

This supplies arbitrary close point pairs, still subject to dist(x,y)<r_E(x).
It does not give all deep-end pair connectors or construct an end ray.
