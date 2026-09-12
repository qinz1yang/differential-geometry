# FiniteHornCommonArms

Owner: Chapter25 continuation, claim a031e4e4-886e-4303-9a53-0efc5f526aa9.
Verified 2026-09-09: focused1 EMPTY (26.08s), named build1 (31.16s),
fresh audit1 (25.35s), the public producer is standard-only through the
current DeepMinimizers artifact. The first independent check passed.
Current hashes and stage receipts are in ambient-completion.json.

Stack two buffered minimizing-tail producers. Pick the common bases on the
recorded axial ray with radii tending to zero and smaller than both endpoint
radii, so both arm lengths stay positive. The actual smooth minimizers are
rescaled to unit speed. Their whole images stay in the middle tail; every pair
of points on opposite arms has an actual smooth minimizing cross-connector in
the outer tail. Length convergence follows from the common base limit.

This constructs the common-base/whole-arm/all-connector part of RayApproximation.
It does not assert uniform convergence to specified EndRay representatives:
the required regularity, extendible-ray uniqueness and limit identification
remain separate obligations. No new geometric record or assumed arm package
is introduced.
