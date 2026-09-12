# Uniform early-slab volume

Owner: Chapter25 task01a07c8d-49fa-7373-9948-022395d0119a.
Claim: 8c5ff5d8-d45c-4949-9791-6ce902b5c969 (shared three-file batch).
2026-09-08 20:09 UTC: VERIFIED, one public theorem.

Target: lem:scn-early-slab-volume in every finite positive dimension, with an
arbitrary fixed positive radius bound and no relation r^2 <= t. Reuse the actual
normal-chart/density argument of FamilySmallBall, retaining one uniform spatial
radius independently of time; extend to larger bounded radii by monotonicity.
No curvature hypothesis or upstream Chapter23/24 geometry enters this argument.

Producer: `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.family_early_slab_volume`.
Final focused check: 28.3s EMPTY on the first check. Named build: 22s, lint-clean.
Fresh joint audit: 28.4s, standard axioms only. Current hashes/log paths are in
`E:/lean-tools/chapter25-audit-20260908/noncollapse-completion.json`.
The private normal-chart lemma now returns a positive radius independently of
the time parameter; scaling that radius uniformly into any prescribed positive
rho and using volume monotonicity proves the full early-slab statement.
Root import is unique; the shared batch claim is released after registration.
