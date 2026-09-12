# CompactSlabVolume

Owner: Chapter25 task01a07c8d-49fa-7373-9948-022395d0119a.
2026-09-10 VERIFIED: check2 EMPTY15.24s, named build1 passed17.79s,
fresh standard-only audit in BookNoncollapseAxioms1. Claim43253d98 released
after landing; current state remains in WORKING_STATUS.md. Frozen receipt:
E:/lean-tools/chapter25-book-20260910/book-noncollapse-completion.json.

Target: the actual prescribed-slab conclusion of lem:scn-early-slab-volume,
master05b.tex lines3973ff. EarlySlabVolume.family_early_slab_volume returns
some positive tau; this does not itself give an arbitrary specified T0.
The present proof takes any compact K inside the smooth family's carrier,
so in particular includes both endpoints of K=[0,T0].

Reuse the native FamilyParamControl and EarlySlabVolume proof mechanism,
with density minima and speed maxima over the entire prescribed compact K.
Normal charts may be chosen using g(0), which is a smooth metric even when0
is not in K. MetricFamilySmoothOn is used only on K. A finite spatial cover
gives a uniform small radius; volume monotonicity extends to every r<=rho.
No connectedness, nonemptiness, Ricci flow equation, dimension-three input,
curvature bound or entropy input is added. Empty K and empty M are explicit.

The private local proofs stay here while the concrete compact-slab argument
is being verified; no lower-lane file or alternate metric hierarchy is edited.
All three acceptance checks pass. The private density-continuity theorem
omits unused completeness, compactness, separation and boundaryless parameters;
the chart-control theorem omits unused compactness of the whole manifold.
