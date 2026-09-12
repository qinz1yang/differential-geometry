# SlabKoszulControl

2026-09-10 SOURCE-WRITTEN / UNVERIFIED. Claim
f677a104-3934-41da-b3bc-8aa1a019bb95. No compiler during Chapter23's window.

This is the actual-metric consumer of SlabCovariantChangeBound: the tensor
estimated is contrTail of the native Levi-Civita connection difference with
the source metric. Native koszulComp_at supplies the identity; its all-order
bound is the sum of three slot permutations, with factor 3/2. The constant
is selected before both metrics and the positive error. Order a needs only
orders below a of the reference connection relative to the target connection.
All bounds are on an arbitrary open subset of the frame domain. Requiring
them on the whole trivialization domain would not follow from local slab
comparison data; the native frame and coefficient smoothness are restricted
to this open subset before the estimate is applied.

This does not assert that its numerical inputs already hold for IsSlabLimit.
Those require the local coordinate induction described in SlabCovariantChangeBound.md.
A second source-written theorem converts positive metric derivatives to the
intrinsic metric-error norm under an explicit frame comparison. It reuses
covDeriv_self_succ, metricCovDerivNorm_eq_iterCov and compL2_tower_le.
Still required: establish the local uniform frame comparison from C0 continuity,
raise the last slot using the already controlled inverse metric derivatives,
and prove the ensuing uniform limit is the actual next Christoffel derivative.

The private permutation estimate follows the existing proof inside
iterated_covariant_tensor_bound_of_koszul_contraction. No competing connection,
metric or compactness definition is introduced. Saved EMPTY check, named lint
refresh and fresh public axiom audit remain pending.
