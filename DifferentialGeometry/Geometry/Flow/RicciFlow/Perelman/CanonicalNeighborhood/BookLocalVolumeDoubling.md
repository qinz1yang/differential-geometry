# BookLocalVolumeDoubling

Owner: Chapter25 task01a07c8d-49fa-7373-9948-022395d0119a.
2026-09-10 VERIFIED: check2 passed19.58s, named build1 passed26.76s.
The factor and its >=1 bound have fresh standard-only audits. The geometric
theorem retains exactly one explicit earlier admission, also audited. Claim
c3bef7f9 released after landing; current state remains in WORKING_STATUS.md.
Frozen receipt: E:/lean-tools/chapter25-book-20260910/book-noncollapse-completion.json.

Source: master05a.tex, cor:bg-local-doubling, lines3541--3572. The factor is
the ratio of hyperbolic radial volumes at1 and1/2, with
q=sqrt(a/(n-1)); angular volume cancels. Its lower bound1 is elementary.

The geometry remains one explicit EARLIER obligation, not a proved result.
Native BishopLocal.localBall_cross requires a global Ricci lower bound and
only gives a radius below the injectivity threshold. SegmentPolar.segBall_vol_rel
handles arbitrary radii but still requires global RicciBoundedBelow and a
connected manifold. Neither can consume the book's local Ricci hypothesis
on the actual radius-r ball. BishopIntrinsicLocal.exists_intrMean_on does
accept Ricci along a geodesic, but extending that local input through cut-locus
polar integration is an earlier comparison producer, outside Chapter25 scope.

The new statement retains n>=2, arbitrary closed M including disconnected M,
and no scalar/entropy hypothesis. Chapter25's consumer will choose
C=cutoffEntropyConstant n (localDoublingFactor n a) b before M,g,x,r.
The original consumer is now verified conditional on this exact earlier
geometric input. No claim of reducing total proof debt by moving it.
