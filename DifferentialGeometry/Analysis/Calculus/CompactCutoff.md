# CompactCutoff

## 2026-07-17 manifold plateau producer

`exists_bump_compact` is the finite-dimensional vector-space plateau used by
chart arguments.  `exists_mfd_bump` is the corresponding canonical manifold
producer: for compact `K` inside open `U`, it returns a globally smooth
`[0,1]`-valued function equal to one on a neighbourhood of `K`, with compact
topological support contained in `U`.

The first check exposed two import/instance details rather than a mathematical
gap: `Manifold.metrizableSpace` needs the direct metrizability import, and
`ChartedSpace.locallyCompactSpace H M` needs `I.locallyCompactSpace` installed
for the model first.  With those made explicit, focused verification passed.

This closes the reusable outer-support plateau needed after smoothing the
Riemannian distance tent.  `exists_cutoff_energy` is still theorem-level 0%;
its dedicated cutoff machinery is approximately 82%, with the live frontier
being quantitative comparison of the nonsmooth intrinsic gradient against the
chart Sobolev approximation norm.
