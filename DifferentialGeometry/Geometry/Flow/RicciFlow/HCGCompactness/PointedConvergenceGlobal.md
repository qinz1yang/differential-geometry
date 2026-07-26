# PointedConvergenceGlobal

This module globalizes the comparison maps from `PointedConvergence.lean` when
the pointed limit is compact.

After the geometric compactness step, the map-globalization route is purely
topological over the existing `PointedCGHMaps` API:

- `PointedRiemannianManifold.compact_of_ricci` packages the Bonnet--Myers
  route: connectedness, dimension at least two, a positive Ricci lower bound,
  and metric completeness produce a `CompactSpace` instance for the limit;
- `exists_source_univ` applies the stored open exhaustion to the compact set
  `univ`, so all sufficiently late comparison-map sources are `univ`.
- `target_univ` observes that a full compact source has compact image.  The
  partial diffeomorphism target is therefore closed as well as open; it is
  nonempty by the basepoint, so connectedness of the selected sequence
  manifold (the comparison map's codomain, not merely its source) forces the
  target to be `univ`.
- `globalDiffeomorph` uses the full source and target equalities to obtain a
  bijective local diffeomorphism and applies Mathlib's
  `IsLocalDiffeomorph.diffeomorphOfBijective`.

This layer does not prove compactness or connectedness and does not construct
Hamilton's rescaled source sequence.  Those remain producer inputs for the
Hamilton endpoint.

The only failed local proof step was an attempted `simp` discharge of source
membership after rewriting the source to `univ`; spelling out the rewrite and
`Set.mem_univ` closed it.  Focused verification then passed.

Progress accounting: this reusable compactness/global-map layer is complete
(100%), and the corrected `limit_to_orig` theorem now consumes it and is also
checked (theorem **100%**, no `sorry`).  This does not prove the source CGH
compactness theorem: `ham3_cgh_limit` remains an endpoint at **0%**.  Across the
whole HCG project, machinery is conservatively about **45%**, while the HCG
endpoint theorems remain **0%**.
