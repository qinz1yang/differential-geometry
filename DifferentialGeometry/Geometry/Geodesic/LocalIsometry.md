# LocalIsometry

## Role

This file supplies the geodesic-naturality producer needed by point-data
rigidity.  It deliberately does not introduce a second local-isometry
predicate.  The public interface uses the existing
`IsLocalDiffeomorph I J ∞ f` together with the fiberwise metric identity.

The Poincare-Conjecture `LocalIsometryRigidity.lean` file was used only as a
reference for the normal-neighborhood architecture.  The implementation here
is native to `DifferentialGeometry/` and reuses the existing open-subtype,
pullback-metric, and cross-model geodesic APIs.

## Public results

- `geoEq_map_localIso`: a metric-preserving local diffeomorphism transports the
  geodesic equation at one time.
- `geoOn_map_localIso`: the corresponding result on an open time set.

The pointwise proof restricts a local partial diffeomorphism to open subtypes,
identifies the restricted source metric with the cross-model pullback metric,
applies `geoEq_mapCrossAt`, and then returns to the ambient manifolds.

## Verification and progress

Focused verification and the exact module refresh both pass on the final
source.  The file is sorry-free.

- `geoEq_map_localIso`: 100%.
- `geoOn_map_localIso`: 100%.
- This geodesic-preservation producer: 100%.
- The separate point-data rigidity theorem is tracked in
  `../Metric/LocalIsometryRigidity.md` and is now complete.
- `ham3_space_box` remains theorem-level 0%; the surrounding dedicated
  topology/global-geometry machinery is approximately 45%.  The wider Hamilton
  positive-Ricci infrastructure remains approximately 80%, while the whole HCG
  project is conservatively about 60% infrastructurally developed.

There are no new assumptions packaged as a wrapper and no new foundational
class.  The manifold and sigma-compactness instances in the statement are the
current inputs of the native cross-model pullback/geodesic machinery.
