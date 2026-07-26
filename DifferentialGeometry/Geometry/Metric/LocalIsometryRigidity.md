# LocalIsometryRigidity

## Role

This file ports the point-data rigidity route from the external
Poincare-Conjecture project into the native `DifferentialGeometry/` API.  It
uses the standard hypotheses directly:

- `IsLocalDiffeomorph I J ∞ f`;
- preservation of the two Riemannian inner products by `mfderiv`.

No local-isometry structure, class, or consumer-side frontier assumption is
introduced.

## Route

1. Build a uniformly small geodesic ray from the existing rescaled chart-flow
   and identify its endpoint with `expMap`.
2. Send the ray through each local diffeomorphism using
   `Geodesic.geoOn_map_localIso`.
3. Apply the completeness-free geodesic uniqueness theorem
   `Exponential.geo_eqOn_of_init`.
4. Use the local exponential-map diffeomorphism to obtain eventual equality.
5. Promote local first-order agreement to global equality on a preconnected
   source using a closed-and-open tangent-map agreement locus.

The public results are `localIso_eventually` and `localIso_rigid`.

## Verification and progress

Focused verification and the exact module refresh both pass on the final
source.  The file is sorry-free.  The only typeclass seam exposed by the real
`geo_eqOn_of_init` call was its target `RiemannianBundle`; it is installed
locally from `g'.toRiemannianMetric`, following the existing native metric
pattern rather than adding a theorem assumption.

- `localIso_eventually`: 100%.
- `localIso_rigid`: 100%.
- Dedicated point-data rigidity machinery: 100%.
- `ham3_space_box` remains theorem-level 0%; the surrounding dedicated
  topology/global-geometry machinery is approximately 45%.  The wider Hamilton
  positive-Ricci infrastructure remains approximately 80%, while the whole HCG
  project is conservatively about 60% infrastructurally developed.
