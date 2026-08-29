# VelocityLocal

## Result

`velocity_rep_diffAt` is a public local regularity lemma for the velocity of a
smooth manifold-valued curve. It states that the velocity is differentiable in
the tangent trivialization centered at the parameter under consideration.

The requested theorem is complete and focused verification passed without
warnings.

## Native route

The private proof in `Geometry/Geodesic/PullbackCross.lean` was inspected as the
requested source shape. The implementation does not duplicate that longer
coordinate proof: the lower connection layer now already exports
`MFDerivAlongCurve.velocity_coord_diff`, which proves the same fact under the
weaker local `C²` input. The new theorem lowers the supplied local `C∞` hypothesis
to `C²` and exposes the result in the `chartRepAt` API used by variation
consumers.

No reference-tree code was imported or copied, and no new assumptions,
instances, or foundational objects were introduced.

## Project impact

- `velocity_rep_diffAt`: 100% complete and verified.
- Generic velocity-coordinate infrastructure used here: already complete; this
  file adds only the requested public adapter.
- `lMinVec_nconj_lt`: remains 0% until its L-specific theorem is proved; this
  helper supplies only reusable local regularity.
- `redVolume_anti`: remains 0%.
