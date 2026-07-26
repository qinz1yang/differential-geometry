# RadialLog

## Role

This module converts the ambient polar inverse into a genuine tangent vector at
the round-sphere base point.

## Route

- `radialLog` is the polar angle multiplied by its ambient unit direction.
- `radialLog_smooth`, `radialLog_orth`, and `radialLog_norm` record the scalar
  and tangent-plane facts without unfolding sphere charts.
- `roundLog` passes the ambient vector through `dInclEquiv.symm`; the fixed
  orthogonal projection makes the definition total at the two poles.
- `round_exp_log` uses the explicit great-circle formula from
  `RoundIntrinsic`, not a new inverse-exponential assumption.
- `roundLog_tendsto` controls the base-point singular normal form, and a local
  diagonal-exponential branch then proves `roundLog_smooth` on the full
  one-pole domain `{x | x ≠ -p}`.
- `round_exp_log_ne` packages the exponential/logarithm cancellation on that
  same domain, including the center.
- `roundLog_mfd_self` differentiates that cancellation at the base point and
  identifies the logarithm differential with the identity.  The proof compares
  continuous linear maps only after applying them to a vector, avoiding the
  non-definitional tangent/model topology equality.
- The intrinsic exponential lemmas are parameterized by the caller's sphere
  `PseudoEMetricSpace` and by `CompleteSpace` for exactly its induced
  uniformity, rather than silently selecting the canonical chordal metric.

The smooth codomain is the fixed model space `EuclideanSpace ℝ (Fin n)`.
Although this is definitionally the tangent space at the base point, keeping
the statement in the model-space normal form avoids asking Lean for a
`ChartedSpace` instance on the opaque `TangentSpace` synonym and avoids the
competing Riemannian/bundle norm topologies.

## Verification and progress

Focused verification and exact module verification passed after the
metric-world parameterization.  The file contains no `sorry` or `admit`.

`ham3_space_box` remains unproved and therefore 0%. Its dedicated positive
Killing--Hopf machinery is approximately 74% complete.  The one-pole Cartan
map and its center jet are now available; the next phase is global two-pole
overlap rigidity and gluing.
