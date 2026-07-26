# IsometryExtension

## Status

`ambient_iso_of_tan` is complete, focused verification passes, and the file has
no `sorry`.

The theorem takes points `p q` on the unit sphere and a continuous linear
equivalence between their tangent spaces preserving `roundMetric.inner`.  It
produces an ambient `E ≃ₗᵢ[ℝ] E` sending `p` to `q`, whose induced
`sphereDiffeo` differential at `p` is the supplied tangent map.

## Route

`dInclEquiv` transports the supplied map to an inner-product-preserving
equivalence

`(ℝ ∙ p)ᗮ ≃ₗᵢ[ℝ] (ℝ ∙ q)ᗮ`.

After composing with the target-subspace inclusion, Mathlib's
`LinearIsometry.extend` extends it to an ambient linear isometry.  Finite
dimensionality upgrades this self-isometry to a linear isometric equivalence.
Its value at `p` is orthogonal to `(ℝ ∙ q)ᗮ`, hence lies in `ℝ ∙ q`; unit
norm forces it to be `q` or `-q`.  In the negative case, postcomposition with
the reflection in `(ℝ ∙ q)ᗮ` fixes every prescribed tangent vector and flips
the normal sign.

Finally, `mfderiv_incl_sphereDiffeo` identifies the ambient action on
`dIncl p v` with the differential of `sphereDiffeo`; injectivity of the sphere
inclusion differential recovers equality with the original tangent map.

This avoids constructing an explicit orthogonal direct-sum equivalence and
adds no assumptions or new typeclasses.

## Project accounting

- `ambient_iso_of_tan`: 100%.
- The round-sphere tangent-isometry-to-ambient-extension producer: 100%.
- The Cartan/Jacobi global-extension phase: approximately 5%; this theorem
  closes one algebraic realization brick but not the exponential-map transfer.
- `ham3_space_box`: theorem not proved (0%); its dedicated topology/global
  geometry machinery is approximately 42%.
- The wider Hamilton positive-Ricci development remains approximately 80%
  infrastructurally developed; open endpoint theorems are counted separately.

The next consumer should use this theorem only after the Cartan transfer has
produced the tangent-space isometry at chosen base points.
