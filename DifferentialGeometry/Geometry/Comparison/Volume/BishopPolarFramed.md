# BishopPolarFramed notes

## 2026-07-19 center-metric polar adapter

- The raw `normalBall_polar` theorem uses the fixed model norm.  This is not
  the tangent norm induced by `g p`, so its image cannot be used directly as a
  geodesic metric ball.
- Added a separate framed-coordinate module instead of changing the existing
  raw-coordinate API.  Its assumptions use the `NormedSpace` supplied by
  `InnerProductSpace`, avoiding the known independent-`NormedSpace` instance
  diamond.
- `exists_framed_den` proves that the framed parametrized density is one
  positive center-dependent constant times the raw normal density after
  applying `normalFrame`.  The determinant formula for this constant remains
  private.
- `framedRatio_anti` removes that constant before integration and transfers a
  raw radial density-ratio inequality to framed coordinates.
- `framedImage_polar` and `framedBall_polar` give the polar integral for the
  framed exponential.  By `framed_norm_lt_iff`, the model ball here represents
  the center-metric tangent ball.
- Focused verification passed without warnings.  All declarations are proved
  without `sorry` or new assumptions.

The next frontier is `normalBall_ratio`: produce the directionwise raw ratio
from `exists_radial_cmp` at one common physical radius, transfer it with
`framedRatio_anti`, and integrate over the model unit sphere.  The nontrivial
bookkeeping is that `exists_radial_cmp` requires its raw launch vector and
transverse family to be small in the fixed model norm; unit framed directions
must therefore be rescaled before applying it.  This is substantial geometric
assembly, not a remaining defect in the framed polar formula.

Honest accounting: the three framed-coordinate adapter theorems are complete
(100%).  `normalBall_ratio`, `localBall_ratio`, `localPack_card`, and the Step-A
discharge are each unstated/unproved (0%).  Dedicated Route B machinery is
approximately 58--62%; the full V1--V3 volume/CGT producer program is
approximately 41--45%.  Global Bishop--Gromov and unconditional HCG endpoints
remain 0% as theorems.
