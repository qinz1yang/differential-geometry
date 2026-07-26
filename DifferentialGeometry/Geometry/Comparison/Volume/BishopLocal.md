# BishopLocal

## 2026-07-19 status

The intrinsic local comparison layer is proved and focused-check green without
current-file warnings or `sorry` declarations.

- `framedBall_eq_small` identifies a framed normal image with the intrinsic
  Riemannian-distance ball below `expDiffeoRadius`.
- `localBallVolume` is the volume of an actual `Metric.ball` for the canonical
  Hopf--Rinow metric realization.
- `localBall_eq_normal` transfers between metric-ball and framed-normal-ball
  volume using the existing two subset directions from `BallVolume`.
- `localBall_cross` proves cross-multiplied Bishop comparison on one positive
  center-dependent interval and chooses that interval strictly below
  `injRadius`.
- `localBall_ratio` packages the same result as antitonicity of the volume
  ratio.

The mathematical conclusion is local only.  The returned radius is the minimum
of the radial-Jacobi comparison radius, the selected exponential partial-
diffeomorphism radius, and a positive injectivity witness.  Thus the theorem
does not show comparison at every radius below `injRadius`.

## Exact blocker for packing

The intended `localPack_card` requires comparison at
`(2 * m + 1 / 2) * r` around every selected center.  Step A proves this scale
is below the center's injectivity radius through `InjRadiusDecayInput`, but its
adaptive scale has no relation to the extra analytic radius returned by
`localBall_cross`.

The missing producer is therefore a local Bishop comparison theorem on every
strictly injective ball, not another finite-packing lemma.  The current proof
cannot simply enlarge its radius: `exists_radial_cmp` supplies Jacobi
regularity only for uniformly small initial vectors, while `framedBall_polar`
uses one selected local partial diffeomorphism whose source need not contain an
arbitrary ball below `injRadius`.

This is a genuine missing geometry/API and route-choice frontier.  The smallest
decision is whether to extend the Jacobi and change-of-variables machinery to
raw framed exponential maps on arbitrary strictly injective balls, or instead
prove a uniform lower bound for the existing comparison radius from the HCG
bounded-geometry inputs.  Adding a comparison-radius assumption to
`localPack_card` would not be useful: Step A cannot discharge it.

## Honest accounting

- `localBall_ratio`: theorem complete, 100%.
- `localPack_card`: not stated or proved, 0%.
- Step-A direct volume/packing discharge: not stated or proved, 0%.
- Dedicated Route B machinery: approximately 74--78%.
- Full V1--V3 volume-comparison/CGT machinery: approximately 45--49%.
- Global Bishop--Gromov and unconditional HCG compactness endpoints: 0% as
  theorems.
