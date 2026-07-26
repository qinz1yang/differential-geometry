# FamilyParamControl

## Verified state — 2026-07-23

`exists_param_ctrl` is proved without `sorry`, and focused verification passes
without warnings.

For a fixed initial exponential parametrization
`Ψ := expMapDiffeo (G.metric 0) a`, the theorem produces a short positive time,
a fixed positive model radius, a positive lower density constant, and a speed
constant at least one.  On the doubled closed model ball it proves:

- containment in `Ψ.source`;
- a uniform positive lower bound for
  `paramDensity (G.metric t) Ψ`;
- a uniform bound for the `G.metric t`-speed of `dΨ v` by `L * ‖v‖`;
- validity at the closed endpoint `t = 0`, because continuity is restricted to
  `Icc 0 tau` inside the carrier rather than to regular times.

The proof reuses the coordinate-layer
`PartialDiffeomorph.mfderiv_cont` adapter (built from `tangentHome`) for
continuity of the pushed model vectors and
`Tensor0SFamilyContinuousOnSet.eval_continuous` for the Gram entries.  Compact
minimum and maximum arguments then give the two constants.  No varying-fibre
tensor equality, locally constant chart hypothesis, duplicate consumer-local
adapter, or new consumer assumption is introduced.

## Project position

- `exists_param_ctrl`: 100%.
- Fixed-centre short-slab parameter-control brick: 100%.
- Dedicated machinery for the all-centre `family_vol_low`: approximately 45%;
  the remaining work is the shifted-ball/path-length inclusion, the
  parametrized measure lower bound, and compact finite-cover assembly.
- `family_vol_low` theorem itself: 0%; it remains unproved and is not made
  conditional by this file.
- Initial-time `early_ball_low` and the final no-local-collapsing theorem:
  0% theorem completion; this result advances only their supporting geometric
  machinery.

The shifted model-ball inclusion was not added here because it requires the
explicit-metric path-length adapter and measure-facing assembly.  Those are the
next local consumers, not assumptions of `exists_param_ctrl`.
