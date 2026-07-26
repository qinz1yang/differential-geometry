# RadialRadius status

## 2026-07-18 explicit H6 radius package

- `Rm04DataAt` records the differentiability and endpoint-closed Rm04 ODE data
  at a prescribed source radius.
- `rm04Data_jacobi` proves that package at the canonical
  `jacobiVarRadius = expMapC2Radius / 26`; it uses the direct Jacobi equation,
  endpoint equation, regularity, and initial-derivative producers from
  `JacobiVariation` and does not choose another local radius.
- `rm04_one_le` and `rm04_one_ge` expose arbitrary-direction upper and lower
  endpoint estimates at that same radius.  The old existential APIs in
  `RadialGronwall` remain unchanged compatibility entry points.
- `jacobi_radius_le_c2` records the canonical radius inclusion consumed by the
  framed endpoint bridge.
- Focused and exact verification passed.  This brick is complete. The framed
  orthonormal endpoint and scalar Gronwall consumers now live in
  `C4/H6NormalCoord.lean`.

## Progress accounting

- Explicit radial Rm04 radius brick: 100%.
- Sequence-uniform `NormalRadiusProfile` theorem: 0%.
- Dedicated zero-order H6 normal-coordinate machinery: about 95%.
- Unconditional MSM135 Theorem 3.9 endpoint: 0%.
- Whole HCG compactness machinery: about 60%.
