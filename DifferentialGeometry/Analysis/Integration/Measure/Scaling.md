# Riemannian volume scaling

## State — 2026-07-09

The constant metric-scaling chain is checked without `sorry`:

- `chartGram_scale`: the chart Gram matrix of `c g` is `c` times that of `g`;
- `chartDensity_scale`: the chart density gains the factor
  `sqrt(c ^ finrank Real E)`;
- `chartLocal_scale` and `riemMeasure_scale`: the same factor passes through
  the chart-local measure and partition-of-unity sum;
- `volume_scaleMetric`: the canonical Riemannian volume measure satisfies
  `dμ_(c g) = sqrt(c)^n dμ_g`;
- `volume_scale_apply`: the corresponding formula holds on every carrier set.

The proof follows the canonical measure construction and uses the existing
metric scaling, determinant, density, `withDensity`, map, and measure-sum APIs.
It introduces no alternate volume notion.

## Role in Perelman noncollapsing

This closes the volume half of constant parabolic scaling.
`Geometry/Metric/DistanceScaling.lean` now supplies
`d_(c g) = sqrt(c) d_g` and ball-carrier equality, while
`Perelman/ScaleTransfer.lean` combines those facts with curvature scaling to
transport both single-ball and below-scale kappa predicates.

The Perelman no-local-collapsing theorem and `ham3_noncollapse` remain 0%.
Hamilton's downstream `NoLocalCollapsing -> Ham3Noncollapse` adapter is also
checked, so the dedicated scale-transfer sublane is 100%.  The analytic W-route
machinery remains about 10%, and whole HCG compactness
machinery remains about 45% with endpoint theorems at 0%.

Focused verification of the new scaling file passed.
