# Moving scalar Laplacian energy bound

## State — 2026-07-10

`lapDiff_energy_le` is proved and focused verification passes without warnings.
For a fixed reference metric `g`, it gives one constant `C >= 0`, chosen before
the moving metric and before the spectral vector, such that every finite-support
rank-zero `H^2(g)` representative satisfies

```text
integral (Delta_h u_v - Delta_g u_v)^2 dvol_g
  <= C * metricDerivNormSupOn univ 1 h g g ^ 2 * ||v||^2.
```

The constant is independent of the spectral support and its cardinality.  The
proof integrates `HCGCompactness.lapDiff_sq_le`, then uses the existing scalar
Hessian and gradient energy estimates.  It never compares whole dependent
tensor fibers and never selects a global frame.

## Durable proof choices

- Use the invariant pointwise decomposition from the geometry-layer
  `MetricLapDiff.lean`.
- Rewrite the intrinsic Hessian and differential norms only through the scalar
  identities `hessSec_normSq` and the rank-zero `du` identity.
- Consume the canonical `hess_energy_le` and `grad_energy_le`; the proof does
  not depend on support-wise `l1` estimates.
- Keep all normalization scalar-valued and use restricted `simp only` lists.

## Downstream completion

The previously listed algebraic packaging is now complete in
`MetricLapDiffCore.lean` and `MetricLapDiffTime.lean`.  The true finite-core
action extends to `lapDiffOp : H^2(g) ->L TensorL2 0 0 g`, and
`lapDiffA2_bound` uses
`sqrt C * |metricDerivNormSupOn univ 1 (G.metric (T-s)) gT gT|` as a modulus
tending to zero.  No new consumer assumption was added.

## Honest progress

- `lapDiff_energy_le`: complete (100%).
- Actual continuous linear `A2 : H²(gT) →L L²(gT)`: complete (100%).
- Dedicated `A2` analytic/geometric machinery through the vanishing modulus:
  complete (100%).
- Moving conjugate-heat existence theorem: not proved (0%).
- Perelman no-local-collapsing theorem: not proved (0%).
