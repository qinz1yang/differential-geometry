# Hamilton Positive Ricci Formalization Plan

## Target Theorem

Formalize Hamilton's three-dimensional positive-Ricci route:

```text
If a closed 3-manifold admits a metric with positive Ricci curvature, then it
admits a metric of constant positive sectional curvature.
```

## Current Status

- RicciFlower-local tensor, coordinate, Levi-Civita, Ricci identity, Bochner,
  and scalar calculus layers are now mostly native.
- Section 6 evolution interfaces are largely available; `ricciHeatDataSmooth`
  is now checked from the strengthened `IsSmoothSolutionOn` fields, and the
  remaining lower frontier is producing that strengthened package from
  `IsSolutionOn`.
- Section 7 scalar lower-bound and finite-time consumers are native.
- Section 9 local preservation algebra exists; analytic tensor-WMP producers
  remain explicit.
- Section 10.4 has a checked consumer stack; `ricciDataSmooth` now consumes
  lower `Evolution/RicciNorm.lean` producers, and the live producer work is in
  `RicciFlow/Regularity.lean`.
- Section 11/12 still contain global analytic and compactness frontiers.

## Main Dependency Ladder

### G0. Realized Foundation

Keep `SolutionOn` as candidate flow data and `IsSolutionOn` /
`IsSmoothSolutionOn` as proof packages.  Do not merge data and proof
predicates.  Interval-aware work should keep ordinary flow times separate from
terminal/maximal ambient times.

### G1. Metric, Operators, And Compact Minimum Calculus

Closed pieces include scalar WMP consumers, scalar regularity from smooth
solutions, metric variation bounds interfaces, scalar lower bound, and
finite-time scalar blow-up consumers.

Remaining work is mostly upstream analytic or global, not basic operator
calculus.

### G2. Levi-Civita Connection And Curvature

Levi-Civita smoothness, torsion/metric compatibility, curvature symmetries,
Riemann/Ricci realization, and local-frame/component bridges are native.

Do not import `DifferentialGeometry/Synthetic` for these endpoints.

### G3. Ricci Identity And Bochner

The covariant `(0,s)` Ricci identity, mixed component algebra, rough Laplacian
interfaces, and scalar Bochner consumers are present.  Future work should
consume invariant tensor/curvature-action APIs rather than unfold low-level
slot algebra.

### G4. Short-Time And Maximal Ricci Flow

Short-time existence, maximality, extension criteria, and nonextension past
`Tmax` remain global analytic frontiers.  Keep them as explicit black boxes
until the project intentionally opens parabolic PDE existence.

### G5. Ricci-Flow Evolution Equations

Native routes exist for inverse metric, Christoffel symbols, Ricci, scalar,
frame Ricci norm, and smooth-solution Ricci-norm data.  The current lower
target is `smoothOfSol` in `RicciFlow/Regularity.lean`: produce the
strengthened `IsSmoothSolutionOn` fields from `IsSolutionOn` rather than adding
endpoint hypotheses.

### G6. Maximum Principles

Scalar WMP work is native.  Tensor WMP still has genuine analytic/geometric
producer frontiers, especially the first-null scalar-sign/product-rule bridge.

### G7. Positive Ricci Preservation And Pinching

Dimension-three algebra is native.  The remaining important local frontiers are
the remaining `smoothOfSol` field producers, quotient evolution, and pinching
estimates.

### G8. Convergence To Constant Positive Curvature

Point-selection, noncollapsing, Hamilton compactness, curvature convergence,
and the topological handoff remain global-scale inputs.

## Black-Box Policy

Black-box only genuinely hard analytic/global facts:

- short-time existence and DeTurck analytic theory;
- maximal interval and extension criteria;
- no-local-collapsing;
- Cheeger-Gromov-Hamilton compactness;
- Myers/topological handoff when outside local RicciFlow goals.

Do not black-box tensor algebra, coordinate projection, curvature symmetry,
Levi-Civita smoothness, or finite-dimensional Ricci algebra.

## Immediate Next Work

1. Close the remaining `smoothOfSol` field producers in
   `RicciFlow/Regularity.lean`.
2. Continue to quotient evolution and improved pinching estimates.
3. Keep global Section 11/12 producers explicit and separate from local
   tensor/evolution work.
