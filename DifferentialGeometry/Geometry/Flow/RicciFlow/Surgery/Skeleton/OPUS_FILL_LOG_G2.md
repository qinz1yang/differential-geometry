# G2 log

- 2026-09-26: two new files (not wired in root aggregate).
  - `Geometry/Connection/ParallelTransport/Naturality/PartialDiffeomorph.lean` (331 lines):
    covariant derivative along a merely differentiable curve (MDifferentiableAt + differentiable
    chart rep, the regularity `IsLRegularizedGeodesicOn` carries) is natural under a
    `PartialDiffeomorph` that is isometric on its source, and under an `IsLocalDiffeomorph`;
    chart-rep regularity transfers both ways (the reverse needs `ContinuousAt γ`).
    Supplier: `covDerivAlong_pullback`, `chartRep_map_diff` (Pullback.lean) on `toOpensDiffeo`.
  - `Perelman/LGeometry/Jacobian/Naturality.lean` (509 lines): hypothesis form
    `S.base.metric (T - s^2) = localPullMetric (S'.base.metric (T - s^2)) f hf` per time; D, D'
    independent. Accel, geodesic (forward / reverse / iff on open K), curve, regularized action,
    index integrand + index, Jacobi (at a point, on open K), lGram, lJacobianDensity, lGramDeriv,
    `paramDensity_comp_of_inner_eq` (pointwise inner-product form = survivor clause 4).
  - `Geodesic/Naturality.lean` already exists (global diffeos) and was not edited, so the local
    geodesic statements live in the Jacobian file.
  - Compiled read-only as one scratch module (both files concatenated), clean with
    `linter.mathlibStandardSet`; connection file also clean standalone.
    Axioms: propext, Classical.choice, Quot.sound.
