# HopfRinowProper.lean

This file packages the intrinsic Hopf--Rinow exponential endpoint into the
proper metric-space consequences needed by the HCG Step A instantiation.

The checked route is:

- use `EMetricSpace.ofRiemannianMetric` and `EMetricSpace.toMetricSpace` for
  the finite Riemannian metric;
- use `hopf_rinow_expMapIntrinsic_surjective_minimizing` to cover metric balls
  by images of tangent closed balls;
- use finite-dimensional properness of the tangent fiber plus continuity of
  `expMapIntrinsic` for compactness;
- use the minimizing intrinsic geodesic and `intermediate_value_Icc` for the
  intermediate-distance realization property.

Verification passed for the file before the C4 wiring. The main gotcha is that
consumers must install the same `RiemannianBundle` and fiber inner-product
instances used to build the stored metric; otherwise Lean may select the
project `Tensor0SBundle` tangent norm and produce a typeclass diamond.
