# FiberExpansion.lean

## 2026-07-19 created (option-1 lane, brick J-a)

`gON_expand`: every tangent vector expands in ANY supplied `g`-orthonormal
family of full cardinality, `v = ∑ i, g.inner x (e i) v • e i`.  Green on
first focused check, no `sorry`.

Route: install the honest fiber inner-product structure of `g` via
`g.toRiemannianMetric.toCore x` + `Core.toNormedAddCommGroupOfTopology` +
`InnerProductSpace.ofCoreOfTopology` (`letI` chain copied from
`tangent_frame_expansion` in
`Analysis/Elliptic/…/RiemannianFiberNormSqRiemannOpVWFactorBound.lean`, which
proves the same expansion but only for a frame IT chooses).  Under that
structure `inner ℝ u w = g.inner x u w` is `rfl`; the supplied family is
`Orthonormal`; `basisOfOrthonormalOfCardEqFinrank … |>.span_eq` +
`coe_basisOfOrthonormalOfCardEqFinrank` give the span; `OrthonormalBasis.mk`
+ `sum_repr'` finish.

Intended consumer (bricks J-c/J-e): expand the curvature term `R(·, γ̇)γ̇` in
the parallel frame of `exists_intrFrame` at each point of the intrinsic
radial geodesic, producing the frame-coordinate Jacobi system fed to
`forward_ode2_of_bound`.
