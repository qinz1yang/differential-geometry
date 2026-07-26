# EdgeLowerPairing

## Proved-source facts

- `edgeLowerArm` packages an order-zero coefficient acting on the metric
  difference together with an order-one coefficient acting on its first
  background covariant derivative.
- `edgeLower_pair_le` proves the exact fixed-time estimate
  `pair <= (1/4) * ||nabla W||^2 + (B0 + B1^2) * ||W||^2` from pointwise
  fibre-norm bounds on those two coefficient fields.  It uses no coefficient
  derivatives and no high Sobolev norm of `W`.
- `edgeCoreArm` adds the fixed connection Laplacian and the variable-cometric
  principal arm.
- `edgeCore_pair_le` combines the lower estimate with
  `edgePrincipal_half`.  Under the existing `C0` realization and smallness
  hypotheses its gradient coefficient is `-1/4`, leaving only
  `(B0 + B1^2) * ||W||^2`.
- `edgeTop_split` is the exact arbitrary-realized-metric refold of the full
  top coefficient into the fixed connection Laplacian, the small cometric
  principal arm, and `phiMetCurvCoeff` acting at order zero.
- `edgeCarry0` / `edgeCarry1` contain only fixed carrier/background
  coefficients. `edgeQuad0` / `edgeQuad1` contain the nonlinear residuals;
  crucially `edgeQuad0` is not mislabeled as a bounded reaction coefficient.
- `edgeSlope_split` specializes `rhsSlope_eq_arms` to the closed initial-edge
  pair `(W, 0)` and proves the exact pointwise decomposition
  `principal + edgeCarryArm + edgeQuadArm`.  It assumes no spatial derivative
  bound on the arbitrary endpoint metric.

The source contains no `sorry`, `admit`, or new axiom.  A focused Lean check is
pending the coordinated named dependency build in the shared worktree.

## Exact role and remaining frontier

The exact coefficient identity is now present in source.  The remaining
mathematical goal is one joint nonlinear pairing estimate, not separate
coarse bounds on `edgeQuad0` and `edgeQuad1`.  At fixed carrier `g`, with
`g1 = g + W` and `||W||_{C0,g} <= delta`, prove constants depending only on
closed-edge carrier/background bounds such that

`<W, edgeQuadArm g g1 g_bg W>_{L2(g)}`

is at most `C * delta * ||nabla W||_2^2 + K * ||W||_2^2` (with the first
coefficient small enough for the remaining principal absorption).  The
`nabla(connDiff(g1,g)) * W` part of `edgeQuad0` must be integrated by parts
together with `edgeQuad1`; this converts `W * nabla^2 W` into the admissible
`W * (nabla W)^2` structure.  Bounding `edgeQuad0` first would introduce an
inadmissible constant depending on `nabla g1`.

After that joint estimate, the fixed coefficients in `edgeCarry0/1` are fed
to `carrierEdge_bounds`, and the resulting additive estimates feed the moving
energy/Gronwall layer.

A compact-slab supremum on `[epsilon,T]` is not sufficient because its
constant may diverge as `epsilon` tends to zero.  The current next target is
therefore the exact coefficient split feeding the scalar estimate
`movingRate <= K * movingDiffEnergy`, not another abstract Gronwall wrapper.

## Honest status

- Generic fixed-time lower pairing: 85% (source complete; check pending).
- Concrete Ricci--DeTurck exact RHS realization: 70% machinery (exact source
  split added; coordinated focused check and the joint residual estimate are
  still pending).
- `ricci_flow_forward_unique`: 0% until the public theorem is proved and
  verified.
