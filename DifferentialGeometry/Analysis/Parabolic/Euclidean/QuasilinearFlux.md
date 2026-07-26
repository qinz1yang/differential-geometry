# QuasilinearFlux

## Proved source boundary

The file source-proves the local algebraic and heat-kernel estimates that a
rough `C0` Ricci--DeTurck construction must retain:

- `coeffD2_refold` is the exact directional identity
  `A(u) D_p D_q w = D_p(A(u) D_q w) - DA(u)[D_pu] D_qw`;
- `fluxDiff_norm` is the two-arm coefficient-flux difference estimate;
- `coeffBCF` packages a coefficient flux as a bounded continuous function
  using only a zeroth-order coefficient bound along the path;
- `coeffBCF_diff` controls the spatial supremum norm by the `C0` difference
  of the states and the supremum difference of their first derivatives;
- `heatCoeff_diff` applies the precise `t^(-1/2)` first-heat-kernel bound to
  that nonlinear flux difference;
- `corrDiff_norm` retains and estimates the three arms of the compensating
  `DA(u)[Du] Dw` term;
- `fluxDiffWt` gives the resulting `C⁰`-stability estimate for the
  divergence flux in the `sqrt(t)|D·|` component of the rough norm;
- `corrDiffWt` gives the three-arm stability estimate for the compensating
  term in the `t|source|` component.  Both gradient factors and all time
  weights remain explicit.

No hypothesis bounds a derivative of the initial metric slice.  The
coefficient hypotheses are zeroth-order operator bounds and Lipschitz
dependence on the state value; the inverse-Gram perturbation APIs are the
intended geometric producer for these constants on a small positive-definite
metric ball.

## Exact remaining nonlinear step

`RoughCarleson.lean` now supplies the matching solution/source interface and
the elementary quadratic Carleson product estimate.  This file still does
not claim the full rough Duhamel contraction.  The
non-divergence compensating quadratic-gradient arm behaves like `t^(-1)` under
only pointwise `sqrt(t) * |Du|` control, so its time integral is not justified
by a bare supremum norm.  The faithful next layer is the local parabolic
heat-potential estimate mapping the weighted/Carleson source pair back into
the complete rough solution norm.  Omitting that layer would make the proof
false.

## Verification

The source contains no `sorry`, `admit`, axiom, opaque declaration, or
heartbeat override.  A focused Lean check is pending because the shared
parent build still owns the Lake lock.  Therefore Lean-verified machinery is
still 0%, and `ricci_flow_forward_unique` remains 0%.
