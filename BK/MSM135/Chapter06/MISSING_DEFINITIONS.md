# MSM135 Chapter 6 Missing Definitions

The first-pass Lean files intentionally avoid pretending that these APIs already
exist.

## Measure And Entropy

- Riemannian integral notation for time-dependent metrics.
- Weighted density normalization:

```text
integral_M (4*pi*tau)^(-n/2) * exp(-f) dmu_g = 1
```

- Conjugate heat equation and adjoint heat operator.
- First variation of `W`, including variation of volume form and integration by
  parts.
- Square-completion proof for Perelman's `W` monotonicity.

## `mu` And `nu`

- Admissible function space for `f` or `u`.
- Infimum API connecting:

```text
mu(g,tau) = inf_f W(g,f,tau)
nu(g) = inf_tau>0 mu(g,tau)
```

- Existence of minimizers for `mu` and `nu`.
- Diffeomorphism invariance of `mu` and `nu`.
- Cheeger-Gromov convergence vocabulary compatible with entropy.

## Log-Sobolev

- Sobolev spaces on manifolds and Euclidean space in the form used by MSM135.
- Manifold and Euclidean logarithmic Sobolev inequalities.
- The route from log-Sobolev lower bounds to finiteness of `mu`.

## No Local Collapsing

- Metric balls and volumes for time-dependent metrics.
- Curvature-controlled scale hypotheses:

```text
|Rm| <= r^(-2)
```

- Local collapsing sequence definition.
- Hamilton little-loop conjecture vocabulary.
- Pointed limits and preservation of noncollapsing.
- Injectivity radius lower-bound comparison.
- Hamilton compactness and finite-time singularity-model extraction.

## Improved NLC And Diameter Control

- Local eigenvalue comparison in the form used by Cheng's estimate.
- Topping diameter-control estimate.
- Improved no-local-collapsing constants depending on local entropy quantities.

## Further Calculations

- Weighted modified scalar curvature variation.
- Second variation bilinear form for `F` and `W`.
- Matrix Harnack calculation for the adjoint heat equation.
