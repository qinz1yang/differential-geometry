# HarmonicEnergy status

## Role

This file is the finite-dimensional analytic entrance to the harmonic-map
heat-flow gauge.  It realizes a small lowered tangent tensor by the intrinsic
exponential map, defines the moving-domain Dirichlet energy, and defines its
frozen-time finite-spectral first variation.

The moving measure is essential, but it is not by itself the full mass form
for exponential-section coordinates.  If
`Phi_S(x) = exp^q_x(q sharp S(x))`, the faithful state mass is

```text
M(t,S)(U,V) = integral q_(Phi_S(x))
  (D_S Phi_S[U](x), D_S Phi_S[V](x)) dmu_(g(t)).
```

The current `hmfMass q h U V` is only its zero-section value: it moves the
domain measure but omits the two local-addition differential factors.  Thus
raising the full nonlinear energy derivative by the current `hmfMass` away
from `S = 0` is not faithful.  This objection applies to the finite
Galerkin/energy-gradient route, not automatically to a strong rough equation:
there the vertical differential in `Phi_t` should cancel the identical
top-order differential in the tension after a full-state chain-rule theorem.

## Current proved/source-written facts

- The zero lowered tensor realizes the identity map, and its spatial
  differential is the identity.
- The finite-spectral launch map from coefficient space times `M` to `TM` is
  jointly smooth.
- For each fixed finite mode set and each finite differentiability order,
  compactness of `M` gives one positive coefficient radius on which the
  diagonal exponential is smooth for every base point.
- On that radius, the exponential-section map is jointly smooth in the
  coefficient and manifold point.
- `hmfSpecResid` is the negative frozen-time first variation of the genuine
  moving-volume Dirichlet energy.  `hmfSpecPrin` has the forced dissipative
  sign, and `hmfSpecLow` is its exact algebraic remainder.  These covectors are
  valid, but the existing `hmfSpec_exists` must not be used as the nonlinear
  HMF producer until its mass matrix is replaced by the state mass above.
- The principal form has a spectral-cutoff-independent coercive lower bound
  whenever the moving metric satisfies the existing inverse-cometric and
  volume-comparison inputs.

The newly added local-addition statements still require a focused Lean check;
the shared named upstream build was active when they were source-written.

## Important uniformity distinction

The radius supplied by `hmfSpecChart` is uniform in the point of `M`, but may
depend on the finite mode set.  It must not be advertised as uniform in the
spectral cutoff.  A cutoff-uniform neighborhood has to be measured in a
supercritical intrinsic Sobolev norm (in dimension three, at least `H2` for
pointwise control), using the existing spectral Sobolev embedding.  The plain
Euclidean coefficient norm is the frozen `L2` norm and cannot provide a
cutoff-uniform pointwise local-addition radius.

## Failed/abandoned route

`Analysis/Parabolic/Euclidean/HmfRoughFixedPoint.lean` is still only an
experimental strong formulation, but the moving state mass is not by itself
an obstruction to that route.  Its actual missing geometric facts are the
full-state top-order cancellation and the value dependence of the
quadratic/local-addition coefficient.  It must not be connected to the public
uniqueness endpoint before those are proved.

## Exact frontier

For the Galerkin route, the next mathematical producer is the local-addition state mass.  On a
supercritical Sobolev ball, prove joint regularity of the pointwise map and its
coefficient differential, define the two-differential Gram density above,
prove its zero-section identity and uniform local coercivity, and use it in
the finite-dimensional ODE.  In parallel, prove joint regularity of the
Dirichlet density and its vertical derivative.  `FiniteParametricIntegral.lean`
and `FamilyContinuityParam.lean` can then supply continuity of both the state
mass and energy covector.  Only this corrected ODE (or the equivalent
inverse-Jacobi strong equation) can be identified with genuine HMF.  The
strong route may bypass the mass inversion only after proving the exact
full-state cancellation described above.

After that, the Galerkin lane still needs moving-energy differentiation,
cutoff-uniform higher-order estimates, time compactness, passage of the
nonlinear residual, and smoothing to a `C1`-small diffeomorphism.  An `H1`
bound alone is not `C1` control in dimension three.

## Honest completion

- `ricci_flow_forward_unique`: **0%** (exact theorem not proved).
- Finite moving-mass/Galerkin and local-addition machinery: **about 35%**.
- Full HMF gauge construction through a common positive window: **about 15%**.

These percentages describe machinery only and do not change the endpoint
accounting.
