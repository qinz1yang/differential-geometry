# HarmonicPrincipal

## Source status

This file is source-written while the shared named Lean export owns the build slot.  Focused
elaboration is therefore still pending.  It contains no `sorry`, `admit`, axiom, opaque
replacement, new class, instance, or notation.

## Proved source facts

- `connAddTarget_fd` projects the already proved unipotent derivative of the component-local
  diagonal exponential to its target coordinate.  At the zero section its derivative is
  `(a,b) |-> a+b`.
- `connAdd_vert` specializes this to a vertical perturbation and proves the exact identity
  `D_V exp_x(V)|_{V=0} v = v` in the component-local chart.
- `hmfState` fixes the analytic carrier to the `(0,1)` tensor maximal-regularity state.  A
  covector carrier is intentional: `Musical.sharp_connLap` supplies its canonical vector
  realization without adding a second spectral theory.
- `hmfUnknown` realizes that carrier as a tangent field by the fixed metric sharp.
- `hmfPrincipal` is the sharp of the mixed `(0,1)` connection Laplacian, and
  `hmfPrincipal_eq` proves that it is exactly `connLaplacian_vector g0 hmfUnknown`.
- `connAdd_lap_vert` combines the two facts: the zero-section local-addition derivative leaves
  this frozen vector rough-Laplacian term unchanged.
- `hmfFlux q h` is the exact smooth-core first-order flux for a fixed target metric `q` and
  a moving domain metric `h`.  It inserts `h sharp o q flat - id` only into the leading
  covariant-gradient slot, so the full contraction of that slot is by `h^{-1}` while the
  target covector slot and target connection stay fixed at `q`.
- `hmfFlux_apply` proves this on every point and every two-slot model input.
  `hmfFlux_eq_full` lifts the identity to smooth tensors: the split
  fixed-plus-difference flux is insertion of the full endomorphism
  `h sharp o q flat` in the domain-derivative slot.
- `hmfMass q h` is the fixed target-fibre pairing integrated against `dmu_h`;
  `hmfMass_self` identifies its frozen case definitionally with the established tensor
  `L2(q)` pairing.
- `hmfWeakForm q h` is the corresponding divergence-form principal bilinear form and
  `hmfWeakForm_eq` exposes its split consumer normal form, while `hmfWeakForm_full` gives the
  integral contraction with the full inverse-cometric insertion.  Its only moving-domain
  objects are the inverse-metric flux coefficient and `dmu_h`: neither `covGrad h` nor a
  connection-difference coefficient occurs.
- `hmfFlux_self`, `hmfWeakForm_self`, and `hmfH1_self` identify the frozen flux with
  `covGrad q`, the frozen weak form with the established covariant-gradient `L2(q)` pairing,
  and frozen mass plus weak form with `tensorH1Inner q 0 1`.  Thus the intended completion is
  exactly the existing `TensorH1Compl q 0 1`.

These are genuine ingredients for specializing `TimeTameFixedPoint.time_partial_tame` to the
HMF unknown; they are not an existence wrapper and introduce no replacement hypothesis.

## Mathematical boundary

The full linearization of harmonic-map tension at the identity is a Jacobi operator.  Besides
the vector rough Laplacian it generally contains a curvature zero-order term (with sign fixed
by the repository's curvature convention).  This file therefore claims only the principal
second-order term.

Disconnectedness is not itself a blocker.  `ComponentRestrict.lean` restricts each endpoint
Ricci flow, its initial equality, joint regularity, and PDE to an open connected component;
on that component the local instances `connCompConnected` and `connCompCompact` permit use of
the existing intrinsic `diagExp`.  Its new `forward_of_comp` theorem also reassembles the
componentwise conclusion into ambient metric equality.  This avoids the invalid route of
trying to prove joint smoothness for the pointwise-selected global map
`p |-> connDiagExp p`.

The remaining geometric gap is more specific.  The repository still has no section-space
Nemytskii realization of `V |-> (x |-> exp_x(V x))`, and `HarmonicTension.lean` defines tension
only after a diffeomorphism has already been supplied.  A faithful route must either construct
general-map tension/pullback-connection before the solve, or prove uniformly on a small `C1`
section ball that every local-addition state is already a diffeomorphism and then use the
existing diffeomorphism tension.  The latter route can reuse
`NearIdentity.inj_of_unif_close`, `IsLocalDiffeomorph.clopen_range`, and
`bij_of_unif_close`, but still needs a compact-parametric inverse-function producer giving one
fixed local-injectivity cover for the entire small ball.

The edge audit also found no existing nonautonomous Lions theorem constructing a solution
from a time-dependent coercive form on `TensorH1Compl` with values in its dual.  The
`ScalarNonaut*` files construct strong loss-two operators and their time regularity;
`MetricLapDiffPair` is not the edge substitute because it controls a strong `H2 -> L2`
difference and assumes first metric-derivative bounds.

The Galerkin library is nevertheless reusable in three precise places:

- `Analysis.ODE.forward_solution_of_lipschitzWith_affineBound` already solves a genuinely
  time-dependent finite-dimensional ODE once its vector field is continuous in time and
  uniformly Lipschitz/affine-bounded in the state;
- `energy_hierarchy_explicit_bound` packages the scalar energy inequality once the moving-form
  derivative estimate is proved;
- `right_lipschitz`, `galerkin_subseq`, and `fatou_sq_mass` give modewise compactness and lower
  semicontinuity from uniform coordinate-derivative and mass bounds.

The diagonal heat identity `u_i' = -lambda_i u_i + F_i` and its autonomous Duhamel limit
identification are not reusable.  A moving HMF form first needs the finite mass matrix
`M_N(t)_{ij} = hmfMass q (g t) e_j e_i`, uniform positive definiteness and continuity of its
inverse, followed by the vector field
`-M_N(t)^{-1}(A_N(t)u - F_N(t))`.  Passing the moving bilinear form to the limit must then be
proved directly.

The new weak form shows that first metric derivatives are not mathematically needed for the
HMF principal part.  The global volume-measure subbrick is now source-written in
`Analysis/Integration/Measure/CompactVolumeEquiv.lean`.  Its compact-ratio proof uses only
joint chart-Gram `C0` regularity on the endpoint's closed subslab: on each finite-POU
`tsupport`, both chart-density ratios are continuous and positive, and
`chartLocalMeasure_lintegral` transports their compact bounds to the global measure.
`hmfVolumeEquiv` is the exact endpoint-shaped consumer and returns one two-sided measure
constant for all times in the same `Icc a c`.

This new chain is source-complete and has no `sorry`, but focused verification is deferred
until the shared global build releases the Lean runner.  The next mathematical step is to
combine it with the available pointwise inverse-metric/tensor norm comparison and obtain

```text
|hmfMass q h S T| <= C0 * ||S||_H1(q) * ||T||_H1(q),
|hmfWeakForm q h S T| <= C1 * ||S||_H1(q) * ||T||_H1(q),
c * ||S||_H1(q)^2 <= hmfMass q h S S + hmfWeakForm q h S S.
```

These estimates extend the forms by smooth-core density to `TensorH1Compl q 0 1`; time
continuity of their coefficients is then the input for the moving mass-matrix Galerkin solve.
Thus the volume-measure comparison is no longer the mathematical frontier; the exact next
frontier is the bounded/coercive extension of the smooth forms, followed by the finite
moving-mass-matrix ODE.

After that edge solver, the next geometric producer is a chart-level formula for the tension
of the local-addition map, split as

```text
mixed connection Laplacian of V + curvature/lower-order remainder,
```

together with the time-dependent three-arm tame estimate for that remainder.  One must also
prove finite-cover `C1` diffeomorphism persistence and the gauge PDE identity.  Thus HMF
existence and `ricci_flow_forward_unique` remain 0%.

## Honest accounting

- Exact endpoint `ricci_flow_forward_unique`: 0% until its existing Lean theorem is proved
  and checked.
- Zero-section/local-addition principal identification: source-complete, focused check pending.
- Moving-domain smooth weak principal form, full pointwise/tensor/integral contraction, and
  frozen `H1` identification: source-complete, focused check pending.
- Compact-subslab two-sided moving/reference volume-measure comparison and the
  endpoint-shaped `hmfVolumeEquiv` consumer: source-complete, focused check pending.
- `H1 -> H^{-1}` extension, uniform form bounds/coercivity, and nonautonomous form existence:
  0% theorem completion; the smooth-core coefficient and measure-comparison inputs are now
  source-written.

## 2026-07-19 coupled-Bochner edge audit

The variational construction is not by itself enough for the forward-uniqueness
consumer.  The consumer needs the resulting maps to be diffeomorphisms on one
window whose left endpoint is the merely `C0` metric edge.  The exact geometric
regularity ladder is now pinned down.

For a genuine smooth map heat flow

```text
F_t : (M, g(t)) -> (M, q),     partial_t F = tension_{g(t),q}(F),
partial_t g = -2 Ric(g),       F(0) = id,
```

the fixed-domain Bochner formula has a domain-Ricci contribution.  The time
derivative of the inverse domain metric contributes the opposite term because
`partial_t g = -2 Ric(g)`.  They cancel, leaving

```text
(partial_t - Delta_g) |dF|^2
  = -2 |nabla dF|^2 + 2 * target-curvature-quartic(dF).
```

Since `q` is fixed and compact, the target term is bounded by
`C(q) * |dF|^4`.  The existing scalar weak maximum principle can consume the
resulting logistic inequality and give a uniform short-time upper bound for
`|dF|`.  Thus the scalar comparison stage is already present in the repository;
the smallest missing genuine producer is the displayed coupled map Bochner
identity.

That identity cannot currently be stated at the needed general-map layer.  The
repository has no connection on the pullback bundle `F^* TM`, no covariant
Hessian of a general manifold-valued map, and no curvature commutator for that
connection.  `HarmonicTension.lean` deliberately starts after `F` is already a
diffeomorphism.  Specializing the Bochner identity to diffeomorphisms would be
circular here: diffeomorphism persistence is exactly what the edge estimate is
supposed to prove.

Moreover, the gradient upper bound alone is insufficient.  It neither gives a
lower singular-value bound for `dF` nor proves `dF -> id`.  A faithful edge
completion also needs both of the following quantitative conclusions on the
same window:

```text
sqrt(t) * |nabla dF(t)| <= C,
sup_x dist_q(F(t,x), x) = o(sqrt(t)).
```

The usual interpolation estimate then gives `sup |dF(t)-id| -> 0`, after which
the already available near-identity topology can supply a diffeomorphism.  The
first estimate is a coupled Bernstein/Bochner theorem; the second is a
boundary displacement estimate using the uniform `C0` convergence of `g(t)`
to `q`.  Neither estimate is currently present.  The finite Galerkin `H1`
bound cannot substitute for them.

Consequently the honest HMF edge frontier is not another form-extension
wrapper.  It is the general-map pullback-connection/Bochner layer, followed by
the weighted Hessian and little-oh displacement estimates above.  The exact
endpoint `ricci_flow_forward_unique` remains 0%.
