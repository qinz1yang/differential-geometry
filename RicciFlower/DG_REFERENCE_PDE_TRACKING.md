# DG Reference PDE Tracking

This note tracks development-useful material from the local reference snapshot.
Treat reference files as route guidance only: do not import reference modules
into RicciFlower, do not track the ignored snapshot, and do not create a
parallel API just because a reference theorem has a convenient shape.

## Snapshot

- Current reference source: `upstream/measure` or the ignored snapshot
  `.reference/qinz1yang-differential-geometry-measure/`.
- Old `DGreference/` paths may still appear in older notes; they are reference
  vocabulary, not import targets.
- This file is an inventory and routing note, not a verification certificate.
  Recheck any referenced theorem narrowly before porting its statement.

## Development Policy

Use the reference tree as a proof-route and interface guide.  The RicciFlower
version should live in the closest native layer:

- tensor/component algebra in `RicciFlower/Tensor` or
  `RicciFlower/Coordinates`;
- scalar, gradient, divergence, and Laplacian operators in
  `RicciFlower/Operators`, `RicciFlower/Analysis`, or `RicciFlower/Realized`;
- Ricci-flow evolution and maximum-principle consumers in
  `RicciFlower/RicciFlow` and `RicciFlower/MaximumPrinciple`;
- global PDE existence, compactness, and regularity assumptions in an explicit
  analytic/global layer.

Do not use a reference theorem to hide a missing RicciFlower producer.  If the
native adapter is missing, keep the local frontier visible and state the
smallest RicciFlower bridge lemma.

## High-Value Candidate Lanes

### DeTurck Vector Field

Useful reference patterns:

- connection-difference tensors and smoothness;
- metric trace of connection difference;
- DeTurck vector field in local charts.

RicciFlower use: future short-time existence or DeTurck wrappers, after the
Levi-Civita smoothness and connection-difference APIs are stable.

### Scalar Heat Maximum Principle

Useful reference patterns:

- maximum principle on closed manifolds;
- perturbation argument for weak scalar heat inequalities;
- heat semigroup smoothing facts.

RicciFlower use: compare against `MaximumPrinciple/ScalarWeak.lean` and keep
the RicciFlow consumers phrased through RicciFlower scalar heat predicates.

### Tensor Heat And Quasilinear Parabolic Inputs

Useful reference patterns:

- tensor spectral boundary conditions;
- tensor heat equation interfaces;
- quasilinear parabolic existence shape.

RicciFlower use: future tensor maximum principle and long-time Ricci-flow
regularity; not a replacement for the current local tensor algebra.

### Sobolev, DeGiorgi, Moser, Harnack

These are future analytic foundations.  Do not port them until a concrete
global theorem needs the exact interface.

### Divergence Theorem And Boundary Green Identities

Closed-manifold Green identities already have a RicciFlower route through
`Analysis/Green.lean` and `Analysis/DivergenceTheorem`.  With-boundary versions
should remain deferred until there is a boundary theorem consumer.

### Synthetic Ricci-Flow And Dimension-Three Algebra

Use synthetic/reference files only to audit statement shape and convention.
RicciFlower endpoints should consume native dimension-three algebra,
curvature-component APIs, and local flow packages.

## Priority Queue

1. Keep Section 10 trace-free Ricci and pinching work on native RicciFlower
   producers.
2. Use reference scalar/tensor maximum-principle material only when it gives a
   concrete missing RicciFlower analytic interface.
3. Defer DeTurck/short-time existence until the current local evolution and
   pinching producers are stable.
4. Do not port broad Sobolev, DeGiorgi, or Harnack stacks without a named
   theorem consumer.

## Open Risks

- Reference modules use different namespaces and may depend on infrastructure
  intentionally absent from RicciFlower.
- Some reference comments may have encoding damage; proof terms may still be
  informative, but copied prose should be normalized.
- Any migration must preserve RicciFlower valence, component-order,
  curvature-sign, and time-interval conventions.
