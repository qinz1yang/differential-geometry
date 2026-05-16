# DG Reference PDE Tracking

This note tracks development-useful material from the local, ignored
`DGreference/` tree. Treat these files as reference only: do not import
`DGreference.*`, do not move the tree into git, and do not transplant broad
`DifferentialGeometry.*` subtrees into RicciFlower.

## Snapshot

- `DGreference/` is ignored by git and remains local reference material.
- Current reference tree size inspected: 1310 Lean files.
- Main `DGreference/DifferentialGeometry` distribution:
  - `Analysis`: 528 files.
  - `Integral`: 112 files.
  - `External`: 92 files.
  - `Synthetic`: 61 files.
  - `Tensor`: 60 files.
  - `Realized`: 18 files.
  - `Geometry`: 13 files.
  - `Coordinates`: 8 files.
  - `VectorBundle`: 8 files.
  - `DifferentialForm`: 4 files.
  - `PDE`: 4 files.
- PDE/analysis areas sampled here had no visible `sorry` tokens in the sampled
  files and no `sorry` tokens under:
  - `DGreference/DifferentialGeometry/PDE`.
  - `DGreference/DifferentialGeometry/Analysis/Parabolic`.
  - `DGreference/DifferentialGeometry/Analysis/Laplacian`.
  - `DGreference/DifferentialGeometry/External/DeGiorgi`.
- This was an inventory pass, not a Lean verification pass. The reference tree
  should be rechecked narrowly before porting any statement.

## Development Policy

Use the reference tree as a proof-route and interface guide. The RicciFlower
version should live in the closest native layer:

- tensor/component algebra in `RicciFlower/Tensor` or
  `RicciFlower/Coordinates`;
- scalar, gradient, divergence, and Laplacian operators in
  `RicciFlower/Operators` or `RicciFlower/Realized`;
- Ricci-flow evolution and maximum-principle consumers in
  `RicciFlower/RicciFlow` and `RicciFlower/MaximumPrinciple`;
- global PDE existence, compactness, and regularity assumptions in
  `RicciFlower/RicciFlow/Global` or an explicitly analytic layer.

Do not use a reference theorem to hide a missing RicciFlower producer. If the
local RicciFlower adapter is missing, keep the local frontier visible and state
the smallest bridge lemma.

## High-Value Candidate Lanes

### DeTurck Vector Field

Reference files:

- `DGreference/DifferentialGeometry/PDE/DeTurck/ConnectionDifference.lean`
- `DGreference/DifferentialGeometry/PDE/DeTurck/MetricTrace.lean`
- `DGreference/DifferentialGeometry/PDE/DeTurck/VectorField.lean`
- `DGreference/DifferentialGeometry/PDE/DeTurck/VectorFieldSmooth.lean`

Useful reference statements and patterns:

- `connDiff`, `connDiff_apply`, `connDiff_self`.
- `connDiff_contMDiff`, `connDiff_contMDiffOn`,
  `connDiff_contMDiffOn_local`.
- `deTurckChartLocal`, `deTurckFun`, `deTurckVF`.
- `deTurckChartLocal_eq_deTurckFun`,
  `deTurckChartLocal_contMDiffOn`, `deTurckFun_contMDiff_total`.

RicciFlower use:

- Best near-term use is a RicciFlower-native DeTurck vector-field interface
  after the Levi-Civita smoothness and connection-difference APIs are stable.
- The proof route is local-frame/chart trace plus a cutoff to feed Mathlib's
  global smooth section slot requirements.
- This can support a future DeTurck wrapper around the short-time existence
  black box, but should not replace the current global PDE black-box boundary
  by a shallow assumption stack.

### Scalar Heat Maximum Principle

Reference files:

- `DGreference/DifferentialGeometry/Analysis/HeatEquation/MaximumPrinciple.lean`
- `DGreference/DifferentialGeometry/Analysis/HeatEquation/Semigroup.lean`
- `DGreference/DifferentialGeometry/Analysis/HeatEquation/Smoothing.lean`
- `DGreference/DifferentialGeometry/Analysis/HeatEquation/SmoothingUnconditional.lean`

Useful reference statements and patterns:

- `laplacian_nonpos_at_max`.
- `heat_max_principle_weak_closed`.
- `heatSemigroup`, `heatSemigroup_zero`, `heatSemigroup_add`,
  `heatSemigroup_continuous_at_zero`.
- smoothing representatives for positive time.

RicciFlower use:

- Compare `laplacian_nonpos_at_max` against
  `RicciFlower/Operators/LaplacianMinimum.lean`.
- Use the perturbation argument in `heat_max_principle_weak_closed` as a route
  check for `RicciFlower/MaximumPrinciple/ScalarWeak.lean`.
- Keep current RicciFlow consumers phrased through RicciFlower's scalar
  heat-operator predicates rather than importing the reference heat equation
  stack.

### Tensor Heat And Quasilinear Parabolic Inputs

Reference files:

- `DGreference/DifferentialGeometry/Analysis/Parabolic/TensorSpectral/*`
- `DGreference/DifferentialGeometry/Analysis/Parabolic/TensorHeatEquation/*`
- `DGreference/DifferentialGeometry/Analysis/Parabolic/TensorLinearParabolic.lean`
- `DGreference/DifferentialGeometry/Analysis/Parabolic/QuasiLinear/Existence.lean`
- `DGreference/DifferentialGeometry/Analysis/Parabolic/QuasiLinear/TensorInstance.lean`

Useful reference statements and patterns:

- `TensorH1ComplToTensorL2`, `tensorH1Compl_to_tensorL2_relatively_compact`.
- `tensorResolventL2`, tensor resolvent spectral data, and
  `tensorLaplacianEigenvalueOf`.
- `tensorHeatSemigroup`, `tensorHeatSemigroup_opNorm_le_one`,
  `tensorHeatSemigroup_continuous_on_nonneg`.
- `tensorMildSolution`, `tensor_linear_parabolic_existence`.
- `semilinear_parabolic_existence`, `semilinear_parabolic_unique`.
- `tensorBoundedC0Semigroup`,
  `tensor_quasilinear_parabolic_existence`,
  `tensor_quasilinear_parabolic_unique`.

RicciFlower use:

- This is the most relevant long-term source for a tensor maximum principle,
  tensor heat semigroup, and analytic existence story.
- Near-term RicciFlower should keep these as analytic input shapes, not attempt
  a broad port. The likely first native target is a small theorem-shaped
  interface in a global/analytic Ricci-flow module, with concrete tensor
  spectral infrastructure deferred.
- Component and chart-frame estimates may later inform tensor-section
  Sobolev/L2 bridges, but should go through RicciFlower component APIs rather
  than model tensor internals.

### Sobolev And Elliptic Regularity

Reference files:

- `DGreference/DifferentialGeometry/Analysis/Sobolev/Intrinsic/*`
- `DGreference/DifferentialGeometry/Analysis/Sobolev/Manifold/*`
- `DGreference/DifferentialGeometry/Analysis/Sobolev/Euclidean/*`
- `DGreference/DifferentialGeometry/Analysis/Sobolev/Approximation/*`
- `DGreference/DifferentialGeometry/Analysis/Sobolev/WithBoundary/*`
- `DGreference/DifferentialGeometry/Analysis/Laplacian/Regularity/*`

Useful reference statements and patterns:

- `HasWeakRiemannianGrad`, `MemW1pIntrinsic`, `w1pNormIntrinsic`.
- `MemW1pIntrinsic_of_contMDiff`.
- `contMDiff_dense_in_WkpChart`.
- `h2_loc_chart_pulled`, `h2_loc_chart_pulled_manifold`.
- `laplacianDomainPow`, iterated chart bootstrap statements, and Hessian/Lp
  bridge modules.

RicciFlower use:

- This is useful for future analytic groundwork and regularity notes.
- It is not an immediate route to current Ricci-flow evolution identities,
  which are still tensor/operator producer problems.
- If ported, start with one small closed-manifold Sobolev interface, not the
  with-boundary tree.

### DeGiorgi, Moser, Harnack

Reference files:

- `DGreference/DifferentialGeometry/External/DeGiorgi/*`
- `DGreference/DifferentialGeometry/External/DeGiorgi/WeakFormulation/*`
- `DGreference/DifferentialGeometry/External/DeGiorgi/Supersolutions/*`
- `DGreference/DifferentialGeometry/External/DeGiorgi/MoserIteration/*`
- `DGreference/DifferentialGeometry/External/DeGiorgi/Holder/*`

Useful reference statements and patterns:

- `WeakProblem`, `IsWeakSolution`, `IsSubsolution`,
  `IsSupersolution`, `IsHomogeneousWeakSolution`.
- `harnack`, `harnack_of_homogeneousWeakSolution`.
- `holder_Moser`, `holder_Moser_of_homogeneousWeakSolution`.

RicciFlower use:

- Treat as external analytic theory. It may justify future regularity and
  compactness assumptions, but it is too broad for immediate RicciFlower
  migration.
- The weak-solution interfaces are the most reusable design hint if
  RicciFlower later needs a local PDE hypothesis shape.

### Divergence Theorem And Boundary Green Identities

Reference files:

- `DGreference/DifferentialGeometry/Integral/DivergenceTheorem/*`
- `DGreference/DifferentialGeometry/Integral/DivergenceTheorem/WithBoundary/*`

Useful reference statements and patterns:

- Green identities, integration-by-parts statements, Stokes/divergence theorem
  wrappers, surface measure, outward normal, and boundary trace links.

RicciFlower use:

- Useful if future analytic work needs boundary manifolds, Green identities, or
  integration by parts.
- Current Hamilton closed-manifold Ricci-flow path should only borrow local
  route ideas, because the with-boundary stack has a large API footprint.

### Synthetic Ricci-Flow And Dimension-Three Algebra

Reference files:

- `DGreference/DifferentialGeometry/Synthetic/Flow/RicciFlow/Evolution/*`
- `DGreference/Books/Synthetic/Flow/RicciFlow/DimensionThree/*`

Useful reference statements and patterns:

- `connection_evolution`, `laplacian_evolution`,
  `scalar_curvature_evolution`, `riemann_variation_raw`.
- `RiemannFromRicci3DFinThreeComponentPackage`,
  `RiemannFromRicci3DTraceEigenframePackage`.
- `ricciReactionContractionIdentity_from_dim3_calculus`.
- `hamilton3D_tracefree_norm_heat_eq_of_trace_eigenframe_packages`.
- Hamilton cubic and improved-pinching quotient data/producers.

RicciFlower use:

- Good proof-route map for Sections 6, 8, 9, and 10.
- Use as a checklist for native theorem shapes, especially finite-frame
  component packages and eigenvalue realization handoffs.
- Do not route RicciFlower tensor calculations through `Synthetic`; extract
  small local tensor/component lemmas into RicciFlower instead.

## Priority Queue

1. Compare the DeTurck vector-field stack against current RicciFlower
   Levi-Civita smoothness and metric-family APIs. First bridge target:
   connection-difference tensor plus metric trace as a native RicciFlower
   interface.
2. Compare the scalar maximum-principle proof route with
   `RicciFlower/MaximumPrinciple/ScalarWeak.lean` and
   `RicciFlower/Operators/LaplacianMinimum.lean`. Only port the missing local
   minimum/Laplacian facts if they shorten current proofs.
3. Use tensor heat/quasilinear parabolic files to design theorem-shaped
   analytic inputs for short-time existence and tensor maximum principles.
   Do not port the spectral stack until a concrete consumer requires it.
4. Use the dimension-three algebra files to check current RicciFlower
   component-package interfaces for Riemann-from-Ricci, reaction contraction,
   and improved pinching.
5. Defer broad Sobolev, DeGiorgi, and with-boundary migration. These are
   future analytic foundations, not immediate evolution-identity dependencies.

## Open Risks

- The reference tree uses `DifferentialGeometry.*` module paths and may depend
  on infrastructure that is intentionally absent or differently named in
  RicciFlower.
- Some reference files have mojibake in comments when viewed from the current
  PowerShell session; proof terms may still be usable, but copied prose should
  be normalized before reuse.
- The inspected PDE/analysis areas had no visible `sorry` tokens, but this
  note did not run Lean checks on reference modules.
- Any migration must preserve RicciFlower's existing tensor valence,
  component-order, and time-split conventions.

