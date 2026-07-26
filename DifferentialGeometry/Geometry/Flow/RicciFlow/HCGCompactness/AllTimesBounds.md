# AllTimesBounds

## 2026-07-12 — short-time branch alignment

- Four frame-sum proofs now use both the underlying multilinear slot-linearity theorem and the opaque `Tensor0SSpace` projection theorem.
- The connection-difference sign calculation now normalizes tensor negation before scalar evaluation.
- Focused verification passed without `sorry`; this repairs consumer compatibility and does not change the HCG theorem frontier.

## Source

This file follows MSM135 Chapter 3, Lemma 3.11, "Derivative of metric bounds
at one time to all times."

## Definitions

- Added raw fixed-domain predicates for uniform metric equivalence on a set,
  metric covariant-derivative bounds using the existing `metricCovDeriv`, and
  curvature-derivative bounds using the existing `curvDerivNorm`.
- Kept compactness out of the raw bound predicates.  Compactness of `K` is
  carried by `MetricAllTimesBoundsInput`, the theorem-facing package for the
  MSM135 compact-window hypothesis.
- Added the scalar logarithmic-derivative estimate behind MSM135 equation
  (3.3), using Mathlib's one-dimensional mean value theorem.
- Added `MetricLogDerivativeInput`, a concrete theorem-facing package for the
  fixed-vector metric derivative identity, logarithmic integrability data, and
  the existing `TwoTensorQuadBoundOnWindow`.
- Proved `metricUniformEquivalentOnWindow_of_logDerivativeInput`, propagating
  metric equivalence at `t0` to the whole window with
  `metricEquivalenceFactor C A t t0 = C * exp (2 * A * |t - t0|)`.
- Added `MetricAllTimesSpatialConclusion` for the spatial part of Lemma 3.11.
- Added the 1D spatial assembly layer:
  `metricCovCumulativeConstant`, `metricCovBoundsWindow_of_orderBounds`,
  `MetricAllTimesSpatialInput`, and `metricAllTimes_spatial`.  This packages
  exact-order window bounds into the cumulative spatial conclusion without
  adding any new producer assumptions.
- Added the Phase 2A mixed time-spatial API:
  `metricMixedDeriv`, `metricMixedDerivNorm`,
  `metricMixedDerivNorm_zero`, `MetricMixedDerivBoundOnWindow`,
  `MetricMixedDerivBoundsOnWindow`, their pointwise window bridges, and the
  full `MetricAllTimesConclusion` package.
- Added the Phase 2B q=1 mixed estimate API:
  `MetricMixedDerivOneEvolutionOn`, `metricMixedDeriv_one_eq_of_evolution`,
  `normSq0S_smul`, `sqrt_normSq0S_smul`, `metricMixedOneConstant`, and
  `metricMixedOneWindow_of_ric_bound`, with
  `metricMixedOneWindow_of_evolution` as the wrapper that consumes a
  `MetricCovOrderEvolutionInput`.  The q=1 theorem takes the order-`p`
  evolution input, the already-proved spatial order-`p` window bound, and an
  explicit norm-compatible realization of
  `partial_t nabla^p g = -2 nabla^p Rc` in `metricMixedDeriv`.
- Added the general q >= 1 honest-input mixed estimate API:
  `MetricMixedDerivLayerEvolutionOn`, `metricMixedQConstant`, and
  `metricMixedQWindow_of_evolution`.  This reuses the direct
  `metricMixedDeriv` equation pattern from the q=1 theorem and leaves the Shi
  estimates, time-differentiated Ricci layer, and schematic product bound as
  explicit producer inputs.
- Added `norm_le_initial_add_deriv_bound`, the vector-valued mean-value
  estimate used by the book when integrating the Christoffel-symbol derivative
  bound in equation (3.10).
- Added `lcMetricFamily`, the HCG-local bridge that attaches the
  Levi-Civita connection to a plain time-dependent metric family.
- Added `metricCovDeriv_one_component_eq_metricCovAtBase` and its
  `componentL2Sq3` version, identifying the HCG first derivative
  `metricCovDeriv ... 1` with the fixed-base covariant metric derivative used
  by the Christoffel estimates.
- Added `metricGammaEquiv`, the invariant HCG form of MSM135 equations
  (3.8)--(3.9): in a `g_k(t)`-orthonormal local frame, the norm of the
  connection-difference `(1,2)` tensor and the norm of `nabla^g g_k(t)` are
  bounded by the book's factors `3 / 2` and `2`.
- Added `componentVec3`, `norm_componentVec3`,
  `hasDerivAt_componentVec3`, and `componentL2_le_initial_add`, viewing a
  three-index component array as a finite Euclidean vector so the book's
  `l^2` integration step can reuse the existing vector endpoint estimate.
- Added `gammaL2_le_initial_add`, the component-`l^2` form of MSM135 equation
  (3.10): the Ricci-flow Christoffel variation component formula plus a
  uniform `|nabla_k Rc_k|` bound gives an initial-size-plus-linear-time bound
  for `Gamma_k(t) - Gamma`.
- Added `sqrt_normSq0S_three_diag_le`, the square-root `(0,3)` diagonal
  norm-comparison step from Lemma 3.13 needed for the `B(t,t0)^(3/2)` factor
  in equation (3.11).
- Added `exists_diagInv_of_metricUniformEquivalentOn`, producing the local
  eigenbasis and diagonal inverse-metric data from pointwise metric
  equivalence.
- Added `metricUniformEquivalentOn_symm`,
  `sqrt_normSq0S_three_le_of_metricUniformEquivalentOn`, and the symmetric
  direction, giving the concrete `(0,3)` norm comparison used in MSM135
  equation (3.11).
- Added `covOne_le_connDiff` and `connDiff_le_covOne`, the checked
  first-order bridges between the background norm of `nabla^g g_k`, the
  moving norm of `Gamma_k - Gamma`, and the initial background metric
  derivative norm.
- Added within-interval and carrier-subset versions of the component endpoint
  estimates, so Ricci-flow producers stated as `HasDerivWithinAt` on a
  solution carrier can be integrated on `Set.uIcc a b`.
- Added `gammaL2_le_initial_add_regular` and
  `gammaL2_le_of_christoffel`, feeding regular-time Christoffel evolution plus
  an identity inverse-metric frame into the MSM135 equation (3.10) component
  estimate.
- Added `metricCovBound_of_pointwise`, `metricCovAtTime_of_pointwise`, and
  `metricCovWindow_of_pointwise`, the assembly bridges from pointwise
  estimates to the existing supremum/window predicates used in the statement of
  (3.4).
- Added `MetricCovDerivOrderBoundOn`,
  `MetricCovDerivOrderBoundOnWindow`, and the exact-order window packaging
  lemmas. These separate the book's exact-order estimates from the cumulative
  `0..p` supremum predicate used by convergence definitions.
- Added `covOne_le_diff` and `diff_le_covOne`, two-metric forms of the
  first-order metric/connection-difference comparison.  These avoid introducing
  an artificial time family when MSM135 uses a fixed background metric.
- Added `normSqRS12_eq_l2`, `covOne_le_diff_basis`,
  `diff_le_covOne_basis`, `covOne_le_diff_basis_ref`, and
  `diff_le_covOne_basis_ref`. These are pointwise basis-level replacements for
  the first-order local-frame norm comparison: the algebraic parts of MSM135
  equations (3.8)--(3.9) no longer require a global local frame, only a
  pointwise orthonormal basis and the concrete component identities.
- Added `localFrameOneOfInf`, `diffNormSq_eq_l2`,
  `covOne_le_christoffel`, and `covOne_le_init`.  Together these assemble the
  first-order pointwise estimate from MSM135 equations (3.10)--(3.11): integrate
  the Christoffel evolution, compare component `l^2` and invariant norms, and
  replace the initial connection-difference term by an initial
  `|nabla g_k(t0)|` constant.
- Added `metricUniformEquivalentOn_of_le`,
  `MetricAllTimesFirstOrderInput`,
  `MetricAllTimesFirstOrderConclusion`, and
  `metricAllTimes_firstOrder`.  These complete the Phase 0 first-order
  window assembly of Lemma 3.11: equation (3.3) provides the metric-equivalence
  window, `covOne_le_init` provides the pointwise exact-order-one estimate, and
  `metricCovOrderWindow_of_pointwise` packages it into a uniform
  `MetricCovDerivOrderBoundOnWindow ... 1` conclusion.  The theorem-facing
  input deliberately carries the local frame, inverse-metric component data,
  and the uniform `nabla Ric` component bound as producer inputs rather than
  deriving them from curvature bounds in this pass.
- Added the scalar analytic pieces for the higher-order part of Lemma 3.11:
  `affineGronwall_of_abs_deriv_le` and
  `hasDerivAt_normSq_abs_deriv_le`.
- Added the order-`p` analytic assembly layer:
  `metricCovOrderEvolutionAlpha`, `metricCovOrderEvolutionBeta`,
  `metricCovOrderEvolutionConstant`, `MetricCovOrderEvolutionOn`,
  `MetricCovOrderNormSqEvolutionOn`, `MetricCovOrderEvolutionInput`, and
  `metricCovOrderWindow_of_evolution`.  The theorem proves the all-times
  exact-order bound with constant
  `sqrt (exp ((1 + 8 * Cpp^2) * timeRadius) *
    (initC^2 + (8 * Cppp^2 + 1) / (1 + 8 * Cpp^2)))`.
- **Equation (3.3) is now closed from a Ricci-flow solution sequence.**  The
  producer chain lives in `AllTimesBoundsFlow.lean` and the new foundational
  curvature/metric files it leans on:
  - ① curvature input (`TwoTensorQuadBoundOnWindow`): the general-dimension
    operator-norm (Rayleigh) Ricci bound `|Rc(t)(V,V)| <= A * g(t)(V,V)` with
    `A = n^2 * sqrt C`, via `twoTensorQuadBound_of_solutions` →
    `ricciAt_unitQuad_le_of_sol` → `ricci_unitQuad_le_of_trace`
    (`Geometry/Curvature/RicciOperatorNormBound{,Flow}.lean`,
    `Geometry/Curvature/QuadraticFormBound.lean`).  The first factor is the
    operator norm obtained by homogeneity, not a Hilbert–Schmidt
    Cauchy–Schwarz factor.
  - ② time-`0` metric equivalence from Cheeger–Gromov convergence
    (`exists_uniform_equiv_of_metricCPConv`, now hypothesis-free: the
    `BddAbove`/`hle` content is discharged internally by the polarization
    bound `metricDerivNorm_le_metricDerivNormSupOn`).
  - the fixed-vector metric-derivative identity
    (`metricDiffCovDerivAt_zero_apply`) and the closed-manifold "all metrics
    equivalent" head term (A) `metricUniformEquivalentOn_of_compact`, resting
    on the lifted foundational facts `metric_lower_bound_of_compact`
    (`Geometry/Metric/CompactMetricLowerBound.lean`) and
    `posDef_bilin_quadratic_lower_bound`
    (`Geometry/Metric/TensorInner/PosDefBilinQuadraticLowerBound.lean`).  These
    generic compactness facts were deliberately lifted *out* of the Ricci-flow
    `Evolution` layer into the `Geometry/Metric` and `Tensor` layers so the HCG
    compactness argument does not depend on `Evolution` for non-curvature
    content.
  - log-integrability of the scalar `t ↦ log (g(t)(V,V))` derivative
    (`log_integrable_of_sol`, via the family joint-bundle time-continuity of
    the Ricci and metric tensors).
  - The whole chain is wrapped, with no leftover analytic hypothesis, by
    `metricUniformEquivalentOnWindow_of_solutions'`: a Ricci-flow solution
    sequence with a uniform Riemann bound and time-`0` Cheeger–Gromov
    convergence yields whole-window metric equivalence.

## Frontier

The mixed time-spatial API is now stated, and the q=1 mixed bound is checked.
The next real frontiers are proving the Christoffel/connection-difference
induction from the MSM135 proof, threading smoothness inputs for the higher
time derivatives, and assembling window bounds for
`|partial_t^q nabla^p g(t)|` when `q >= 2`.

Equation (3.3) is no longer a frontier: the producer
`metricUniformEquivalentOnWindow_of_solutions'` derives whole-window metric
equivalence from a Ricci-flow solution sequence (uniform Riemann bound +
time-`0` Cheeger–Gromov convergence) with all analytic inputs discharged (see
the closure bullet in Definitions).  The next equation-level frontier is
(3.4), the order-`p` covariant-derivative bounds, whose remaining producer gap
is described below.

For equation (3.4), the screenshots give the right textbook induction.  The
component algebra for the first Christoffel step is already available:
`gammaEvol_l2_le` gives the local-frame estimate behind
`|partial_t Gamma| <= 3 |nabla Ric|`, while `metricGammaEquiv` now gives the
invariant HCG norm version of the equivalence between `nabla^g g_k(t)` and
`Gamma_k(t) - Gamma`.

The invariant correction formula
`nabla0SFun_sub_cov` is now checked in
`Tensor/RSTensor/NablaOnTensors/HigherOrder.lean`.  It proves that the
difference of two covariant derivatives on a covariant tensor is exactly the
lower-slot action of `CovariantDerivative.difference`.

The `(0,2)` specialization `nabla0SFun_sub_cov_two` is now also checked.  This
is the reusable tensor identity behind the first `Rc_k` estimate in the book's
proof of equation (3.4).

The first Lean blocker is no longer the invariant mixed-tensor layer or the
pointwise `(0,3)` norm-comparison layer: `connectionDifferenceTensorAt`,
`metricGammaEquiv`, `exists_diagInv_of_metricUniformEquivalentOn`, and
`covOne_le_connDiff` provide the needed canonical bridges for equations
(3.8)--(3.11).  To continue honestly toward the full (3.4), RicciFlower still
needs:

- a theorem-facing Christoffel time-derivative input or producer that feeds
  `gammaEvol_l2_le` into `norm_le_initial_add_deriv_bound`;
- the mixed `(p,q)` tensor norm comparison from MSM135 Lemma 3.13 for the
  later curvature and connection-difference induction; the `(0,3)` case needed
  for the first metric derivative is now checked;
- high-order product/commutation estimates expressing
  `nabla^N Rc_k` through `nabla^N g_k`, lower metric derivatives, and
  `nabla_k^j Rm_k` bounds.

The scalar and component-`l^2` endpoint integration for the Christoffel step is
no longer a blocker: it is covered by `norm_le_initial_add_deriv_bound`,
`componentL2_le_initial_add`, `gammaL2_le_initial_add`, their within-carrier
variants, and `gammaL2_le_of_christoffel`.  The remaining first-order assembly
issue is moving from the pointwise local-frame Christoffel estimate to the
window-level `MetricCovDerivBoundOn` predicate while threading the appropriate
orthonormal-frame and inverse-metric hypotheses.

The pointwise diagonalization/eigenvalue bridge needed for equation (3.11) is
now checked.  The remaining first-order assembly issue is not diagonalization;
it is producing the Christoffel time-derivative bound from the Ricci-flow
solution in a form compatible with the invariant connection-difference norm,
then packaging the resulting pointwise estimate into the current
`MetricCovDerivBoundOn` supremum predicate.

The pointwise-to-supremum packaging is now checked, and the two-metric
comparison lemmas are available.  The remaining first-order assembly frontier is
to combine `gammaL2_le_of_christoffel`, `diff_le_covOne`, and
`covOne_le_diff` into a single local-frame pointwise bound for
`metricCovDerivNorm ... 1`, then feed it through
`metricCovWindow_of_pointwise`.  This still needs the frame-level hypotheses
for a `g_k(t)`-orthonormal frame and the Ricci derivative component bound to be
threaded coherently.

The local-frame pointwise assembly is now checked as `covOne_le_christoffel`,
with the constant-shaped version `covOne_le_init`.  The remaining first-order
frontier is the global/window packaging: one must supply or construct the
local orthonormal frames and inverse-metric component hypotheses uniformly
over `x in K` and `t in [β, ψ]`, then feed the pointwise bound through
`metricCovWindow_of_pointwise`.

For the order-`p` analytic assembly, the remaining producer frontier is the
bridge from tensor-valued evolution `MetricCovOrderEvolutionOn` to the squared
`gRef`-metric norm evolution `MetricCovOrderNormSqEvolutionOn`.  This bridge
is intentionally explicit because `Tensor0SSpace` has its own analytic norm,
while the HCG estimates use the metric norm induced by `gRef`.  The later
Ricci-flow producer must also prove the schematic estimate
`|nabla^p Rc| <= C''_p |nabla^p g| + C'''_p`.

The local-frame comparison itself has now been de-globalized at the pointwise
basis level.  The checked basis-level lemmas `covOne_le_diff_basis_ref_lc` and
`diff_le_covOne_basis_ref_lc` replace `covOne_le_diff` and `diff_le_covOne`
using only a pointwise basis with identity inverse-metric matrix.  The component
identity is no longer a frontier: `covOneCompDiff` supplies the
metric-compatibility identity, `connDiffBasisSymm` supplies the torsion-free
symmetry of the connection difference, and `connDiffCompEq` combines them into
the MSM135 equation (3.7) form used for (3.8).

2026-05-29 follow-up: `coord_eq_inner_id` is now checked.  It records the
pointwise algebra that, in a basis whose inverse-metric matrix is the identity,
the coordinate `basis.coord a V` is the metric pairing `h.inner x (basis a) V`.
This is one ingredient for the arbitrary-basis component identity.  The direct
attempt to prove that full identity in `AllTimesBounds.lean` was not kept:
after three focused proof attempts it was still stuck at a `component0S` /
`Fin.cons` shape mismatch when comparing the `Fin 3` slots produced by
`component0S_apply` with the `Fin.cons` slots expected by
`metricCovDeriv_one_apply_section`.  The suspected smallest next lemma is a
general slot-conversion helper for `component0S` of a `(0,3)` tensor, or a
component version of `metricCovDeriv_one_apply_section` stated directly for an
arbitrary pointwise basis and smooth section extensions.

2026-05-29 progress toward (3.4): `PointedConvergence.lean` now provides a
checked local-frame component formula for `metricCovDeriv h gRef 1`, and
`AllTimesBounds.lean` now has the arbitrary-basis version needed to avoid
global-frame assumptions in the first-order comparison.  The first-order
pointwise estimate `covOne_le_christoffel` now uses the basis-level
Levi-Civita comparison route and no longer needs separate metric-orthonormality
fields beyond the inverse-metric identity already used by the component norms.
The next frontier for the full (3.4) proof is the higher-order induction:
formalizing the product/commutator estimates that expand repeated applications
of `nabla - nabla_k` and control the resulting products by lower metric
derivatives and the `nabla_k^j Rm_k` bounds.

## Verification

Focused verification passed for `AllTimesBounds.lean` after adding the
regular-time Christoffel integration bridge, the pointwise-to-window metric
derivative packaging lemmas, the two-metric first-order comparison lemmas, the
exact-order window packaging layer, and the basis-level replacement bridges.
Focused verification also passed after adding the local-frame first-order
assembly and the initial-constant version.  Focused verification passed again
after adding `coord_eq_inner_id`, `covOneCompDiff`, `connDiffBasisSymm`,
`connDiffCompSymm`, `connDiffCompEq`, and the basis-level Levi-Civita versions
of the first-order norm comparisons.  The remaining blockers are the
global/window first-order packaging and, more substantially, the
higher-order/mixed-time induction, not the component integration, coordinate
RHS reduction, invariant norm comparison, component identity, or local-frame
pointwise estimate for equations (3.7)--(3.11).

2026-05-30 Phase 0 update: focused verification passed after adding the
first-order input and conclusion packages and `metricAllTimes_firstOrder`.
The single-frame global/window packaging target is now checked.  The remaining
blockers are producer-side: constructing the supplied local-frame and
inverse-metric component data, deriving the log-derivative input from
Ricci-flow curvature control, deriving the uniform `nabla Ric` bound, and then
formalizing the higher-order and mixed-time induction.

2026-05-30 Phase 2A update: focused and targeted verification passed after
adding the mixed tensor-valued derivative API, q=0 norm reduction, mixed
window-bound predicates, pointwise packaging lemmas, and the full
`MetricAllTimesConclusion` package.  The remaining higher-time work is
producer-side and proof-side, not a missing statement API.

2026-05-30 higher-order analytic update: focused verification and targeted
module verification passed after adding `metricCovOrderWindow_of_evolution`.
The build still reports pre-existing warnings in this file and upstream files,
but no new proof frontier was left in the checked theorem.  The remaining
frontier is producer-side: deriving the squared metric-norm evolution bridge
and the schematic `nabla^p Rc` estimate from Ricci-flow identities and
curvature bounds.

2026-05-30 Phase 2B update: focused verification and targeted module
verification passed after adding the q=1 mixed bound
`metricMixedOneWindow_of_evolution` with constant
`metricMixedOneConstant Cpp Csp0 Cppp = 2 * (Cpp * Csp0 + Cppp)`.  The only
extra explicit input is `MetricMixedDerivOneEvolutionOn`, which now records the
resulting q=1 `metricMixedDeriv` equality directly; the derivative-realization
producer from the Ricci-flow equation remains a later backend theorem.  The
existing order-`p` schematic Ricci bound and spatial window bound then prove
the estimate.  The reusable lower lemma is
`metricMixedOneWindow_of_ric_bound`; the public evolution-wrapper is
`metricMixedOneWindow_of_evolution`.

2026-05-30 Phase 2C/2D statement-layer update: focused verification and
targeted module verification passed after adding the general q >= 1
honest-input theorem `metricMixedQWindow_of_evolution`.  The theorem is a
pure assembly step from `MetricMixedDerivLayerEvolutionOn` plus the supplied
layer norm bound to `MetricMixedDerivBoundOnWindow`, with constant
`metricMixedQConstant Cpq = 2 * Cpq`.  The remaining frontier is producer-side:
constructing the layer tensor and proving its schematic bound from Shi
estimates and the MSM135 product expansion.

2026-05-30 Phase 2C resume note: focused verification no longer reaches the
2C declarations in the current dirty worktree.  It stops earlier at the
first-order bridge `metricCovDeriv_one_component_eq_metricCovAtBase`, where
`SmoothRiemannianMetric` has changed from the old `⊤` alias to the `∞`
smooth metric alias.  Rebuilding the direct Levi-Civita variation upstream
module succeeded, so the remaining blocker is the current dirty metric API
transition, not the 2C layer-bound theorem.

2026-05-30 Phase 1D update: focused verification and targeted module
verification passed after adding the exact-order-to-cumulative spatial
assembly (`metricCovBoundsWindow_of_orderBounds`) and the conservative direct
spatial assembler `metricAllTimes_spatial`.  This closes the requested
statement-level packaging for `MetricAllTimesSpatialConclusion`; the remaining
frontier is still producer-side exact-order estimates, not the packaging.

2026-05-30 Phase 2C resume resolved: the stale-import path was cleared by
refreshing `PointedConvergence` after repairing an upstream local smoothness
side condition in `LeviCivita.Curvature.LeviCivita`.  Focused verification and
targeted module verification now pass for `AllTimesBounds.lean`.  The 2C API
remains the honest-input layer theorem `metricMixedQWindow_of_evolution`; the
remaining mathematical frontier is still producer-side construction of the
layer tensor and its schematic bound, not this assembly theorem.

2026-05-30 Phase 2D update: added the final bound-side mixed assembly:
`metricMixedZeroWindow_of_spatial`, `metricMixedCumulativeConstant`,
`metricMixedBoundsWindow_of_layerBounds`, `MetricAllTimesInput`, and
`metricAllTimes`.  This packages exact `(a,b)` mixed window bounds into the
cumulative `MetricAllTimesConclusion`.  The q=0 layer can be supplied from
spatial order bounds via `metricMixedDerivNorm_zero`; q>=1 layers still come
from the honest producer inputs used by `metricMixedQWindow_of_evolution`.

2026-06-01 DC3b bridge update: added `metricCov1_coord`, identifying
local-frame components of the HCG first metric derivative tensor
`metricCovDeriv 1 g h` with
`Coordinates.metricCovDerivForMetricCompInFrame` for the Levi-Civita
connection of `h`.  This lets the DC1 Christoffel-difference component formula
feed the HCG schematic product layer without duplicating the metric derivative
API.  Focused verification and targeted module verification passed.  The
remaining DC3b frontier is still the finite Christoffel expansion/product
control, not this coordinate bridge.

2026-06-03 F3 k=1 metric-derivative bridge update: added
`metricCovDeriv_two_eval_smooth_slots` and `metricCov2_coord`.  These identify
local-frame components of `metricCovDeriv 2 g h` with the coordinate
second-covariant derivative of metric components used in the differentiated
Christoffel formula.  Verification passed for this file, and the targeted
module build passed earlier in the run.  The remaining F3 frontier is no longer
the `nabla_h^2 g` coordinate bridge; it is the HCG norm packaging and the
pointwise local orthonormal-frame/inverse-data producer needed to make that
packaging global.

2026-06-03 F3 k=2 metric-derivative bridge update: added
`metricCovDeriv_three_eval_smooth_slots` and `metricCov3_coord`. These
identify local-frame components of `metricCovDeriv 3 g h` with the coordinate
third covariant derivative of metric components used by the next
Christoffel-difference calculation. Verification passed, and targeted module
verification completed. The remaining `k = 2` frontier is not this component
bridge; it is the finite product-rule/norm estimate for the second derivative
of the Christoffel-difference formula.

2026-06-07 equation (3.3) closure: focused verification passed for
`AllTimesBoundsFlow.lean` and the new foundational producer files
(`Geometry/Curvature/QuadraticFormBound.lean`,
`Geometry/Curvature/RicciOperatorNormBound.lean`,
`Geometry/Curvature/RicciOperatorNormBoundFlow.lean`,
`Geometry/Metric/CompactMetricLowerBound.lean`,
`Geometry/Metric/TensorInner/PosDefBilinQuadraticLowerBound.lean`).  This
discharges every analytic input of MSM135 equation (3.3) from a Ricci-flow
solution sequence and packages them into the hypothesis-free producer
`metricUniformEquivalentOnWindow_of_solutions'`.  The generic compactness
facts behind the closed-manifold head term (A) were lifted out of the
Ricci-flow `Evolution` layer into the `Geometry/Metric` and `Tensor` layers,
per the architectural rule that HCG compactness must not depend on `Evolution`
for non-curvature content.  The next frontier is the equation-(3.4) producer
chain (the order-`p` `MetricCovOrderEvolutionInput` from Shi estimates).

2026-06-07 equation (3.4) linearity backbone: focused verification and targeted
module verification passed for two new files,
`Tensor/RSTensor/NablaOnTensors/TotalNabla0SLinear.lean` and
`HCGCompactness/MetricCovDerivLinear.lean`.  The first adds the generic tensor
fact `totalNabla0SFun_smul` (scalar-homogeneity of the total covariant
derivative), kept in the `Tensor` layer per the lift-out-of-`Evolution` rule.
The second adds `covDerivOfField` — the same fixed-`gRef` iterated background
covariant derivative as `metricCovDeriv`, but applied to an arbitrary covariant
`(0,2)`-tensor field — together with the bridge
`metricCovDeriv_eq_covDerivOfField` and the scalar-homogeneity
`covDerivOfField_smul`.  This is the algebraic backbone of the equation-(3.4)
evolution `∂_t (∇^p g) = -2 ∇^p Rc`: `covDerivOfField gRef p` realizes the
`nablaRic` family from the Ricci `(0,2)`-tensor field, and `covDerivOfField_smul`
factors the constant `-2` through every covariant-derivative step.  The three
remaining producer pieces for `MetricCovOrderEvolutionInput.hevol`/`ric_bound`
are: (a) the single-step *parametric* identity that `∂_t` commutes with the
fixed background covariant derivative (`∂_t totalNabla0SFun = totalNabla0SFun
∂_t`), the analytic heart of `hevol`; (b) packaging the raw Ricci `(0,2)` field
`ricciTwoTensorField` as a smooth `Tensor0SField`; and (c) the schematic Shi
estimate `|∇^p Rc| ≤ C''_p |∇^p g| + C'''_p`, obtained by converting the
`g`-covariant Bernstein–Bando–Shi tower bound `bernsteinShi_solution_estimate`
to the `gRef` connection via the connection-difference expansion.

2026-06-07 equation (3.4) parametric Clairaut: focused verification and targeted
module verification passed for the new file
`Tensor/RSTensor/NablaOnTensors/TotalNabla0STimeDeriv.lean`, which adds
`nabla0SFun_hasDerivWithinAt` and `totalNabla0SFun_hasDerivWithinAt` — the
single-step identity that the time derivative commutes with the fixed background
covariant derivative (piece (a) above).  The proof reuses the already-checked
`extDerivFun` time-swap infrastructure (`FixedBaseExtDerivTimeDerivativeOn` and
its model-space core `fixedBaseFDerivTimeDerivativeAt_of_contDiff` from
`Bundle/PartialMfderiv`): the directional expansion
`nabla0SFun_eval_smooth_slots` splits `∇_X α` into the scalar exterior-derivative
term (whose time derivative is the supplied swap hypothesis) and finitely many
correction terms evaluated at the fixed base point with parameter-independent
slots (whose time derivatives are pointwise).  The lemma takes the swap and the
pointwise time derivatives as hypotheses, isolating the next `hevol` frontier:
discharging `FixedBaseExtDerivTimeDerivativeOn` for the `k`-fold covariant
derivative `∇^k g` from the solution's joint spacetime smoothness
(`IsSolutionOn.smoothMetric`), then the `hevol` induction over `p` (base case
`ricciFlow_metric_hasDerivAt`, step via this Clairaut plus `covDerivOfField_smul`
to carry the constant `-2`).
