# B2 / P2 plan: Perelman's L-geometry

Written 2026-08-15.  This is the execution plan for the `P2` phase of
`../POINCARE_PLAN.md`, called **B2** in the current work allocation.  Its
mathematical references are Morgan--Tian `newcompar.tex`, `newcomp2.tex`, and
`noncoll.tex`.  Those files are references only; all implementation belongs
under `DifferentialGeometry/` and uses RicciFlower conventions.

Live status is recorded by the latest entry in the status log.  Older dated
entries and the creation-time percentages below are historical snapshots, not
current truth.  As of 2026-08-27, `redVolume_anti`, `redVolume_zero_lim`,
`redVolume_lsc`, `redVolume_unif_low`, `exists_redWeak_sup`,
`exists_redLen_le`, `redVolume_late_low`, `redVolume_ball_eta`, and its
`redVolume_ball_le` specialization are checked; `smooth_nlc` remains unproved.

## 0. Scope and final deliverables

The first implementation target is Perelman's L-geometry for an **ordinary
smooth Ricci flow on one fixed manifold**.  Surgery-space-time paths are a
later consumer-facing extension.  In particular, the first stages must not:

* introduce a global RFWS or an exotic space-time manifold;
* represent topology change by a single family `Real -> Metric M`;
* make generalized-flow data a field of the basic L-length definition;
* replace existence, cut-locus, or monotonicity arguments by supplied
  hypotheses with endpoint-looking names.

For a solution `S : SolutionOn D`, terminal forward time `T`, and a curve
`gamma : Real -> M` parameterized by backward time `tau`, use

```text
g_tau       = S.metric (T - tau)
X(tau)      = d gamma / d tau
L(gamma)    = integral sqrt(tau) * (R(T-tau,gamma(tau)) + |X(tau)|^2_g_tau)
l(q,tau)    = inf_gamma L(gamma) / (2 * sqrt(tau))
Vtilde(tau) = integral (4*pi*tau)^(-n/2) * exp(-l(q,tau)) dmu_g_tau(q)
```

The normalization of reduced volume is the standard `(4*pi*tau)^(-n/2)`
normalization.  Morgan--Tian sometimes suppresses the constant; theorem
statements must record which normalization they use.

The ordinary-flow capstones are:

1. `redVolume_anti`: reduced volume is antitone in backward time;
2. `smooth_nlc`: the resulting kappa-noncollapsing theorem for smooth flows;
3. scaling and pullback naturality sufficient to feed the existing
   `Perelman.NoLocalCollapsing` interface.

The later surgery capstone is an eventwise version of `smooth_nlc` whose
L-curves may cross metric seams and whose loss is controlled exactly as in
Morgan--Tian `noncoll.tex`.  It is not part of the initial fixed-manifold API.

Honest status at creation:

* `redVolume_anti`: unstated and unproved, **0%**;
* `smooth_nlc`: unstated and unproved, **0%**;
* dedicated L-geometry machinery: **0%**;
* reusable generic prerequisites already in the tree: roughly **35--45%**
  (curve derivatives, variational calculus, curvature, volume, exponential
  maps, and parabolic scaling).  This prerequisite number is not theorem
  completion.

## 1. Existing native assets

Reuse these APIs rather than building parallel versions.

| Need | Existing native layer |
|---|---|
| metric family and scalar curvature | `RicciFlow/Basic/Core.lean`: `SolutionOn`, `IsSolutionOn`, `SolutionOn.scalar` |
| time translation | `SolutionOn.timeShift` and its metric/scalar lemmas |
| parabolic scaling | `RicciFlow/ParabolicRescaling.lean` |
| velocity of a manifold curve | `mfderiv (I := source model) I gamma tau 1` and `MFDerivAlongCurve` |
| intrinsic derivative along a curve | `Connection/ParallelTransport/CovariantDerivativeAlong.lean`: `covDerivAlong` |
| smooth two-parameter variations | `Comparison/Variation/*`, especially `IsSmoothVariation` |
| first and second variation patterns | `Variation/FirstVariation.lean`, `SecondVariation.lean`, `RegularParameterFirstVariation.lean` |
| curvature commutation | `Variation/CovariantCommutationCurvature.lean` |
| Jacobi and exponential-map machinery | `Geometry/Exponential/*` |
| gradient, Hessian, Laplacian | `Geometry/Operator/Operators.lean`, `HessianTraceRealization.lean` |
| Riemannian volume | `Analysis/Integration/Measure/RiemannianMeasure.lean` and `Integration/Volume/*` |
| normal-coordinate Jacobians | `Comparison/Volume/NormalChartMeasure.lean`, `JacobianBounds.lean` |
| target NLC vocabulary | `Perelman/Noncollapsing.lean` |

The key missing reusable bridge is a clean calculus API for a curve evaluated
against the **moving metric** `S.metric (T - tau)`.  Build that bridge at the
lowest natural layer; do not copy the fixed-metric variation proofs into every
L-geometry theorem.

## 2. Module layout

Create the directory

```text
DifferentialGeometry/Geometry/Flow/RicciFlow/Perelman/LGeometry/
```

and use the following modules.  Keep the umbrella
`Perelman/LGeometry.lean` import-only once there is more than one module.

| Module | Responsibility |
|---|---|
| `Defs.lean` | velocity, speed squared, L-density, L-length |
| `Reparam.lean` | `s = sqrt(tau)` regularization and change of variables |
| `MovingMetric.lean` | time derivative of inner products and along-curve identities |
| `FirstVariation.lean` | first variation and Euler--Lagrange equation |
| `Geodesic.lean` | `IsLGeodesic`, regularized ODE, existence and uniqueness |
| `Exp.lean` | L-exponential map and its local smoothness |
| `Scaling.lean` | parabolic-scaling naturality of regularized curves and L-exp |
| `Naturality.lean` | fixed-diffeomorphism pullback naturality |
| `Jacobi.lean` | L-Jacobi equation and differential of L-exp |
| `SecondVariation.lean` | L-index form and second variation |
| `Minimizer.lean` | minimizing L-geodesics and L-cost |
| `CutDomain.lean` | minimizing domain, conjugate/cut alternatives, measurability |
| `ReducedLength.lean` | reduced length, gradient/time identities, weak inequalities |
| `Lipschitz.lean` | local Lipschitz and a.e. differentiability |
| `ReducedVolume.lean` | reduced-volume measure, change of variables, and global monotonicity |
| `Monotonicity.lean` | Jacobian density and strict-ray pointwise monotonicity |
| `CompleteFlow.lean` | complete bounded-curvature extension (`newcomp2.tex`) |
| `SmoothNLC.lean` | smooth-flow kappa-noncollapsing producer |

Tentative public names respect the 20-character limit:

```text
lVelocity       lSpeedSq       lDensity       lLength
IsLGeodesic     lExp           IsLJacobi      lCost
redLength       redDensity     redVolume      redVolume_anti
smooth_nlc
```

Names are tentative until their live signatures are tested.  Do not create a
data structure merely to make these names possible; raw curves plus separate
regularity hypotheses are preferred initially.

## 3. Mathematical dependency ladder

### L0. Definitions and time orientation

Implement the four scalar definitions in `Defs.lean` for raw curves
`gamma : Real -> M`.  Definitions are total because `SolutionOn`'s metric
family is total on `Real`; theorems that use the Ricci-flow equation must carry
the honest hypothesis that `T - tau` lies in `D.carrier`.

First checked facts should include:

* `lSpeedSq` is nonnegative;
* `lLength ... a a = 0`;
* additivity across adjacent intervals, with exactly the integrability
  hypotheses required by `intervalIntegral`;
* integrability/continuity of the density for a smooth curve on a compact
  positive backward-time interval;
* invariance under eventual equality of curves on the integration interval.

Do not claim L-density is nonnegative without a scalar-curvature hypothesis:
scalar curvature may be negative.

### L1. Square-root reparameterization

For `alpha(s) = gamma(s^2)`, prove the velocity relation

```text
A(s) = 2*s * X(s^2)
```

in tangent-space form, then prove

```text
L(gamma; tau1,tau2)
  = integral_[sqrt(tau1),sqrt(tau2)]
      (1/2 * |A(s)|^2 + 2*s^2*R(T-s^2,alpha(s))) ds.
```

This is the regular normal form at `tau = 0`; all ODE existence at the base
time should use `s`, not the singular `1/(2*tau)` equation directly.

Stop and add a general interval-integral substitution lemma only if Mathlib's
existing change-of-variables theorem cannot express the square map.  Such a
lemma belongs in `Analysis/Integration`, not in a Ricci-flow consumer.

### L2. Moving-metric calculus and first variation

For `g_tau = g(T-tau)`, first prove the reusable scalar identity

```text
d/dtau <Y,Z>_g_tau
  = <D_tau Y,Z> + <Y,D_tau Z> + 2*Ric(Y,Z).
```

Then adapt the existing fixed-metric variation engine to show the first
variation formula, including the endpoint term
`2*sqrt(tau)*<Y,X>`.  Deduce the Euler--Lagrange equation

```text
D_tau X - 1/2 grad R + (1/(2*tau))*X + 2*Ric(X,.)^sharp = 0.
```

Define `IsLGeodesic` by this intrinsic equation on positive backward times.
Do not define it as “is a critical point” until a sufficiently general
fundamental lemma of calculus of variations is available; instead prove the
critical-point equivalence afterward.

### L3. Regularized ODE and L-exponential

Rewrite the equation in `s = sqrt(tau)`.  Use chart ODE existence to prove a
unique L-geodesic with

```text
gamma(0) = x,
limit sqrt(tau)*X(tau) = Z.
```

Define `lExp S T x Z tau` by evaluating that solution.  Prove:

* initial value and initial tangent normalization;
* smooth dependence on `(Z,tau)` for `tau > 0` and the regularized extension
  at `tau = 0`;
* pullback and parabolic-scaling naturality.

Do not use the ordinary exponential map as the definition of `lExp`; it is
only the small-time comparison model.

### L4. L-Jacobi and second variation

Differentiate the L-geodesic equation using the existing curvature
commutation theorem.  Define `IsLJacobi` and identify solutions with the
differential of `lExp`.  Prove the regularized initial-value theorem at
`tau = 0`.

Then define the L-index form and prove the second-variation formula.  Reuse the
existing `Variation.SecondVariation` proof architecture, but keep the moving
metric and `nabla Ric`, `Hess R` correction terms explicit.  The main output is
positivity of the L-index form along a minimizing segment before the first
L-conjugate point.

### L5. Minimizers, L-cost, and the cut domain

Define `lCost` as the infimum of `lLength` over admissible curves with fixed
endpoints.  Prove existence of a minimizer first on compact manifolds.  The
complete bounded-curvature case is postponed to L8.

Build the analogue of the ordinary injectivity domain:

* unique minimizing L-geodesic before cut time;
* L-exp is a local diffeomorphism away from L-conjugate points;
* the minimizing tangent domain is open and star-shaped in backward time;
* its complement/cut image is measurable and has zero Riemannian measure in
  the form needed for change of variables.

This is the first major global-geometric frontier.  Do not assume a measurable
cut decomposition in `ReducedVolume.lean`; prove it here or leave the precise
frontier visible.

### L6. Reduced length and differential inequalities

Define

```text
redLength(q,tau) = lCost(x,q,tau) / (2*sqrt(tau)).
```

On the smooth minimizing domain prove the gradient and time-derivative
identities and the trace/Hessian inequalities from Morgan--Tian
`newcompar.tex` Sections “Second-order differential inequalities” and
“Reduced length”.  Then prove local Lipschitz estimates and extend the key
inequalities weakly or almost everywhere across the cut locus.

Do not encode the inequalities only on supplied smooth subsets; the later
measure theorem needs a statement covering almost every point of a time
slice.

### L7. Reduced volume and monotonicity

Define `redDensity` and `redVolume` using
`riemannianVolumeMeasure (S.metric (T-tau))`.  Prove the tangent-space
change-of-variables formula through `lExp` and its Jacobian.

For fixed initial tangent `Z`, prove antitonicity of

```text
tau^(-n/2) * exp(-redLength(lExp Z tau,tau)) * Jac(lExp_tau)(Z).
```

and its Euclidean small-time limit.  Integrate on the nested minimizing
domains to obtain `redVolume_anti`.  This is the ordinary-flow capstone of the
core L-geometry lane.

The Jacobian proof must use the L-Jacobi fields and second-variation trace
bound.  A theorem taking pointwise Jacobian monotonicity as an assumption is
not completion of this stage.

### L8. Complete bounded-curvature flows

Follow Morgan--Tian `newcomp2.tex`:

* existence of minimizing L-geodesics by coercivity and Hopf--Rinow;
* local Lipschitz estimates under bounded curvature;
* `min redLength <= n/2`;
* distributional reduced-length inequalities using compact cutoffs;
* reduced volume bounded by the Euclidean value, with rigidity.

Reuse the project's completeness, properness, Shi bounds, and cutoff/barrier
machinery.  Do not strengthen consumers to compactness when the book only
requires completeness plus bounded curvature.

### L9. Noncollapsing and surgery extension

First prove `smooth_nlc` for ordinary compact smooth Ricci flows and adapt it
to the existing `Perelman.NoLocalCollapsing` predicate.  Compare this output
with the entropy/W route; keep one canonical public predicate and two producer
theorems, not two noncollapsing hierarchies.

Only after the ordinary proof is complete, extend L-length across the event
presentation from `Perelman/Surgery/`.  A crossing path is piecewise a smooth
fixed-manifold path, with adjacent pieces matched by the surgery seam.  Prove
additivity of L-length and metric invariance on the kept region before
attempting Morgan--Tian `noncoll.tex`'s good/bad path decomposition.

The generalized-flow noncollapsing theorem is a P7 producer and must remain
separate from `smooth_nlc`.

## 4. Historical first execution brick (completed)

This section records the 2026-08-15 kickoff and must not be used as the current
next-step list.  It began in `E:/testdifferential-geometry`; future sessions
must inspect the live branch instead of hard-coding `short-time-existence`.
The original kickoff was:

1. reread `AGENTS.md`, `important_lesson.md`, `lessons.md`, `convention.md`,
   `dictionary.md`, this plan, and the live signatures named in Section 1;
2. confirm the working tree and file claims; do not touch stale claims or
   unrelated files;
3. create `Perelman/LGeometry/Defs.lean` and `Defs.md`;
4. implement `lVelocity`, `lSpeedSq`, `lDensity`, and `lLength` for an ordinary
   `SolutionOn` and raw curve;
5. prove the smallest stable L0 facts listed above, including at least one
   non-definitional integrability or congruence result;
6. focused-check the file through `scripts/lake-locked.ps1`; review the diff;
7. update this plan's status and next exact theorem, then continue into
   `Reparam.lean` if L0 is green.

The first session must not add `sorry`, an endpoint wrapper, a new foundational
class, or an RFWS object.  If a moving-fibre elaboration problem appears,
scalarize after applying the metric to the velocity; do not prove equality of
whole tangent-bundle or Hom objects.

## 5. Verification and stop conditions

For every Lean file, claim it before editing, use focused checks first, and
write the same-name Markdown note.  Refresh an `.olean` only when a downstream
module needs a newly exported declaration.  Never run raw `lake build`.

Stop and report rather than disguising the gap if any of the following occurs:

1. the basic definition appears to require an RFWS or a dependent space-time
   tangent bundle;
2. the square-root reparameterization needs a genuinely absent manifold chain
   rule or interval substitution theorem;
3. first variation requires a new consumer assumption instead of a reusable
   moving-metric identity;
4. L-geodesic existence cannot be expressed with the current chart ODE API;
5. cut-domain measurability would have to be assumed;
6. monotonicity is reduced to a new black-box Jacobian inequality;
7. surgery topology is being mixed into the ordinary-flow core.

At every handoff record separately:

* the live percentage of each named capstone theorem, determined from its
  actual declaration and verification rather than an older status entry;
* dedicated L-geometry machinery percentage;
* generic reused infrastructure;
* exact smallest failed theorem/API and whether it is routine, missing API, or
  a genuine mathematical frontier.

## Status log

- 2026-08-15: plan created after a live source audit.  No native L-length,
  reduced-length, or reduced-volume declaration existed.  The fixed-manifold
  first route was selected; `Defs.lean` is the first execution target.
- 2026-08-15 (L0--L1 execution): `LGeometry/Defs.lean` and
  `LGeometry/Reparam.lean` are focused-green, warning-free, and contain no
  `sorry` or `admit`.  L0 now has the four total fixed-manifold definitions,
  speed-square nonnegativity, zero/additive interval laws, germ-level
  congruence, and moving-metric/scalar continuity plus integrability.  L1 now
  has `A(s) = 2s X(s^2)`, the regularized density, and the oriented
  square-root interval formula.  Mathlib's existing monotone substitution
  theorem was sufficient, so no generic integration wrapper was added.

  The next exact theorem is `lInner_deriv` in `MovingMetric.lean`.  At a
  backward time `tau0` with `T - tau0` regular, and for differentiable sections
  `V,W` along `gamma`, it should state the `HasDerivAt` identity

  ```text
  d/dtau <V,W>_{g(T-tau)} |_{tau0}
    = <D_tau V,W> + <V,D_tau W> + 2 Ric(V,W)
  ```

  using `covDerivAlong` for the two fixed-time connection terms and
  `IsSolutionOn.equation` for the backward-time metric term.  Prove the
  chart-regularity form matching the existing metric-compatibility theorem
  first, then add a smooth-curve wrapper.

  Honest progress: `redVolume_anti` **0%**; dedicated L-geometry machinery
  about **2--3%**; reusable generic prerequisites about **35--45%**; P2 as a
  whole remains below **1%**.  The whole Poincare program estimate remains
  **3--5%** because this first local brick does not materially move the
  multi-year denominator.

- 2026-08-15 (L2 moving-metric brick): `LGeometry/MovingMetric.lean` is
  focused-green, warning-free, and contains no `sorry` or `admit`.
  `lInner_deriv_chart` proves the weakest pinned-chart form of

  ```text
  d/dtau <V,W>_{g(T-tau)}
    = <D_tau V,W> + <V,D_tau W> + 2 Ric(V,W),
  ```

  and `lInner_deriv` supplies a pointwise-smooth wrapper.  The proof uses a
  jointly differentiable scalar chart-Gram pairing and its two coordinate
  slices; it does not infer the full derivative by merely adding two frozen
  formulas, and it introduces no new family class or moving-bundle equality.

  The next exact theorem is `lDensity_deriv` in
  `LGeometry/FirstVariation.lean`, the pointwise variation derivative of the
  L-density.  Reuse the native speed-square variation and mixed-covariant
  commutation plus fixed-time scalar-gradient duality.  Do not add an
  integrated variation theorem with a new domination hypothesis; first
  produce any missing joint compact-slab regularity at the reusable layer.

  Honest progress: `redVolume_anti` **0%**; dedicated L-geometry machinery
  about **4--5%**; reusable generic prerequisites about **35--45%**; P2 as a
  whole remains below **1%**.  The whole Poincare program estimate remains
  **3--5%**.

- 2026-08-15 (L2 first variation and equation):
  `LGeometry/FirstVariation.lean` and `LGeometry/Geodesic.lean` are
  focused-green, warning-free, and contain no `sorry` or `admit`.
  `lLength_first_var` proves the complete oriented Morgan--Tian first-variation
  identity, with compact domination and all interval integrability produced
  internally.  `lEulerPair` and `lLength_euler` give the fully applied scalar
  Euler-residual form.  `HasLEquationAt` prevents fake solutions at
  nondifferentiable points, `IsLGeodesic` is set-indexed for local positive
  regular-time segments, and `lFirst_var_zero` proves equation implies
  fixed-endpoint stationarity.

  Three independent routes have now been rejected.  Separate fixed-time scalar
  smoothness plus joint value continuity did not control spatial derivatives;
  pointwise difference quotients/FTC still lacked a common compact bound; and
  the existing exponential-map variation realization requires global
  completeness, connectedness, and continuous Riemannian-bundle assumptions
  absent from this lane.  The first two were resolved by the new generic
  producers `derivFst_contMDiffAt`, `scalarJointAt`, and `metricCLMSmoothAt`.
  The third is the current honest stop condition.

  The exact next producer is `exists_chartVar` in the generic
  comparison/variation layer: realize a compactly supported smooth field along
  a curve, supported inside one coordinate chart, by a smooth variation fixed
  wherever that field vanishes.  This should enable the fundamental-lemma
  converse from fixed-endpoint criticality to the pointwise L-geodesic equation
  without strengthening consumers.

  Honest progress: `redVolume_anti` **0%**; dedicated L-geometry machinery
  about **8--10%**; reusable generic prerequisites about **40--50%**; P2 as a
  whole remains below **1%**.  The whole Poincare program estimate remains
  **3--5%**.

- 2026-08-15 (L2 criticality equivalence): the third route boundary is now
  resolved without stronger consumer assumptions.  The generic
  `Comparison/Variation/ChartVariation.lean` module proves `exists_chartVar`:
  a compactly supported smooth model field whose supported curve image lies
  in one chart is realized as the transverse field of a global smooth
  variation, fixed wherever the field vanishes.  Its assumptions do not
  include completeness, connectedness, a metric, or a continuous
  Riemannian-bundle package.

  `LGeometry/FirstVariation.lean` now exposes the continuity producers
  `lGrad_contOn`, `lCross_contOn`, and `lEuler_contOn`, together with test-vector
  linearity `lEulerPair_smul`.  `LGeometry/Geodesic.lean` defines the canonical
  fixed-endpoint predicate `IsLCritical`; `IsLGeodesic.critical` proves the
  forward implication, and `IsLCritical.isLGeo` uses `exists_chartVar`, the
  scalar fundamental lemma, and continuity to prove the pointwise Euler
  equation on `Ioo a b`.  The generic producer and first-variation module have
  green targeted refreshes, while `Geodesic.lean` is focused-green and
  warning-free.  These files contain no `sorry` or `admit`.

  L2 is therefore complete at the planned intrinsic/criticality level.  The
  exact next theorem is `lEuler_sq` in `LGeometry/Geodesic.lean`: for
  `alpha(s) = gamma(s^2)` and `A = alpha'`, prove at `s > 0` the fully applied
  identity

  ```text
  4*s^2*lEulerPair
    = <Y,D_s A> - 2*s^2*<grad R,Y> + 4*s*Ric(Y,A).
  ```

  This is the nonsingular L3 normal form.  Do not start chart ODE existence
  from the singular `tau` equation, and do not define `lExp` before this
  identity is green.

  Honest progress: `redVolume_anti` **0%**; dedicated L-geometry machinery
  about **10--12%**; reusable generic prerequisites about **45--55%**; P2 as a
  whole remains below **1%**.  The whole Poincare program estimate remains
  **3--5%**.

- 2026-08-16 (first L3 regularized ODE brick): the square-root normal form and
  its first-order phase interface are focused-green and warning-free, with no
  `sorry` or `admit`.  The generic connection layer now has
  `covDerivAlong_comp`, and `lVelocity_sq_pos` supplies the positive-time germ
  identity even when manifold derivatives use their totalized zero value.
  `lEuler_sq` proves

  ```text
  4*s^2*lEulerPair
    = <Y,D_s A> - 2*s^2*<grad R,Y> + 4*s*Ric(Y,A).
  ```

  `lRegAccel` packages the direct vector right-hand side
  `2*s^2*grad R - 4*s*Ric-sharp(A)`, and
  `HasLEquationAt.accel_sq` upgrades the all-test-vector equation to
  `D_s A = lRegAccel`.  `lPhaseField` is the corresponding fixed-chart
  first-order system.  Its zero-time value is the ordinary phase field of
  `g(T)`, and the correct seed is `A(0) = 2*Z`, not `Z`.

  The exact next theorem is `lPhaseField_smoothAt` in `Geodesic.lean`: under
  `hS : IsSolutionOn S`, `T - s^2 in D.regular`, and a chart-interior phase
  point, prove joint `C-infinity` regularity of
  `Function.uncurry (lPhaseField S T x0)` at `(s,z)`.  Existing manifold
  integral-curve existence and uniqueness are sufficient after autonomizing
  on `Real x (E x E)`; no new Picard class or stronger manifold hypothesis is
  planned.

  `lPhaseField_smoothAt` is currently unstated and therefore **0%**.  The
  smallest missing reusable API is joint smoothness of the fixed-chart
  Christoffel contraction for a smooth metric family: a close proof exists
  only as a private DeTurck helper.  The scalar-gradient and Ricci-sharp terms
  can be produced componentwise from `scalarJointAt`, inverse-Gram
  smoothness, `derivFst_contMDiffAt`, and the metric evolution equation.  This
  is an API-placement gap rather than a mathematical obstruction, and its
  reusable prerequisites are counted separately.

  Honest progress: `redVolume_anti` **0%**; dedicated L-geometry machinery
  about **12--14%**; reusable generic prerequisites about **45--55%**; P2 as a
  whole remains below **1%**.  The whole Poincare program estimate remains
  **3--5%**.

- 2026-08-21 (`arxiv-preprint` migration and L3 existence): the checked L0--L3
  implementation has been migrated to the current native layout.  In
  particular, `Solution/Basic` replaces the older `Basic/Core` route,
  `Evolution/Scalar/JointRegularity.scalar_joint` supplies joint scalar
  regularity, and `Bundle/PartialMfderiv/Basic.timeDeriv_smoothAt` supplies the
  first-time-derivative producer.  The required generic bridges now live at
  their native layers: `metricCLMSmoothAt`, `covDerivAlong_comp`,
  `exists_chartVar`, the fixed-chart metric-sharp formula, and joint scalar and
  Ricci coordinate regularity.  No reference-tree import was introduced.

  `lPhaseField_smoothAt` is now proved and focused-green.  The autonomized ODE
  layer gives `exists_lPhaseSol`, arbitrary-base-time germ uniqueness
  `lPhaseSol_unique_at`, and its zero-time wrapper.  The chart/intrinsic bridges
  then give `exists_lRegCurve`, `lRegCurve_unique_at`, and the zero-time
  specialization, with the correct seed `A(0) = 2*Z`.

  `LGeometry/Exp.lean` completes the first maximal-domain brick:
  `IsLRegCurveOn`, `LRegCurveWitness`, the open `lRegDomain`, the totalized
  `lRegCurve`, `lExpDomain`, and `lExp`, including the zero-domain and zero-value
  laws.  It follows the native `maximalGeodesic` convention and returns the
  base point outside the witnessed domain.  Focused verification is green and
  warning-free, and the migrated files contain no `sorry` or `admit`.

  The exact next theorem is `lRegWitness_eq`: two `IsLRegCurveOn` witnesses on
  open preconnected sets containing zero, with the same `(x,Z)`, agree on the
  intersection of their domains.  It must propagate `lRegCurve_unique_at`
  from the common initial data at zero, after which `lRegCurve` can be shown
  locally equal to any witness and the existing local-flow machinery can
  export smooth dependence of `lExp`.  Pointwise germ uniqueness is complete;
  connected-domain propagation is not yet claimed.

  Honest progress: `redVolume_anti` **0%**; dedicated L-geometry machinery
  about **18--20%**; reusable generic prerequisites about **60--70%**; P2 as a
  whole remains below **1%**.  The whole Poincare program estimate remains
  **3--5%**.

- 2026-08-21 (L3 witness coherence and short-time smooth dependence):
  `LGeometry/Exp.lean` is focused-green and warning-free.  The maximal
  square-root-time domain is now preconnected; `lRegWitness_eq` propagates
  arbitrary-base-time germ uniqueness across overlapping witness intervals;
  and `lRegCurve_eqOn` identifies the totalized maximal curve with every local
  witness.

  The local ODE flow has also been promoted to actual parameter dependence.
  `exists_lPhaseFlow` gives a jointly smooth chart phase flow near a regular
  seed, `exists_lRegFamily` reconstructs a common smooth intrinsic family for
  nearby initial tangent vectors, and `lRegCurve_smoothAt` proves the
  regularized joint extension at `(Z,0)`.  Composing with `sqrt` away from zero,
  `exists_lExpFamily` proves joint smoothness of `lExp` on a uniform short
  positive-time interval.  No compactness/completeness consumer hypothesis,
  ordinary exponential-map definition, or new solution class was introduced.

  The exact next producer is `lRegFamily_extend`: continue this smooth family
  across a compact subinterval of a witnessed regularized solution, using the
  local phase flow and `lRegWitness_eq`.  This is needed before claiming joint
  smoothness at every positive point of the full maximal `lExpDomain`.
  Pullback/parabolic-scaling naturality also remains in L3, and L4 must not use
  the short-time theorem as an all-domain statement.

  Honest progress: `redVolume_anti` **0%**; dedicated L-geometry machinery
  about **22--24%**; reusable generic prerequisites about **65--75%**; P2 as a
  whole remains below **1%**.  The whole Poincare program estimate remains
  **3--5%**.

- 2026-08-21 (L3 full maximal-domain smoothness and naturality): L3 is now
  complete for the ordinary fixed-manifold `SolutionOn` model.  `Exp.lean`
  extends the local phase collar along every witnessed compact
  square-root-time segment.  The resulting declarations `lRegFamily_extend`,
  `lRegCurve_smooth`, `lRegCurve_smoothAt`, `lRegJointDom_open`,
  `lRegCurve_smoothOn`, `lExpPosDom_open`, and `lExp_smoothOn` give joint
  smoothness on the full positive maximal domain, while retaining the smooth
  regularized extension at `s = 0`.

  `Scaling.lean` proves both witness directions under parabolic rescaling and
  then identifies `lRegDomain`, the totalized `lRegCurve`, `lExpDomain`, and
  `lExp`; the terminal formula uses `Z -> R^(-1/2) Z` and `tau -> R*tau`.
  The generic metric input is the native `covDerivAlong_scale` theorem.
  `Naturality.lean` separately proves fixed-diffeomorphism naturality from the
  generic `chartRep_map_diff` and `covAlong_natMDiff` bridges.  Its
  single-witness theorem is directional, while the maximal-domain equality
  genuinely uses the inverse diffeomorphism.  `Perelman/LGeometry.lean` is now
  the import-only public entry point.

  All edited L3 modules are focused-green and warning-free; the two new
  terminal modules also pass targeted module verification.  The lane contains
  no `sorry`, `admit`, new axiom, reference-tree import, new foundational
  class, or strengthened compactness/completeness consumer assumption.

  The exact next declaration is `lRegJacobiPair` in a new `Jacobi.lean`: the
  fully paired scalar linearization of the regularized L-geodesic equation,
  with the current-time metric frozen in both along-curve covariant
  derivatives.  Then define `HasLRegJacobiAt` and `IsLRegJacobi`; the first
  substantive theorem is `lRegVar_jacobi` for a smooth family of regularized
  L-geodesics.  Connecting that theorem to the local `lExp` family will require
  a pointwise `cov_commute_at` adapter in the generic curvature-commutation
  layer, because the existing public wrapper assumes a globally smooth
  variation.  The fixed-chart pointwise identity already exists, so this is a
  routine local API placement task rather than a mathematical blocker and does
  not require consultation.

  Honest progress: `redVolume_anti` **0%**; dedicated L-geometry machinery
  about **30--32%**; reusable generic prerequisites about **75--80%**; P2 as a
  whole remains below **1%**.  The whole Poincare program estimate remains
  **3--5%**.

- 2026-08-22 (L4 Jacobi bridge, index form, and fixed-endpoint second
  variation): the regularized variation equation is now fully connected to the
  ordinary positive-backward-time equation.  `Jacobi.lean` proves
  `lRegVar_jacobiAt`, `lRegVar_jacobi`, the initial-tangent field
  `lRegJacobiField`, `lRegCurve_jacobi`, its normalization
  `lRegJacobi_d0`, and the differential identity `lExpJacobi_eq`.

  `SecondVariation.lean` defines the dynamic `lJacobiVel`, `lJacobiPair`,
  `HasLJacobiAt`, and `IsLJacobi`.  The fully paired square-root bridge
  `lJacobiPair_sq`, the moving-connection regularity theorem
  `lJacobiVel_sq_diff`, and `lJacobi_of_sq` yield `lExp_jacobi` without
  comparing whole moving bundle or Hom-valued objects.  The supporting
  Ricci-flow connection layer separates the scalar pairing identities
  `connBack_pair` and `connBack_along_sq` from `connBack_vec_sq`, which
  reconstructs chart differentiability of the resulting moving vector field.

  The L-index layer now contains `lIndexInt`, `lIndex`, pointwise and integral
  symmetry, the diagonal formula, the scalar balance identity
  `lIndex_balance`, zero interval, adjacent additivity with honest
  integrability hypotheses, Green's identity, the fixed-endpoint form, and the
  Jacobi boundary formula.  The scalar producers `lEuler_var_c1`,
  `lVarJacobiVel_diff`, and `lVarInner_c1` generate the compact-interval
  integrability needed by the concrete consumer.  Consequently
  `lLength_second_var` is proved with only its natural inputs: a smooth
  variation, a central L-geodesic, and fixed endpoints.  Its conclusion is the
  exact equality between the second derivative of L-length and twice
  `lIndex Y Y`; no nonnegativity is claimed without minimization or
  no-conjugate-point input.

  Focused verification is warning-free, the exported `SecondVariation` module
  refresh passes, and the import-only L-geometry umbrella checks against the
  refreshed artifact.  The edited lane contains no `sorry`, `admit`, new axiom,
  reference-tree import, foundational class, generalized RFWS object, or
  strengthened consumer assumption.

  The exact next theorem is `lRegJacobi_unique` in `Jacobi.lean`: on a connected
  regularized-time interval, two regularized L-Jacobi fields along the same
  curve with equal value and equal frozen-metric covariant derivative at one
  time agree throughout the interval.  It should be produced from the native
  regularized phase/ODE uniqueness layer, not added as a consumer hypothesis.
  This is the gate for defining L-conjugate points via the initial-tangent
  differential of `lExp`, and then proving the remaining L4 output, positivity
  of the index form before the first conjugate point.

  Honest progress: `redVolume_anti` **0%**; `lLength_second_var` **100%**;
  the broader L4 phase about **70--75%**; dedicated L-geometry machinery about
  **48--52%**; reusable generic prerequisites about **88--92%**; P2 as a whole
  remains below **1%**.  The whole Poincare program estimate remains **3--5%**.

- 2026-08-22 (L4 regularized Jacobi uniqueness and conjugacy):
  `LGeometry/JacobiUnique.lean` is focused-green and warning-free.
  `lRegJacobi_unique` proves initial-value uniqueness on a connected open
  regularized-time set by putting the field and its moving covariant velocity
  into a fixed-chart linear ODE and propagating equality by an open/relatively
  closed argument.  Its public hypotheses do not assume that the base curve is
  an L-geodesic or add an acceleration equation.

  The reusable coefficient input is now honest: `scalarHess_cont` and
  `nablaRicci_cont` supply the joint scalar-Hessian and covariant-Ricci tensor
  families, while `lRegJacCLM_cont` reconstructs the geometric velocity from
  its fixed-chart coordinate and proves operator-norm continuity without
  unfolding tensor or Hom representations.  The two generic regularity
  producers and the uniqueness module pass focused verification; the new
  exported modules have the targeted refreshes needed by their consumers.

  `LGeometry/Conjugate.lean` is also focused-green and warning-free.  `IsLConj`
  includes positive `lExp`-domain membership, so the totalized off-domain value
  cannot create artificial conjugate points.  `isLConj_iff` and
  `isLConj_iff_jac` give the kernel and regularized-Jacobi characterizations;
  `lExpDeriv_inj` and `lExpDeriv_surj` give the finite-dimensional
  nonconjugate differential consequences.

  The exact next theorem is `lRegIndex_balance` in a new `RegIndex.lean`.
  Define the square-root-time index density so that

  ```text
  d/ds <D_s Y,W> = 2 K_s(Y,W) + lRegJacobiPair(Y,W).
  ```

  This removes the positive-lower-endpoint restriction from the Green identity
  and permits a genuine endpoint at `s = 0`.  The subsequent bridge to the
  ordinary `lIndex` must prove the change of variables only almost everywhere:
  the pointwise density identity need not hold at `s = 0`.  Do not claim index
  positivity by adding a supplied semidefiniteness hypothesis; its remaining
  input is the native L-minimizer and field-realization layer.

  Honest progress: `redVolume_anti` **0%**; `lRegJacobi_unique` **100%**;
  the conjugacy definition/characterization brick **100%**; the broader L4
  phase about **78--82%**; dedicated L-geometry machinery about **52--56%**;
  reusable generic prerequisites about **90--93%**; P2 as a whole remains below
  **1%**.  The whole Poincare program estimate remains **3--5%**.

- 2026-08-22 (L4 endpoint-zero regularized index): `Jacobi.lean` now exposes
  `lRegJacobi_dyn_eq`, the residual-preserving moving-velocity identity; the
  original `lRegJacobi_dyn` is its Jacobi-zero corollary, so the connection
  calculus is not duplicated.  The refactored module is focused-green and its
  exported artifact is refreshed.

  The new `LGeometry/RegIndex.lean` is focused-green and warning-free.  It
  defines `lRegIndexInt` and `lRegIndex`, proves pointwise and integral
  symmetry, and establishes

  ```text
  d/ds <D_s Y,W> = 2 lRegIndexInt(Y,W) + lRegJacobiPair(Y,W).
  ```

  Consequently `lRegIndex_green` is valid on oriented intervals whose endpoint
  may be `s = 0`; `lRegIndex_zero_ends` and `lRegIndex_jacobi` give the
  fixed-endpoint and Jacobi boundary forms.  `lRegIndexInt_sq` identifies the
  positive-time density under `tau = s^2`, while `lIndex_sq` proves the
  interval identity by an almost-everywhere congruence that removes only the
  singleton `s = 0`.  No false pointwise equality at zero is stated.  The
  terminal L-geometry umbrella checks against the targeted `RegIndex` export.

  The exact next theorem is `lRegAction_second` in a new `RegAction.lean`.
  Define the direct regularized Lagrangian and action on a raw regularized
  curve, prove the first-variation formula, and then show that a smooth
  fixed-endpoint regularized variation about an `IsLRegCurveOn` central curve
  has second derivative `2 * lRegIndex Y Y`.  Produce compact domination and
  integrability internally; do not pass through an epsilon-to-zero limit and
  do not add a supplied semidefiniteness or minimizer assumption.

  Honest progress: `redVolume_anti` **0%**; the regularized index/Green/square
  bridge **100%**; the broader L4 phase about **82--85%**; dedicated L-geometry
  machinery about **55--59%**; reusable generic prerequisites about
  **90--93%**; P2 as a whole remains below **1%**.  The whole Poincare program
  estimate remains **3--5%**.

- 2026-08-22 (L4 endpoint-zero regularized action): the new
  `LGeometry/RegAction.lean` defines the direct square-root-time Lagrangian
  `lRegLag` and action `lRegAction`.  `lRegDensity_eq` and `lLength_reg`
  identify them with the earlier square-reparameterized density and ordinary
  L-length.  `lRegLag_deriv`, `lRegAction_deriv`, `lRegEuler_var_c1`, and
  `lRegAction_first` provide the pointwise, integral, regularity, and
  integration-by-parts first-variation layers with compact domination
  produced internally.

  The capstone `lRegAction_second` is focused-green and exported through the
  public L-geometry umbrella.  For a supplied smooth fixed-endpoint variation
  about an `IsLRegCurveOn` central curve it proves that the second derivative
  of regularized action is `2 * lRegIndex Y Y`.  The interval may have an
  endpoint at `s = 0`.  Jacobi integrability comes from the joint Euler
  regularity and `lRegEuler_deriv`; index-density integrability is proved
  internally from the independent metric/curve-time `C^2` theorem
  `lVarMetric_c2`, `inner_deriv_at`, and `lRegIndex_balance`.  No epsilon limit,
  supplied domination, minimizer wrapper, or semidefiniteness hypothesis was
  introduced.  Focused checks, the targeted `RegAction` export, and the
  import-only umbrella check all pass without warnings.

  The exact next theorem is `lRegIndex_nonneg_var` in a new
  `LGeometry/Minimizer.lean`: an actual smooth fixed-endpoint variation whose
  regularized action has a local minimum at the central parameter has
  nonnegative diagonal `lRegIndex`.  It should be a direct consequence of
  `lRegAction_deriv`, `lRegAction_second`, and the native real-calculus theorem
  `second_deriv_nonneg_of_isLocalMin`, not a supplied semidefinite wrapper.
  The following producer is the generic fixed-endpoint field-realization
  theorem needed to apply this result to an arbitrary smooth field; the
  existing complete-metric exponential producer is mathematically stronger
  than necessary, so the local ordinary-exponential route is being checked in
  the generic variation layer before adding L-specific assumptions.

  Honest progress: `redVolume_anti` **0%**; the regularized action/second-
  variation brick **100%**; the broader L4 phase about **86--89%**; dedicated
  L-geometry machinery about **58--62%**; reusable generic prerequisites about
  **90--93%**; P2 as a whole remains below **1%**.  The whole Poincare program
  estimate remains **3--5%**.

- 2026-08-22 (L4 variation-level index nonnegativity and field-realization
  blocker): the new `LGeometry/Minimizer.lean` proves the warning-free,
  exported theorem `lRegIndex_nonneg_var`.  Its hypothesis is an actual
  `IsLocalMin` statement for regularized action along a supplied smooth
  fixed-endpoint variation.  `lRegAction_deriv` supplies differentiability,
  the local-minimum derivative test gives the zero first derivative,
  `lRegAction_second` gives `2 * lRegIndex`, and
  `second_deriv_nonneg_of_isLocalMin` gives the sign.  No minimizer predicate,
  semidefinite wrapper, or desired-sign assumption was introduced.

  Extending this result to every smooth zero-endpoint field reached an honest
  missing-groundwork stop after three distinct native routes were checked.
  The ordinary `expMap` API is smooth only for a fixed base point; the local
  addition API currently needs compactness; and `exists_chartVar` handles only
  fields supported in one manifold chart.  The smallest reusable missing
  theorem is `total_exp_smooth_at` in the ordinary exponential smoothness
  layer: joint smoothness of

  ```text
  u : TangentBundle I M |-> expMap g u.proj u.snd
  ```

  at every zero vector, under local finite-dimensional manifold assumptions
  and without `CompleteSpace M`, `PseudoEMetricSpace M`, or an `IsMetricNorm`
  consumer hypothesis.  Its proof must add the varying-base
  chart-flow/`maximalGeodesic` identification missing beneath the existing
  `exists_chartExp_jointContDiffOn_nat`.  After it, the exact next producer is
  `exists_var_fix_ends` in the generic variation layer, followed by the
  arbitrary-field L-theorem `lRegIndex_nonneg`.

  Compact-manifold existence of an actual L-minimizer remains a separate
  global frontier: the current tree lacks manifold-valued weak `H^1`
  compactness, lower semicontinuity for the time-dependent kinetic action, and
  the Tonelli regularity upgrade.  This infrastructure is not hidden behind a
  supplied minimizer-existence theorem.

  Honest progress: `redVolume_anti` **0%**;
  `lRegIndex_nonneg_var` **100%**; arbitrary-field `lRegIndex_nonneg` **0%**;
  `total_exp_smooth_at` **0%**; the dedicated field-realization construction
  above that API is about **65--70%** understood but unproved; the broader L4
  phase is about **88--90%**; dedicated L-geometry machinery about
  **59--63%**; reusable generic prerequisites about **90--93%**; P2 remains
  below **1%** and the whole Poincare program remains **3--5%**.

- 2026-08-22 (L4 arbitrary-field index nonnegativity): the ordinary total
  exponential route was discarded because preferred charts do not give the
  required varying-base smoothness statement on an arbitrary charted
  manifold.  The replacement is fully local and checked.  The generic theorem
  `exists_var_fix_ends` cuts off the smooth geodesic vector field on the total
  tangent bundle near the compact image of the prescribed field, takes its
  complete compact-support flow, and projects that flow to the manifold.  It
  realizes every globally `C^8` field on `uIcc a b` and fixes both endpoints
  when the field vanishes there.  No `CompleteSpace M`, `PseudoEMetricSpace M`,
  `IsMetricNorm`, local-addition wrapper, or ordinary exponential smoothness
  hypothesis was added.

  The reusable `lRegIndex_congr` theorem transports both fields and their
  covariant derivatives on `uIoo a b`, then removes the remaining endpoint by
  an almost-everywhere interval-integral congruence.  This avoids the false
  inference that equality on a closed interval determines the two endpoint
  derivatives.  The new `lRegIndex_nonneg` combines this theorem with
  `exists_var_fix_ends` and `lRegIndex_nonneg_var`.  Its hypothesis is the
  honest statement that the central curve locally minimizes regularized action
  along every smooth fixed-endpoint variation; it does not assume the desired
  index sign.  Focused checks pass without warnings, and the generic
  field-realization export and `RegIndex` export are green.

  The exact next declaration is `sqrtReparam` in `LGeometry/Reparam.lean`,
  followed by `lLength_sqrt` in `LGeometry/RegAction.lean`.  The latter must use
  an almost-everywhere inverse square-root change of variables and discard the
  singleton backward-time endpoint; it must not require the raw curve to be
  differentiable at `tau = 0`.  Compact existence of an L-minimizer remains a
  separate direct-method frontier after this bridge.

  Honest progress: `redVolume_anti` **0%**; `lRegIndex_nonneg_var` **100%**;
  arbitrary-field `lRegIndex_nonneg` **100%**; generic fixed-endpoint field
  realization **100%**; the broader L4 phase **100%**; dedicated L-geometry
  machinery about **62--66%**; reusable generic prerequisites about
  **94--96%**.  `exists_lMinimizer` remains **0%**, with its dedicated
  direct-method machinery about **0--5%**.  P2 remains below **1%** and the
  whole Poincare program remains **3--5%**.

- 2026-08-22 (L5 inverse square-root action bridge): `sqrtReparam` now reads a
  regularized curve as a raw backward-time curve.  The positive-time identity
  `lDensity_sq_pos` uses the totalized manifold derivative and therefore holds
  for every raw curve, including the nondifferentiable branch.  The oriented
  integral theorem `lLength_sq_ae` removes the only possible exceptional point
  `s = 0` by an almost-everywhere congruence, so it requires no curve
  differentiability hypotheses.

  In the direct action layer, `lRegAction_congr` proves congruence from curve
  equality on `uIoo a b`; derivative equality is obtained only on genuine
  neighborhoods inside that open interval, and the endpoints are discarded by
  the interval measure.  `lLength_reg_ae` and the capstone `lLength_sqrt` then
  prove

  ```text
  lLength S T (sqrtReparam alpha) 0 tau
    = lRegAction S T alpha 0 (sqrt tau)
  ```

  for every `alpha` and `0 <= tau`.  In particular, the theorem does not demand
  differentiability of the singular raw curve at backward time zero.  Focused
  checks and the targeted `Reparam` and `RegAction` exports pass without
  warnings; an independent read-only audit confirmed both orientations and the
  degenerate interval `tau = 0`.

  This completes the executable inverse-reparameterization stage.  The next L5
  theorem endpoint is `exists_lMinimizer`, but it remains an honest direct-
  method blocker rather than a theorem to wrap with assumptions.  The current
  tree has no canonical manifold-valued absolutely-continuous/weak `H^1` path
  space, weak derivative subsequence extraction, lower semicontinuity theorem
  for the time-dependent metric action, or Tonelli regularity upgrade.  The
  admissible-path category must be chosen together with that API; no temporary
  `IsLAdmissible` or minimizer-existence wrapper is added here.

  Honest progress: `redVolume_anti` **0%**; inverse square-root action bridge
  **100%**; `lRegIndex_nonneg` **100%**; `exists_lMinimizer` **0%**, with its
  dedicated direct-method machinery about **0--5%**; dedicated L-geometry
  machinery about **64--68%**; reusable generic prerequisites about
  **94--96%**.  P2 remains below **1%** and the whole Poincare program remains
  **3--5%**.

- 2026-08-22 (L5 coercivity, C0 compactness, and first H1 realization): the
  direct-method preparation is now implemented through the full bounded-action
  C0 subsequence stage.  `metric_lower_icc` supplies one positive moving-metric
  coercivity constant on the compact spacetime slab.  `lScalar_lower`,
  `lAction_consts`, `lRefEnergy_bound`, and `lEdistOf_bound` turn one action
  bound into one family-wide fixed-reference energy budget and intrinsic
  square-root distance modulus, without assuming scalar curvature is
  nonnegative.  The reusable fixed-metric producers are `curveEnergy_mono` and
  `edistOf_le_budget`; `dist_lt_of_riedist` transfers the intrinsic modulus to
  any compatible compact-manifold pseudometric.

  `arzela_subseq_cpt` is the generic supplied-compact-target Arzela--Ascoli
  extraction theorem.  The L-specific capstone `lAction_subseq` applies it to
  every uniformly action-bounded sequence of regularized curves, and
  `lAction_subseq_fix` proves that two common endpoints survive in the C0
  limit.  All constants are chosen before the curve/sequence quantifier; no
  curvewise constants are silently reused as uniform data.

  The earlier claim that all AC/H1 and lower-semicontinuity infrastructure was
  absent was too broad.  The generic tree already had metric-valued absolute
  continuity and vector-valued `timeH1`.  This stage adds
  `timeH1.compact_subseq`, the genuine WeakSpace theorem
  `timeQuad_weak_lsc`, and the adapters `timeH1.ofContDiffOn`,
  `timeH1.toFun_ofContDiffOn`, and `timeH1.deriv_ofContDiffOn`.
  `chartCoord_contDiff`, `chartTimeH1`, `chartTimeH1_toFun`, and
  `chartTimeH1_deriv` then realize a C1 manifold curve whose image stays in one
  fixed chart as a coordinate-valued time-H1 path.  These generic and
  single-chart modules are focused-green without warnings or placeholders;
  required targeted exports and the L-geometry umbrella check are also green.

  The remaining stop is now precise.  There is no chart-independent
  manifold-valued weak H1 realization: finite chart localization and a weak
  chain rule on chart overlaps must identify the local weak derivatives before
  they can be compared with `lVelocity`.  The next reusable producer is an
  overlap theorem such as `chartH1_overlap`, followed by stability/lower
  semicontinuity for the curve-dependent moving-metric coefficient and
  continuity of the scalar potential integral.  A separate Tonelli/
  Euler--Lagrange regularity upgrade is then needed.  Stating
  `exists_lMinimizer` now would require choosing a new foundational path object
  or hiding these facts behind consumer assumptions, both forbidden in this
  lane.

  Honest progress: `redVolume_anti` **0%**; `exists_lMinimizer` **0%**;
  bounded-action C0 subsequence stage **100%**; fixed-chart C1-to-H1 producer
  **100%**; chart-independent manifold H1 realization about **10--15%**;
  dedicated direct-method machinery about **35--45%**; dedicated L-geometry
  machinery about **68--72%**; reusable generic prerequisites about
  **97--99%**.  P2 remains below **1%** and the whole Poincare program remains
  **3--5%**.

- 2026-08-22 (L5 weak chart-overlap chain rule): the generic theorem
  `timeH1.chain_ae` now identifies weak derivatives whenever two existing
  time-H1 representatives agree through a map on the closed time interval and
  a relative Frechet derivative is supplied along the first representative.
  It deliberately does not claim to construct nonlinear compositions in
  `timeH1`; that stronger Nemytskii/FTC theorem is unnecessary for comparing
  separately extracted chart limits.

  `chartH1_overlap` applies this producer to two time-H1 coordinate
  representatives of the same manifold curve. Its conclusion uses
  `tangentCoordChange`, hence it works under only `IsManifold I 1 M` and does
  not require a boundaryless model, finite dimensionality, compactness, a
  metric, or C1 regularity of the underlying curve. The canonical C1
  realizations are covered by `chartH1_overlap_c1`. Both modules are
  focused-green without warnings or placeholders.

  Weak derivative compatibility on an overlap is therefore no longer the L5
  blocker. The next exact generic theorem is `timeOp_weak_lim`: stability of a
  bounded time-dependent continuous-linear coefficient acting on a weakly
  convergent `timeL2` sequence when the coefficients converge uniformly in
  operator norm. In parallel, the next geometric producer is finite
  time-chart localization for the compact C0 limit image; neither step should
  introduce a new manifold-H1 foundational object. Moving-metric quadratic
  lower semicontinuity, scalar-potential continuity, and the separate Tonelli/
  Euler--Lagrange regularity upgrade remain after those producers.

  Honest progress: `redVolume_anti` **0%**; `exists_lMinimizer` **0%**;
  bounded-action C0 subsequence stage **100%**; fixed-chart C1-to-H1 producer
  **100%**; weak chart-overlap identification **100%**; chart-independent
  manifold H1 realization about **25--35%**; dedicated direct-method machinery
  about **40--50%**; dedicated L-geometry machinery about **69--73%**;
  reusable generic prerequisites about **98--99%**. P2 remains below **1%**
  and the whole Poincare program remains **3--5%**.

- 2026-08-22 (L5 coefficient weak limits and finite chart split):
  `timeOp_weak_lim` proves that uniformly essentially bounded
  operator-valued coefficients converging uniformly in essential operator norm
  preserve weak convergence of time-L2 inputs. The theorem derives the needed
  uniform input norm bound from weak convergence by Banach--Steinhaus instead
  of adding it as a consumer hypothesis. Its proof combines the existing
  `timeOp` norm bound, a strongly vanishing coefficient-error term, and the
  adjoint test for the fixed limiting operator.

  The pure topological producer `exists_chart_split` gives every continuous
  compact-interval curve an eventually finite monotone subdivision whose
  closed pieces each lie in one preferred chart source. It requires only a
  `ChartedSpace`, interval nonemptiness, and `ContinuousOn`; the implementation
  does not import the existing heavy parallel-transport theorem with unrelated
  finite-dimensional smooth-manifold context. Both new modules are
  focused-green without warnings or placeholders.

  The next exact generic stage is the local interval API in
  `TimeH1Slice.lean`: construct a time-H1 slice on `[a,b]`, identify its
  continuous representative with `t |-> u.toFun (a+t)`, and identify its weak
  derivative with the translated original derivative almost everywhere. This
  will let `exists_chart_split` feed finitely many local H1 extractions and the
  already proved `chartH1_overlap`. After slicing, the next analytic theorem is
  moving-coefficient quadratic lower semicontinuity; scalar-potential
  continuity and the separate Tonelli/Euler--Lagrange regularity upgrade still
  remain.

  Honest progress: `redVolume_anti` **0%**; `exists_lMinimizer` **0%**;
  finite chart subdivision **100%**; weak coefficient-product stability
  **100%**; chart-independent manifold H1 realization about **35--45%**;
  dedicated direct-method machinery about **45--55%**; dedicated L-geometry
  machinery about **70--74%**; reusable generic prerequisites about **99%**.
  P2 remains below **1%** and the whole Poincare program remains **3--5%**.

- 2026-08-23 (L5 finite-chart compactness and raw-action lower
  semicontinuity): the local and finite direct-method chain is now checked end
  to end. `TimeH1Slice.lean` supplies translated restrictions;
  `TimeOperatorWeak.lean` and `TimeQuadraticWeak.lean` pass weak convergence
  through uniformly convergent moving coefficients; and the finite-family
  theorem `timeH1.compact_subseq_fin` extracts one common subsequence. The
  generic finite chart producer `exists_cpt_split` also records compact chart
  buffers, not merely chart-source membership.

  `MetricFamilyGram.lean`, `MetricFamilyGramWeak.lean`,
  `ScalarCompact.lean`, and `KineticChart.lean` realize the moving kinetic and
  scalar terms with the correct forward time `T - s^2`. `ActionFinite.lean`
  turns the global C0 limit into finitely many canonical local `timeH1`
  representatives and extracts their weak derivatives simultaneously.
  `lRegAction_fin_lsc` then proves finite generalized chart-action lower
  semicontinuity. None of these theorems assumes scalar-curvature
  nonnegativity; the scalar term is controlled by compact continuity.

  The new generic bridge `curve_mdiff_local` proves that a curve represented
  by a fixed-chart `timeH1` path is manifold differentiable almost everywhere
  on the represented interval. It uses the chart inverse only within
  `range I`, so it does not add `I.Boundaryless`. Consequently
  `lRegAction_chart` identifies the finite generalized chart expression
  exactly with the raw manifold `lRegAction`. The terminal theorem
  `lAction_liminf` now gives a fixed-endpoint uniformly convergent subsequence
  and the honest inequality

  ```text
  lRegAction S T gamma a b
    <= liminf (fun n => lRegAction S T (alpha (chi n)) a b) atTop.
  ```

  Focused checks of the new producers, explicit targeted refreshes of exported
  modules, and the public `LGeometry.lean` umbrella check are green without
  warnings or placeholders. The endpoint is still not
  `exists_lMinimizer`: `exists_seq_tendsto_sInf` already handles the elementary
  minimizing-sequence bookkeeping, but the extracted local chart-H1 curve is
  not yet known to lie in the closure of the fixed-endpoint C1 competitor
  class with convergence of the action.

  The exact next generic/geometric producer is `lAction_c1_dense` in a new
  `ActionDensity.lean`. Its input should be the finite chart-H1 realization
  used by `lRegAction_chart`; its output should be fixed-endpoint C1 curves
  converging uniformly to `gamma`, strongly in the local H1 derivatives, and
  with `lRegAction` converging to `lRegAction S T gamma a b`. Three existing
  routes do not supply this statement: Mathlib manifold smooth approximation
  controls only C0 error, the current vector-valued `timeH1` API has no
  endpoint-preserving smooth-density/gluing theorem, and local L-ODE/
  `lExp` existence gives neither global endpoint shooting nor action
  minimality. Adding a new manifold-H1 foundational object or an admissibility
  wrapper would only hide this density theorem and remains forbidden. After
  density, a separate Tonelli/Euler--Lagrange regularity theorem must upgrade
  the relaxed minimizer to an `IsLRegCurveOn` curve.

  Honest progress: `redVolume_anti` **0%**; `exists_lMinimizer` **0%**;
  `lAction_liminf` and the finite-chart raw-action lower-semicontinuity stage
  **100%**; `lAction_c1_dense` **0%**; the Tonelli regularity producer **0%**;
  dedicated minimizer/direct-method machinery about **72--78%**; dedicated
  L-geometry machinery about **73--77%**. Reused generic compactness and weak
  L2 infrastructure for the completed stage is **100%**, while the new generic
  endpoint-preserving H1 density producer is **0%**. P2 remains below **1%**
  and the whole Poincare program remains **3--5%**.

- 2026-08-23 (L5 fixed-endpoint action recovery and first Tonelli bricks):
  the recovery side of the finite-chart direct method is now checked end to
  end. `TimeH1Flat.lean` proves `exists_flat_deriv`, strong approximation of a
  time-L2 derivative by a globally smooth function supported inside the open
  time interval. `TimeH1Density.lean` upgrades this to `exists_flat_dense`:
  global C1 curves with exact endpoint traces, constant germs at both
  endpoints, exact `timeH1` realization, strong H1 convergence, and strong
  derivative convergence. The proof corrects the derivative integral by a
  normalized interior bump; it does not infer endpoint flatness merely from
  pointwise support containment.

  `ActionDensityGeom.lean` supplies `exists_c1_of_flat`, including repeated
  nodes, zero-length pieces, and the empty subdivision. `ActionDensity.lean`
  constructs compact chart buffers internally, chooses one common tail over
  the finite chart family, and proves the terminal recovery theorem
  `lAction_c1_dense`. Its fixed-endpoint global C1 approximants converge
  strongly in each local chart-H1 space, uniformly as manifold curves, and in
  the complete regularized L-action. The public theorem exposes neither
  buffer choices nor stronger consumer assumptions. The focused checks,
  targeted exports, and public `LGeometry.lean` umbrella check are green
  without warnings or placeholders.

  The first genuine Tonelli bricks are also checked. `timeQuad_weak_euler`
  derives a weak Euler identity from an actual fixed-endpoint local minimizer;
  `mom_primitive` and `mom_rep_cont` turn that identity into an almost-
  everywhere momentum primitive with a continuous representative.
  `chartGramOp_unit` derives invertibility of the chart Gram operator from its
  existing metric coercivity, and `chartGramInv_cont` proves continuity of the
  inverse family on every regular chart-coordinate set. None of these results
  assumes a supplied inverse, momentum equation, or desired regularity.  The
  current momentum theorem uses an L2 force.  For the genuinely nonlinear
  chart action the position derivative contains a coefficient times
  `|u'|^2`, which is only L1 at the initial H1 regularity level; the L2 theorem
  is therefore a checked specialization, not yet the final Tonelli interface.

  The first nonlinear geometric and natural-exponent bridges are now checked.
  `ActionEuler.lean` defines `lChartLag` and `lChartAct` with the actual Gram
  and scalar coefficients evaluated along `u.toFun`, and `lRegAction_stat`
  derives stationarity of the full regularized action from an actual smooth
  fixed-endpoint local minimum.  It does not freeze the metric coefficient or
  assume the first variation.  `TimeQuadraticRegularL1.lean` proves
  `mom_primitive_l1` and `mom_rep_cont_l1`: a raw force merely integrable on
  the closed interval gives an almost-everywhere momentum primitive and a
  continuous representative.  `ActionVelocity.lean` proves `chartGram_time`,
  `chartVel_of_mom`, and `chartVel_rep_cont`; these derive the coefficient
  bound and inverse from the native metric family and turn that L1 momentum
  representative into a continuous coordinate-velocity representative.

  The full chart-H1 theorem `lChart_weak_euler` remains unstated and unproved.
  Its exact missing generic prerequisite is `timeH1_nl_deriv` in a nonlinear
  time-action module: for a curve-dependent quadratic coefficient and scalar
  potential with compact-buffer C1 bounds, differentiate the integral action
  on `timeH1`, prove that the position derivative is an actual `IntegrableOn`
  force, and derive the zero-endpoint weak Euler identity from an actual local
  minimum.  Three existing routes do not close this bridge: the fixed-
  coefficient `timeQuad_weak_euler` has the wrong nonlinear interface; the
  smooth geometric first variation now recorded by `lRegAction_stat` does not
  apply to an H1 base curve; and pointwise smoothness of `chartGramOp` does not
  by itself provide the needed Nemytskii/integral Frechet derivative into the
  H1 dual.  No L2 force, supplied Euler equation, or desired regularity may be
  added as a consumer hypothesis.  After this generic producer,
  `lChart_weak_euler` can feed the already checked L1 momentum and inverse
  chain; a later geometric identification gives `isLRegCurve_of_min`.

  Honest progress: `redVolume_anti` **0%**; `exists_lMinimizer` **0%**;
  `lAction_c1_dense` and its dedicated density machinery **100%**;
  `lAction_liminf` and raw-action lower semicontinuity **100%**; smooth
  nonlinear stationarity **100%**; the L1 momentum and momentum-to-velocity
  bridges **100%**.  The full nonlinear chart-H1 weak Euler theorem and the
  terminal Tonelli regularity theorem remain **0%**; their checked dedicated
  generic machinery is about **75--85%**, with the nonlinear H1 first-
  variation theorem still a substantial missing API rather than a local proof.
  Dedicated minimizer/direct-method machinery is about **84--89%** and
  dedicated L-geometry machinery about **78--82%**. Reused generic
  compactness, weak-L2, and endpoint-density infrastructure needed by the
  completed recovery stage is **100%**. P2 remains below **1%** and the whole
  Poincare program remains **3--5%**.

- 2026-08-23 (L5 relaxed attainment, Tonelli producers, and exact
  elaboration frontier): the fixed-endpoint direct method now attains its
  relaxed endpoint. `ActionAttain.lean` proves `exists_lRegMinC1`: a
  continuous finite-chart-H1 curve attains the infimum of the global C1
  actions and satisfies the genuine global C1 competitor inequality.
  `ActionSplice.lean` and `ActionLocalMin.lean` then prove
  `lChartAct_local`, transferring that inequality to an actual local minimum
  of every positive fixed-endpoint chart segment. These theorems do not assume
  stationarity or an Euler equation.

  The native Tonelli producer chain is checked through the point immediately
  after a weak Euler identity. `primitive_c1` and `mom_rep_c1` upgrade a
  continuous force to a C1 momentum representative. `chartGramInv_smooth`
  derives the jointly smooth Gram inverse from the native metric family.
  `chartVel_rep_c1` converts the momentum representative to a C1 velocity
  representative. `chartScalFun_smooth` and `chartScalCov_smooth` expose the
  whole chart scalar value and spatial covector without finite-coordinate
  reconstruction. `lChartForceRep_cont` and `lChartForceRep_ae` give the
  continuous representative of the actual L-force. Finally,
  `lChartVel_c1` is a verified C1-to-C2 bootstrap from the actual interval
  weak identity; it does not take a supplied force equation or inverse.

  The shared-node recovery infrastructure is also checked independently.
  `contDiffOn_Icc_join` glues adjacent closed-interval C1 pieces with matching
  one-sided derivatives. `timeH1.tent` supplies the exact `0,z,0` H1 node
  test, and `exists_tent_c1` approximates it by closed-interval C1 curves with
  exact outer endpoints and exact node value, strongly both in `timeH1` and
  in the derivative `timeL2` norm. `lNode_c1_dense` realizes two compatible
  chart-H1 pieces as one continuous shared-node curve and produces global C1
  competitors converging strongly in both pieces, uniformly on the manifold,
  and in the full regularized L-action. Repeated subdivision nodes are allowed.

  The remaining Tonelli theorem is blocked at an exact verification boundary,
  not hidden behind a new assumption. `ActionWeakEuler.lean` contains the
  source statements `lChartAct_line` and `lChart_weak_euler`, but a focused
  check deterministically exhausts 200000 heartbeats while reducing the
  minimal private producer

  ```text
  lWeakScal_cont :
    ContinuousOn
      (fun q => lWeakScal ... q.2
        (u.toFun q.2 + q.1 • v.toFun q.2))
      (Icc (-1) 1 ×ˢ Icc 0 L).
  ```

  This final route uses the checked public `chartScalFun_smooth` directly and
  passes joint lag continuity to the generic dominated-integral argument,
  which derives every parameter slice's interval integrability internally.
  Explicitly omitting the unused positive-finrank, boundaryless, and
  sigma-compact section instances from this declaration leaves the same
  deterministic timeout.
  Earlier genuinely different routes through coordinatewise scalar
  covectors, a whole scalar covector followed by a separate shifted
  integrability producer, and an isolated translated `lScalar_int` theorem
  reached the same deterministic `whnf` performance boundary. The whole-Hom
  topology issue is no longer present: the Gram derivative is fully evaluated
  on two velocities and bounded on a compact product of unit balls.

  `ActionRegular.lean` contains the source-only theorem `lChart_min_c1`, with
  the actual local-minimum input and no supplied Euler or regularity
  hypothesis, but it was intentionally not checked because its
  `ActionWeakEuler` import is not green. Neither red source module is imported
  by the public `LGeometry.lean` umbrella. All verified attainment, force,
  velocity, bootstrap, local-minimum, and shared-node recovery modules are
  imported there; the focused umbrella check is green after the one genuinely
  required targeted refresh of `ActionNodeSplice`.

  The exact next verification target remains `lWeakScal_cont` in
  `ActionWeakEuler.lean`. Once its elaboration performance is resolved, the
  concrete checked sequence is `lChart_weak_euler`, `lChart_min_c1`, and then
  the Weierstrass--Erdmann node equation `lNode_mom_match`; the last theorem
  must use the checked shared-node C1 recovery and must not assume momentum
  matching or introduce a cotangent-transition wrapper.

  Honest progress: `redVolume_anti` **0%**; terminal regular
  `exists_lMinimizer` **0%**; relaxed `exists_lRegMinC1` **100%**;
  fixed-endpoint local chart-minimum transfer **100%**; raw direct method and
  fixed-endpoint C1 recovery **100%**; generic C1 momentum/velocity,
  continuous-force, C1-to-C2, and shared-node test/recovery producers for their
  stated interfaces **100%**. `lChart_weak_euler`, `lChart_min_c1`, and
  `lNode_mom_match` are each **0% verified**; their dedicated source and
  supporting machinery is about **92--95%**, **90--93%**, and **90%**
  respectively. Dedicated minimizer/direct-method machinery is about
  **94--96%**, while dedicated L-geometry machinery is about **85--87%**.
  Reused generic infrastructure for the completed bricks is **100%**. P2
  remains below **1%** and the whole Poincare program remains **3--5%**.

- 2026-08-23 (weak Euler green, fixed-chart C1/momentum green, node corner
  execution): the previous elaboration frontier is closed.  The scalar
  space-time term is now packaged through the existing subtype-continuity API,
  so `lChartAct_line` and `lChart_weak_euler` both pass focused verification
  without warnings.  `ActionRegular.lean` then proves the actual
  local-minimizer endpoint `lChart_min_c1`, and `ActionMomentum.lean` strengthens
  it to `lChart_mom_c1`: a closed-interval C1 momentum representative equal
  pointwise to twice the chart Gram operator applied to the continuous
  velocity, with derivative equal to twice the continuous chart force.
  Neither theorem takes a supplied Euler equation, inverse Gram operator, or
  desired regularity.

  The exact node-variation support is also green.  `TimeQuadraticBoundary.lean`
  evaluates the upward and downward affine ramp integrals as the terminal and
  negative initial momentum pairings.  `TimeH1Ramp.lean` realizes those ramps
  in `timeH1`; `TimeH1Buffer.lean` supplies a nonzero common scale whose whole
  affine unit tube stays in an open chart target.  `ChartTimeC1.lean` lifts a
  C1 fixed-chart representative back to a C1 manifold curve.
  `lNode_c1_dense` now exposes the constructed curve's chart containment and
  representation facts, and the verified theorem `lNodeAct_min` uses them to
  transfer the global fixed-endpoint C1 comparison to an exact two-piece chart
  action inequality.  This comparison assumes neither stationarity nor the
  corner equation.

  The current exact theorem is `lNode_mom_match`.  Its same-chart analytic core
  is being executed directly from `lNodeAct_min`, `lChartAct_line`,
  `lChart_mom_c1`, and the two ramp boundary identities.  The cross-chart
  assembly must then localize the right-hand head in the left node chart and
  cancel the unchanged tail; affine tents in the two original charts are not
  exact shared-node variations because the chart transition is nonlinear.
  No nonlinear endpoint-amplitude wrapper or cotangent-transition object will
  be introduced.

  Honest progress: `redVolume_anti` **0%**; terminal
  `exists_lMinimizer` **0%**; relaxed `exists_lRegMinC1` **100%**;
  `lChartAct_line`, `lChart_weak_euler`, `lChart_min_c1`, and
  `lChart_mom_c1` **100%**; shared-node density and two-piece action comparison
  **100%**; `lNode_mom_match` **0% until its public theorem is proved**.
  Dedicated node-match machinery is about **94--96%**; dedicated
  minimizer/direct-method machinery about **96--97%**; dedicated L-geometry
  machinery about **87--89%**.  Reused generic compactness, weak-L2, C1,
  ramp, and endpoint-density infrastructure needed here is **100%**.  P2
  remains below **1%** and the whole Poincare program remains **3--5%**.

- 2026-08-23 (cross-chart node momentum match green): the public theorem
  `lNode_mom_match` is now focused-checked and its module refresh is green,
  without warnings or placeholders.  Starting only from the global
  fixed-endpoint C1 competitor inequality, it obtains exact two-piece action
  comparison, proves the right piece C1, rewrites a positive right-hand head
  in the left node chart, applies the checked same-chart corner theorem, and
  transports the resulting scalar Gram pairing back with
  `chartDeriv_head` and `chartGramOp_change`.  It assumes neither momentum
  matching nor curve regularity at the node.

  The next exact theorem is `lNode_vel_match`: cancel the positive-definite
  chart Gram operator from `lNode_mom_match` and prove that the two endpoint
  coordinate velocities are related by `tangentCoordChange`.  The proof must
  use the existing Gram-unit and coordinate-change composition APIs and must
  not introduce a cotangent-transition wrapper.  In parallel, the generic
  two-piece manifold C1 gluing producer is being checked at the TimeSobolev
  layer for the subsequent finite-node assembly.

  Honest progress: `redVolume_anti` **0%**; terminal
  `exists_lMinimizer` **0%**; `lNode_mom_match` **100%**;
  `lNode_vel_match` **0% until its public theorem is proved**.  Dedicated
  node-corner machinery is about **98--99%**; dedicated
  minimizer/direct-method machinery remains about **96--97%**; dedicated
  L-geometry machinery is about **89--91%**.  Reused generic infrastructure
  needed by the checked corner theorem is **100%**.  P2 remains below **1%**
  and the whole Poincare program remains **3--5%**.

- 2026-08-23 (node velocity match and generic C1 join green):
  `lNode_vel_match` is now focused-checked and refreshed without warnings or
  placeholders.  Under exactly the assumptions of `lNode_mom_match`, it uses
  coordinate-change composition, `chartGramOp_change`, and
  `chartGramOp_unit` to cancel the positive-definite Gram operator and prove
  that the right initial coordinate velocity is the tangent-coordinate
  transport of the left terminal coordinate velocity.

  The lower generic layer now also exports the checked theorem
  `curve_c1_join`.  Two positive adjacent pieces of the same manifold curve,
  C1 on their respective closed intervals and with matching one-sided
  derivatives in the node-centered chart, glue to a C1 curve on the whole
  interval.  It needs no finite-dimensionality, completeness, separation,
  compactness, or Ricci-flow assumptions and does not require one chart to
  contain both full pieces.

  The next exact theorem is `lNode_c1`: derive the C1 regularity of both
  positive L-action pieces from their local minimality, transport
  `lNode_vel_match` into the node-centered chart, and apply
  `curve_c1_join`.  Repeated or zero-length subdivision nodes remain a later
  compression step and are not silently included in this positive two-piece
  statement.

  Honest progress: `redVolume_anti` **0%**; terminal
  `exists_lMinimizer` **0%**; `lNode_mom_match` and `lNode_vel_match`
  **100%**; `lNode_c1` **0% until its public theorem is proved**.  Dedicated
  positive-node corner machinery is **100%**; dedicated
  minimizer/direct-method machinery remains about **96--97%**; dedicated
  L-geometry machinery is about **90--92%**.  The generic two-piece C1 join
  and other reused infrastructure needed here are **100%**.  P2 remains below
  **1%** and the whole Poincare program remains **3--5%**.

- 2026-08-23 (positive two-piece C1 regularity green): `lNode_c1` is now
  focused-checked and refreshed without warnings or placeholders.  From the
  same global fixed-endpoint C1 competitor inequality as the corner equation,
  it derives exact two-piece comparison, local minimality and chart C1 for
  each piece, translates the endpoint derivatives to global time, transports
  both into the node-centered chart, and applies `curve_c1_join` after
  `lNode_vel_match`.  Thus the positive two-piece minimizer is genuinely C1
  across its chart node; node regularity is a conclusion, not a hypothesis.

  The generic strict finite iteration `curve_c1_fin` is also checked and
  refreshed.  It strongly inducts over a bounded Nat-indexed subdivision,
  gluing the final segment after locally identifying the accumulated-left
  derivative with the previous-piece derivative.  This theorem deliberately
  excludes repeated nodes.

  The next exact L-geometry producer is arbitrary-window localization:
  transfer the global relaxed fixed-endpoint minimum to any adjacent positive
  two-piece window without assuming the baseline curve is already globally
  C1.  That producer will let `lNode_c1` run at every internal strict node;
  repeated/zero-length node compression remains the following separate step.

  Honest progress: `redVolume_anti` **0%**; terminal
  `exists_lMinimizer` **0%**; `lNode_mom_match`, `lNode_vel_match`, and
  positive two-piece `lNode_c1` **100%**.  Arbitrary-window localization is
  **0% until a public theorem is proved**.  Positive-node corner machinery
  and strict finite generic C1 gluing are **100%**; dedicated
  minimizer/direct-method machinery remains about **96--97%**; dedicated
  L-geometry machinery is about **91--93%**.  Reused generic infrastructure
  needed by the completed stages is **100%**.  P2 remains below **1%** and
  the whole Poincare program remains **3--5%**.

- 2026-08-23 (arbitrary positive-window comparison green):
  `lNodeWin_cmp` is focused-checked and refreshed without warnings or
  placeholders.  For any finite chart-H1 realization with at least two
  pieces, any selected adjacent positive pair, and any compatible pair of
  target-contained replacements, it embeds the replacements into the full
  dependent family, realizes the resulting continuous finite-H1 curve by
  global fixed-endpoint C1 curves, applies the genuine global minimum, and
  cancels every unchanged prefix and suffix action term.  The theorem is not
  tied to the original chart family, so it also applies after a short-head
  refinement of the right segment.

  The next exact producer is that caller-side refinement: insert a positive
  split point in one finite segment while preserving nodes, charts,
  dependent `timeH1` pieces, representations, and all unchanged complement
  data.  This will supply the common-chart left/head comparison needed by the
  already checked same-chart corner theorem at every internal node.  In
  parallel, subdivision compression is selecting all original positive
  segments while retaining their indices and exact endpoints.

  Honest progress: `redVolume_anti` **0%**; terminal
  `exists_lMinimizer` **0%**; `lNodeWin_cmp` **100%**; caller-side dependent
  refinement **0% until a public producer is proved**.  Arbitrary positive-
  window comparison machinery is about **98--99%**, with only the refinement
  consumer assembly remaining; dedicated L-geometry machinery is about
  **92--94%**.  Reused generic infrastructure remains **100%**.  P2 remains
  below **1%** and the whole Poincare program remains **3--5%**.

- 2026-08-23 (witness-preserving subdivision compression green): the generic
  theorem `exists_strict_subdiv` is focused-checked and refreshed without
  warnings or placeholders.  From a monotone `Fin (m+1)` node family it
  filters the original positive segments, enumerates them in strict index
  order, and returns a strict compressed node family together with the
  original segment map.  Each compressed segment has exactly the endpoints
  of its recorded original segment, so dependent `lSegLen`, chart, and
  `timeH1` witnesses can be transported; the all-zero case correctly returns
  no segments.  Value-only list deduplication was rejected because it would
  lose those witnesses.

  The generic compression theorem is **100%**.  The next L-specific work is
  to transport the finite realization along its returned segment map and to
  combine that strict realization with `lNodeWin_cmp` and the short-head
  refinement adapter.  `redVolume_anti` and terminal `exists_lMinimizer`
  remain **0%**; dedicated L-geometry machinery remains about **92--94%**
  because this generic producer is not itself an L endpoint.  P2 remains
  below **1%** and the whole Poincare program remains **3--5%**.

- 2026-08-23 (strict L-realization transport green): `exists_lStrict` is
  focused-checked and refreshed without warnings or placeholders.  It consumes
  `exists_strict_subdiv`, preserves the strictly increasing original positive-
  segment map, and transports the chart centers, dependent `timeH1` pieces,
  chart-source containment, and exact coordinate representatives to the
  compressed strict subdivision.  The public result needs no Ricci-flow,
  compactness, or smoothness assumptions.

  Generic subdivision compression and its L-specific realization transport are
  **100%**.  The next exact producer remains `lNodeRef_cmp`: split the selected
  right segment at a positive interior time and use `lNodeWin_cmp` to obtain the
  common-chart left/head comparison while preserving every untouched finite
  piece.  `redVolume_anti` and terminal `exists_lMinimizer` remain **0%**;
  dedicated L-geometry machinery is about **92--94%**; reused generic
  infrastructure is **100%**.  P2 remains below **1%** and the whole Poincare
  program remains **3--5%**.

- 2026-08-23 (finite right-head refinement green): `lNodeRef_cmp` is
  focused-checked and refreshed without warnings or placeholders.  At an
  arbitrary selected internal node it inserts a positive split point into the
  right segment, realizes the short head in the left chart, uses `timeH1.slice`
  for the old-chart tail, transports every dependent length witness, and
  preserves all unchanged pieces.  Applying `lNodeWin_cmp` to the refined
  realization gives the exact common-chart left/head action comparison.

  The caller-side finite refinement adapter is **100%**.  The next exact theorem
  is `lFinNode_vel`: combine this comparison with right-piece C1 regularity,
  `lNode_mom_same`, chart-head derivative transport, and Gram injectivity to
  prove velocity matching at any positive finite internal node.  Dedicated
  L-geometry machinery is about **93--95%**; reused generic infrastructure is
  **100%**.  `exists_lMinimizer` and `redVolume_anti` remain **0%**; P2 remains
  below **1%** and the whole Poincare program remains **3--5%**.

- 2026-08-23 (strict finite piece regularity green): `lStrict_piece_c1` is
  focused-checked and refreshed without warnings or placeholders.  For each
  segment of a strict finite realization it derives the actual fixed-endpoint
  local minimum from the global competitor inequality and concludes closed-
  interval C1 regularity through `lChart_min_c1`.  Strictness supplies exactly
  the positive length needed by the analytic theorem.

  Strict finite piecewise C1 regularity is **100%**.  The next exact theorem
  remains `lFinNode_vel`, followed by finite C1 gluing.  Dedicated L-geometry
  machinery is about **93--95%**; reused generic infrastructure is **100%**.
  `exists_lMinimizer` and `redVolume_anti` remain **0%**; P2 remains below
  **1%** and the whole Poincare program remains **3--5%**.

- 2026-08-23 (arbitrary finite-node velocity match green): `lFinNode_vel` is
  focused-checked and refreshed without warnings or placeholders.  Under only
  positivity of each realized piece, it proves C1 regularity for the selected
  right segment, extracts a short head in the left chart, applies
  `lNodeRef_cmp` and `lNode_mom_same`, transports the endpoint derivative
  through the chart transition, and cancels the native positive-definite Gram
  operator.  No strict-subdivision package or desired corner equation is an
  input.

  Arbitrary finite-node velocity matching is **100%**.  The next exact theorem
  is `lFinCurve_c1`: translate these coordinate endpoint equalities into the
  node-centered chart and combine them with strict piecewise regularity via
  `curve_c1_fin`.  Dedicated L-geometry machinery is about **94--96%**; reused
  generic infrastructure is **100%**.  `exists_lMinimizer` and
  `redVolume_anti` remain **0%**; P2 remains below **1%** and the whole
  Poincare program remains **3--5%**.

- 2026-08-23 (strict finite global C1 green): `lFinCurve_c1` is
  focused-checked and refreshed without warnings or placeholders.  Its
  canonical interface accepts any positive number of strict realized pieces.
  The single-piece case uses local chart regularity directly; the multiple-
  piece case converts `lFinNode_vel` at every internal node into equality in
  the node-centered chart and applies `curve_c1_fin`.

  Strict finite global C1 regularity is **100%**.  The next exact theorem is
  `lMinCurve_c1`: compress an arbitrary monotone realization with
  `exists_lStrict`, rule out the zero-piece case from `a < b`, and apply
  `lFinCurve_c1`.  Dedicated L-geometry machinery is about **94--96%**; reused
  generic infrastructure is **100%**.  `exists_lMinimizer` and
  `redVolume_anti` remain **0%**; P2 remains below **1%** and the whole
  Poincare program remains **3--5%**.

- 2026-08-23 (strict finite piece C2 green): `lStrict_piece_c2` is
  focused-checked and refreshed without warnings or placeholders.  On every
  positive strict piece it derives the genuine local minimum, obtains the
  continuous weak velocity and native weak Euler identity, applies
  `lChartVel_c1`, and uses the pointwise within-derivative identity to conclude
  `ContDiffOn Real 2` for the coordinate representative.  It assumes neither
  Euler nor C2 regularity.

  Strict finite piecewise C2 regularity is **100%**.  In parallel with the
  repeated-node/global-C1 consumer `lMinCurve_c1`, the next analytic audit is
  the genuine classical bridge from this chart Euler data to
  `covDerivAlong = lRegAccel`; no assumption-wrapped substitute will be added.
  Dedicated L-geometry machinery is about **95--96%**; reused generic
  infrastructure is **100%**.  `exists_lMinimizer` and `redVolume_anti` remain
  **0%**; P2 remains below **1%** and the whole Poincare program remains
  **3--5%**.

- 2026-08-23 (monotone finite minimizer C1 green): `lMinCurve_c1` is
  focused-checked and refreshed without warnings or placeholders.  It applies
  `exists_lStrict` to an arbitrary monotone finite realization, rules out the
  zero-piece compressed family from the strict global endpoint inequality
  `a < b`, and invokes `lFinCurve_c1`.  Repeated and zero-length chart pieces
  are therefore fully discharged before the global C1 conclusion.

  The repeated-node/global-C1 assembly is **100%**.  The next exact direct-
  method consumer is `exists_lRegMinC1On`, which hides the finite realization
  returned by `exists_lRegMinC1` and exposes the attained C1-on minimizer,
  endpoint values, exact cost equality, and genuine competitor inequality.
  Dedicated L-geometry machinery is about **95--97%**; reused generic
  infrastructure is **100%**.  `exists_lMinimizer` and `redVolume_anti` remain
  **0%**; P2 remains below **1%** and the whole Poincare program remains
  **3--5%**.

- 2026-08-23 (C1 relaxed minimizer attainment green):
  `exists_lRegMinC1On` is focused-checked and refreshed without warnings or
  placeholders.  It consumes `exists_lRegMinC1` and `lMinCurve_c1`, hides all
  finite chart-H1 and approximation witnesses, and returns a closed-interval
  C1 curve with prescribed endpoints, exact `lRegCostC1` equality, and the
  genuine global fixed-endpoint C1 competitor inequality.  It does not assert
  `IsLRegCurveOn`.  Its present signature inherits the positive-finrank
  instance from the node-regularity chain; the raw direct-method producer does
  not need that instance.

  C1 relaxed attainment is **100%**.  The exact analytic frontier is now the
  native `lChartEuler_iff` calculation converting the checked pointwise chart
  momentum equation into `covDerivAlong = lRegAccel`; after that, the minimizer
  can be identified with the regularized L-ODE on each positive piece.
  Dedicated L-geometry machinery is about **96--97%**; reused generic
  infrastructure is **100%**.  The terminal `exists_lMinimizer` and
  `redVolume_anti` remain **0%**; P2 remains below **1%** and the whole
  Poincare program remains **3--5%**.

- 2026-08-23 (classical fixed-chart Euler bridge green):
  `lChartEuler_iff` is focused-checked and refreshed without warnings or
  placeholders.  At a local chart parameter `r`, it uses the global
  square-root time `a + r` and proves the genuine equivalence between the
  differentiated chart momentum equation and the second component of
  `lPhaseField`.  The proof stays scalar after fully applying the Gram
  operator: `lRegInner_deriv` gives the moving-metric derivative,
  `chartGram_spatial` gives the spatial Gram--Christoffel identity,
  `lRegAccel_inner` gives the intrinsic acceleration pairing, and Gram
  invertibility recovers the model-space vector equation.  No Euler,
  acceleration, or smooth-solution conclusion is supplied as an assumption.

  The generic `chartGram_spatial` producer and the L-specific
  `lChartEuler_iff` bridge are **100%**.  The next exact theorem is
  `lChart_min_accel`: consume the momentum and C1 velocity representatives of
  an actual positive fixed-chart minimum, invoke `lChartEuler_iff` pointwise,
  and apply `lPhase_accel` to the shifted global phase
  `z(s) = (u.toFun (s - a), q (s - a))`.  The terminal
  `exists_lMinimizer` and `redVolume_anti` remain **0%**; dedicated L-geometry
  machinery remains about **96--97%**, reused generic infrastructure is
  **100%**, P2 remains below **1%**, and the whole Poincare program remains
  **3--5%**.

- 2026-08-23 (fixed-chart minimizer acceleration green):
  `lChart_min_accel` is focused-checked and refreshed without warnings or
  placeholders.  It derives C1 momentum and velocity representatives from a
  genuine positive fixed-chart local minimum, cancels the momentum factor,
  invokes `lChartEuler_iff`, and applies `lPhase_accel` to the correctly
  shifted phase.  It then identifies the phase velocity with the actual
  `lVelocity` on a neighborhood, so the public conclusion is the intrinsic
  `covDerivAlong = lRegAccel` equation at every interior parameter time.  No
  compactness, pseudometric, Euler equation, or acceleration equation is an
  input.

  The fixed-chart classical consumer is **100%**.  The next exact assembly is
  `lStrict_piece_accel`: derive the local minimum on every positive strict
  finite piece, apply `lChart_min_accel`, and transport the shifted inverse-
  chart curve back to the attained manifold curve.  In parallel the endpoint
  audit must determine the weakest native route extending the equation across
  subdivision nodes before claiming `IsLRegCurveOn`.  The terminal
  `exists_lMinimizer` and `redVolume_anti` remain **0%**; dedicated L-geometry
  machinery is about **97--98%**, reused generic infrastructure is **100%**,
  P2 remains below **1%**, and the whole Poincare program remains **3--5%**.

- 2026-08-23 (arbitrary-base phase existence green):
  `exists_lPhaseSol_at` is focused-checked and refreshed without warnings or
  placeholders.  At any regular square-root time `s0` and chart-interior phase
  state `z0`, it constructs the autonomized integral curve directly through
  `(s0,z0)` at parameter time `s0`; a generalized clock lemma then identifies
  the first component with actual time on a two-sided neighborhood.  No time
  translation is used, so the nonautonomous field retains the correct
  `T - s^2` dependence.

  Arbitrary-base phase existence is **100%**.  The next exact producer is
  `exists_lRegCurve_at`, reconstructing a genuine intrinsic local curve with
  prescribed position and velocity at `s0` and the full regularized solution
  triple.  That producer will support the endpoint patch after the internal-
  node regularity assembly.  The terminal `exists_lMinimizer` and
  `redVolume_anti` remain **0%**; dedicated L-geometry machinery is about
  **97--98%**, reused generic infrastructure is **100%**, P2 remains below
  **1%**, and the whole Poincare program remains **3--5%**.

- 2026-08-23 (strict finite open-piece acceleration green):
  `lStrict_piece_accel` is focused-checked and refreshed without warnings or
  placeholders.  It applies the fixed-chart minimizer theorem on every
  positive strict piece, identifies the shifted inverse-chart curve with the
  attained manifold curve as a germ through the exact representation witness,
  transports `lVelocity` by the native `mfderiv` germ congruence, and transports
  the covariant derivative with `covDerivAlong_congr_curve`.  Thus the actual
  attained curve satisfies `covDerivAlong = lRegAccel` at every point in every
  open piece; no equation or regularity conclusion is an input.

  Strict finite open-piece acceleration is **100%**.  The next exact frontier
  is the node/endpoint extension needed before asserting `IsLRegCurveOn` for
  the attained curve.  It must combine strict piecewise C2, global C1 node
  matching, and a native continuity or phase-ODE argument; it must not simply
  omit the finite nodes from a theorem whose set includes them.  The terminal
  `exists_lMinimizer` and `redVolume_anti` remain **0%**; dedicated L-geometry
  machinery is about **97--98%**, reused generic infrastructure is **100%**,
  P2 remains below **1%**, and the whole Poincare program remains **3--5%**.

- 2026-08-23 (arbitrary-base intrinsic regularized curve green):
  `exists_lRegCurve_at` is focused-checked and refreshed without warnings or
  placeholders.  From any regular square-root time `s0`, prescribed point
  `x`, and prescribed actual tangent velocity `A0`, it reconstructs the local
  phase solution as a manifold curve with `alpha s0 = x` and
  `lVelocity alpha s0 = A0`.  On a two-sided neighborhood it supplies the full
  local regularized triple: manifold differentiability, differentiability of
  the actual-velocity chart representative, and the intrinsic acceleration
  equation.  No regularized solution or Euler equation is an input.

  Arbitrary-base intrinsic regularized curve existence is **100%**.  The next
  exact theorem is `lFinNode_reg`: combine global finite C1 gluing with the two
  adjacent strict C2/acceleration pieces and a deleted-neighborhood derivative
  extension to obtain the full regularity triple at every internal node.  The
  endpoint patch will then use `exists_lRegCurve_at` on both sides of the
  closed minimizing interval.  The terminal `exists_lMinimizer` and
  `redVolume_anti` remain **0%**; dedicated L-geometry machinery is about
  **98%**, reused generic infrastructure is **100%**, P2 remains below **1%**,
  and the whole Poincare program remains **3--5%**.

- 2026-08-23 (internal-node and full-interior regularity green):
  `hasDerivAt_of_punct`, `lStrict_piece_c2_at`, `lFinNode_reg`,
  `lStrict_curve_reg`, and `lMinCurve_reg` are focused-checked and their
  downstream exports are refreshed without warnings or placeholders.  The
  generic deleted-neighborhood theorem extends a continuous derivative field
  through one puncture.  At every strict internal node, global C1 gluing makes
  the actual chart phase continuous while the adjacent C2/acceleration pieces
  solve the phase equation off the node; phase reconstruction then supplies
  manifold differentiability, actual-velocity chart differentiability, and
  the intrinsic acceleration equation at the node itself.  Finite segment
  coverage assembles pieces and nodes on the full open interval, and
  `exists_lStrict` transports the conclusion back across repeated and
  zero-length pieces of an arbitrary monotone realization.

  Internal-node regularity and the full open-interval regularity package are
  **100%**.  The exact remaining direct-method regularity producer is
  `exists_lRegExt`: keep the attained curve on `Icc a b`, attach the
  arbitrary-base local regularized curves outside its two endpoints, and use
  the same punctured phase argument to make total `lVelocity` and acceleration
  honest at both endpoints.  Only after that theorem is green may the closed-
  interval `IsLRegCurveOn` minimizer be packaged.  The terminal
  `exists_lMinimizer` and `redVolume_anti` remain **0%**; dedicated L-geometry
  machinery is about **98--99%**, reused generic infrastructure is **100%**,
  P2 remains below **1%**, and the whole Poincare program remains **3--5%**.

- 2026-08-23 (closed-interval endpoint extension green):
  `exists_lRegExt` is focused-checked and refreshed without warnings or
  placeholders.  It starts from a curve that is C1 on `Icc a b` and satisfies
  the full regularized equation on `Ioo a b`.  The one-sided chart derivatives
  determine honest endpoint tangent data; `exists_lRegCurve_at` supplies local
  regularized curves through those data, and the returned total curve uses
  them outside the closed interval while remaining equal to the original
  curve on `Icc a b`.  A punctured phase argument at each endpoint proves the
  total manifold derivative, actual-velocity chart differentiability, and
  intrinsic acceleration equation there.  In particular, no total endpoint
  derivative of the original closed-interval curve is assumed.

  Closed-interval endpoint extension is **100%**.  The next exact theorem is
  `exists_lRegMinOn`: consume the finite witnesses of `exists_lRegMinC1`, use
  `lMinCurve_reg` for the open interval, apply `exists_lRegExt`, normalize
  `Z = (1/2) * lVelocity alpha 0`, and package the attained curve as
  `IsLRegCurveOn` on `Icc 0 b` while retaining exact cost and competitor data.
  The terminal `exists_lMinimizer` and `redVolume_anti` remain **0%**;
  dedicated L-geometry machinery is about **99%**, reused generic
  infrastructure is **100%**, P2 remains below **1%**, and the whole Poincare
  program remains **3--5%**.

- 2026-08-23 (endpoint-honest regularized minimizer green):
  `exists_lRegMinOn` is focused-checked and refreshed without warnings or
  placeholders.  It deliberately consumes `exists_lRegMinC1` before hiding
  the finite realization, obtains closed-interval C1 and open-interval full
  regularity from `lMinCurve_c1` and `lMinCurve_reg`, and applies
  `exists_lRegExt`.  The returned curve is an actual `IsLRegCurveOn` on
  `Icc 0 b`, has the prescribed terminal point, realizes `lRegCostC1`, and is
  no more expensive than every global fixed-endpoint C1 competitor.  Its
  normalized initial tangent is defined from the repaired curve's actual total
  velocity, not from the original one-sided direct-method witness.

  The endpoint-honest regularized minimizer theorem is **100%**.  The next
  exact capstone is `exists_lMinimizer`: expose the same result in raw backward
  time using `sqrtReparam` and `lLength_sqrt`, with an explicit cost/competitor
  statement that does not introduce a temporary admissible-path class or
  enlarge the competitor category beyond what the direct method proved.  The
  terminal theorem itself remains **0%** until stated and proved;
  `redVolume_anti` remains **0%**.  Dedicated L-geometry machinery is about
  **99%**, reused generic infrastructure is **100%**, P2 remains below **1%**,
  and the whole Poincare program remains **3--5%**.

- 2026-08-23 (compact raw L-minimizer capstone green):
  `lCost`, `lCost_eq_reg`, and `exists_lMinimizer` are focused-checked and the
  capstone export is refreshed without warnings or placeholders.  `lCost` is
  the infimum of raw `lLength` over `sqrtReparam` of global regularized C1
  fixed-endpoint competitors; this selects the exact category proved by the
  direct method without adding a temporary admissible-path predicate.
  `lCost_eq_reg` applies `lLength_sqrt` competitor by competitor.  On a compact
  manifold and positive backward time, `exists_lMinimizer` then applies the
  endpoint-honest regularized minimizer at `sqrt tau` and returns an actual
  `IsLRegCurveOn` whose raw L-length equals `lCost` and is no greater than that
  of every competitor in the stated class.

  The compact global-regularized-C1 `exists_lMinimizer` endpoint is **100%**;
  its dedicated direct-method and regularity machinery is **100%**.  This does
  not claim an AC or piecewise-C1 category, nor the complete noncompact L8
  extension.  The next L5 frontier is the unique-minimizing/cut domain, its
  local-diffeomorphism and star-shaped structure, and the measure-zero cut
  image needed for reduced length.  `redVolume_anti` remains **0%**; P2 remains
  below **1%**, and the whole Poincare program remains **3--5%**.

- 2026-08-23 (minimizing-prefix and downward cut fibers green):
  `exists_chartH1_join` is focused-checked and refreshed without warnings or
  placeholders.  It combines two closed-interval C1 curves meeting at a node
  into one finite chart-H1 realization, with the common node duplicated across
  a zero-length middle segment.  `lReg_prefix_min` then uses this realization,
  global fixed-endpoint C1 density, action convergence, and honest interval
  additivity to show that a global regularized minimizer minimizes every closed
  C1 prefix.  The companion `lRegCostC1_eq_on` identifies such a closed-prefix
  minimizer with `lRegCostC1` without adding a global-C1 hypothesis.

  The maximal-flow API now exports `lRegDomain_seg`, `lRegDomain_reg`,
  `lRegCurve_c1On`, `lExpPosDom_down`, and `lExpPosDom_reg`.  `lMinDomain_down`
  consumes these statements and the prefix theorem to prove that minimizing
  membership survives every decrease to a positive backward time;
  `lMinFiber_ord` packages each fixed-initial-tangent fiber as an
  order-connected set.  All of these modules are focused-checked and their
  exported symbols are refreshed.

  The backward-time star-shaped/order-connected minimizing-fiber theorem is
  **100%**; compact global minimizer attainment is **100%**; and the
  nonconjugate local-diffeomorphism producer is **100%**.  The strict pre-cut
  uniqueness / cut-alternative theorem is unstated and unproved (**0%**), and
  the cut-image measure-zero theorem is unstated and unproved (**0%**).
  `IsLMinVec` includes equality at a possible cut time, so the inclusive
  `lMinDomain` is not generally expected to be open; an `interior` wrapper
  would not replace the missing cut mathematics.  The next exact stage is the
  strict pre-cut uniqueness/cut alternative, followed by the separate open
  injectivity domain and its measure-zero cut image.

  `redVolume_anti` remains **0%**.  Dedicated L-geometry machinery for the
  compact ordinary-flow route is about **90%**; generic finite-chart and C1
  density infrastructure used here is **100%**.  P2 remains below **1%**, and
  the whole Poincare program remains approximately **3--5%**.

- 2026-08-23 (strict pre-cut uniqueness green):
  `CutStrict.lMinVec_unique_lt` is focused-checked, axiom-audited, and refreshed
  without warnings or placeholders.  If the `Z` ray minimizes through `tau`,
  `0 < sigma < tau`, and a minimizing `W` ray reaches the same point at
  `sigma`, then `W = Z`.  The strict inequality is essential because
  `IsLMinVec` deliberately includes equality at a possible cut time.

  The proof is the native broken-path argument.  It splices the `W` prefix to
  the `Z` tail, converts both minimizing raw lengths to regularized actions,
  and uses additivity to show that the splice is still globally minimizing.
  `exists_chartH1_join` and `lMinCurve_c1` force C1 matching at the node;
  one-sided `mfderivWithin` uniqueness identifies the two node velocities.
  Finally `lRegSol_eqOn` propagates the matched phase state back to zero, where
  the normalization `A(0) = 2 Z` recovers equality of initial tangents.  The
  public theorem's axiom audit reports only `propext`, classical choice, and
  quotient soundness.

  Strict pre-cut uniqueness is **100%**.  The next exact theorem is
  `lMinVec_nconj_lt`: a ray that remains minimizing to a later time is not
  L-conjugate at a strictly earlier time.  That theorem is currently unstated
  and unproved (**0%**).  Its smallest missing mathematical producer is an
  L-specific `lIndex_neg_conj`: from an interior vanishing nonzero L-Jacobi
  field, construct a globally smooth zero-endpoint field with strictly
  negative `lRegIndex`.  Existing `isLConj_iff_jac`, `lRegIndex_green`,
  `lRegIndex_jacobi`, and `lRegIndex_nonneg` reach both sides of this bridge,
  but no native declaration currently connects them.

  The later `lCut_alt` boundary theorem is also unstated and unproved (**0%**).
  Beyond nonconjugacy it needs the Morgan--Tian min--max bound and a native
  compactness/stability theorem for minimizing initial tangents, so that a
  bounded sequence has a convergent subsequence whose limit remains
  minimizing.  Therefore openness of the genuine injectivity domain and the
  cut-image measure-zero theorem remain **0%**.  Do not replace them by
  `interior (lMinDomain ...)`.

  `redVolume_anti` remains **0%**.  Dedicated L-geometry machinery for the
  compact ordinary-flow route is about **90--91%**; the generic splice,
  finite-chart, C1-density, and ODE-uniqueness infrastructure used here is
  **100%**.  P2 remains below **1%**, and the whole Poincare program remains
  approximately **3--5%**.

- 2026-08-24 (strict pre-cut nonconjugacy green):
  `IndexNegative.lIndex_neg_conj` and `CutStrict.lMinVec_nconj_lt` are now
  focused-checked without warnings or placeholders.  The latter uses the
  weakest public assumptions: positivity of `sigma` is recovered from the
  assumed L-conjugacy rather than repeated as a hypothesis.

  The native negative-index producer is necessarily branchwise.  A canonical
  Jacobi field vanishing at `sqrt sigma` is globalized together with its ray;
  the Green cross term is paired with a polynomial test field, and an honest
  integrability-aware quadratic expansion chooses two directions whose index
  sum is negative.  They agree at the conjugate node and vanish at the two
  outer endpoints.  `IndexNode.lIndex_sum_nonneg` realizes those directions by
  a common moving-node variation and proves their index sum nonnegative from
  fixed-endpoint minimizing action, yielding the contradiction.  Treating the
  node as fixed would kill the Green cross term and is not a valid substitute.

  The supporting exported bricks are also green: germ congruence and adjacent
  interval algebra in `RegIndexAlgebra`, compact-interval density integrability
  in `RegIndexSmooth`, ray/Jacobi neighborhood globalization in
  `RayGlobalize`, and the moving-node second-variation identity in `IndexNode`.
  All interval-addition and quadratic-expansion uses carry the required
  `IntervalIntegrable` hypotheses.

  Strict pre-cut nonconjugacy is **100%**.  The next exact endpoint is the
  boundary cut alternative `lCut_alt`, which remains unstated and unproved
  (**0%**); it still requires the separate minimizing-vector compactness/
  stability and min--max input described above, rather than another consumer
  wrapper.

  `redVolume_anti` remains **0%**.  Dedicated L-geometry machinery for the
  compact ordinary-flow route is now about **92%**; generic splice,
  finite-chart, C1-density, and ODE infrastructure reused by this stage is
  **100%**.  P2 remains below **1%**, and the whole Poincare program remains
  approximately **3--5%**.

- 2026-08-25 (boundary cut alternative and genuine injectivity domain green):
  The compactness/min--max route is now closed without a frontier wrapper.
  `MinVecBound.lRegInit_bound` and `MinVecVar.lRegInit_var` turn uniform
  regularized action bounds into bounded initial tangents; `RayContinue`
  proves `lRegDomain_of_slab`, continuing every regularized L-ray across a
  compact regular backward-time slab.  `CutAlternative.lCut_alt` then proves
  the boundary alternative: at the greatest minimizing time, the initial
  tangent is either L-conjugate or a distinct minimizing tangent reaches the
  same endpoint.  All of these declarations are focused-green without
  warnings or placeholders, and the exported modules needed downstream have
  been refreshed.  The `lCut_alt` axiom audit reports only `propext`, classical
  choice, and quotient soundness.

  `CutInjectivity` defines the textbook strict domain
  `lInjDomain = {Z | exists sigma > tau, (Z,sigma) in lMinDomain}` rather than
  using `interior (lMinDomain ...)`.  `lInj_isOpen` proves this domain open
  without assuming positivity of the displayed `tau`; at positive time,
  `lInj_local` and `lInj_inj` prove that fixed-time `lExp` is locally a smooth
  diffeomorphism and globally injective on it.  `CutLocus` defines
  `lCutDomain`, `lCutImage`, `lCutConj`, and `lCutMulti`; proves the fixed-time
  minimizing slice and cut domain closed; records Borel measurability of the
  tangent cut domain; and proves

  ```text
  lCutImage = lCutConj union lCutMulti.
  ```

  The split, closedness, and tangent-domain measurability endpoints are
  focused-green and their axiom audits again report only `propext`, classical
  choice, and quotient soundness.  This does **not** prove that the cut image
  is measurable or null.

  The next exact image theorems are `lCutConj_null` and `lCutMulti_null`, both
  still unstated and unproved (**0%**).  The conjugate branch has Mathlib's
  Euclidean Sard core
  `addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`, but the required
  Riemannian-volume chart-null transfer exists only as a consumer-specific
  theorem under the elliptic Hessian tree; importing that consumer into
  L-geometry would invert the architecture.  The smallest generic repair is
  to factor a chart-null theorem into `Analysis/Integration/Measure` and then
  add finite/countable chart localization.  The multiple-minimizer branch is
  the larger frontier: it needs a positive compact-slab local-Lipschitz theorem
  for `lCost`, followed by a manifold-chart Rademacher/null-transfer theorem
  and the implication from two minimizing tangents to nondifferentiability.
  Existing `CostContinuity` and Euclidean Rademacher APIs do not supply these
  L-specific and manifold bridges.  Claiming cut-image measurability or
  nullity now would therefore trigger the plan's honest stop condition rather
  than close the mathematics.

  `lCut_alt`, strict-domain openness/injectivity, the tangent cut-domain
  topology, and the set-theoretic cut-image split are each **100%**.  The
  cut-image measure-zero theorem remains **0%**, and `redVolume_anti` remains
  **0%**.  Dedicated compact ordinary-flow L-geometry machinery is about
  **96--97%**; generic compactness, chart, C1-density, and ODE infrastructure
  reused by the completed stage is **100%**.  P2 remains below **1%**, and the
  whole Poincare program remains approximately **3--5%**.

- 2026-08-25 (fixed-time cut nullity and first reduced-length brick green):
  The two cut-image branches are now closed without assuming cut-image
  measurability.  `CutConjNull.lCutConj_null` combines Euclidean Sard with the
  generic finite-chart/Riemannian-volume null-transfer API.  For the multiple
  branch, `CostChartLip.lCost_chart_lip` proves chart-local Lipschitz regularity
  of fixed-time L-cost on every positive compact regular slab, including the
  unreachable-endpoint case where the real infimum is over the empty set.
  `LocalBranch.lCost_nondiff_two` proves that two distinct nonconjugate
  minimizing rays reaching one endpoint force failure of manifold
  differentiability.  Manifold Rademacher, the conjugate/multiple cut split,
  and set inclusion then give `CutMultiNull.lCutMulti_null` and
  `CutMultiNull.lCut_null`.

  These declarations are warning-free focused green without placeholders.
  The direct modules needed by the public import-only umbrella were refreshed,
  and the umbrella itself is focused green.  Axiom audits of
  `lCutMulti_null` and `lCut_null` report only `propext`, classical choice, and
  quotient soundness.  Thus the fixed-time cut-image nullity theorem is
  **100%**.

  `ReducedLength` now defines

  ```text
  redLength(S,T,x,y,tau) = lCost(S,T,x,y,tau) / (2*sqrt(tau))
  ```

  and proves the positive-time cancellation laws plus
  `redLength_diff_ae`: on a compact positive regular time slice, reduced
  length is manifold-differentiable outside a Riemannian-volume null set.
  This first L6 brick is **100%**, focused green, and its axiom audit again
  reports only the standard three axioms above.

  `ReducedLength.lCost_eq_branch` is also warning-free focused green and its
  axiom audit reports only the standard three axioms above.  For an initial
  tangent in the strict injectivity domain, it identifies L-cost on a
  neighborhood of the endpoint with the inverse-L-exp action branch.  The
  proof pulls the open strict minimizing domain back through
  `lExp_localDiffeo`, uses `lMinDomain_down` for nearby inverse images, and
  finishes with the local-inverse identities and `lLength_sqrt`.  This local
  cost/branch equality stage is **100%**.

  The exact next producer is `lRayAct_hasFDeriv` in `RayEndpoint.lean`: the
  Fréchet derivative, with respect to the initial tangent, of the fixed-time
  regularized ray action.  Its derivative is the terminal metric-flat
  covector composed with the differential of fixed-time L-exp.  This is the
  smallest honest bridge from the existing one-parameter first variation to
  the full manifold differential.  Mathlib's parametric interval-integral
  differentiation API and the native joint smooth L-ray family provide the
  intended route.  `lRayAct_hasFDeriv` is now being implemented and remains
  **0%** until focused green.  Only after it may the local-inverse chain rule
  prove `lActBranch_hasMFD`, followed by `lCost_hasMFD` and the spatial
  gradient formula.  The existing curvewise endpoint derivative alone is not
  any of those results.

  `redVolume_anti` remains unstated and unproved at **0%**.  Dedicated compact
  ordinary-flow L-geometry machinery is about **98%**; the generic compactness,
  finite-chart, C1-density, ODE, null-transfer, and manifold-Rademacher
  infrastructure reused by this stage is **100%**.  P2 remains below **1%**,
  and the whole Poincare program remains approximately **3--5%**.

- 2026-08-25 (strict-region spatial differential and gradient green):
  The parameter-dependent action layer is now native and checked.  The generic
  `hasFDerivAt_paramInt` differentiates a jointly `C2` compact-interval
  integral under the integral sign.  `RayEndpoint.lRayAct_hasFDeriv` applies it
  to the regularized ray action and identifies the derivative with the
  terminal metric-flat covector composed with fixed-time `d lExp`.
  `LocalBranch.lActBranch_hasMFD` composes with the local inverse and cancels
  `d lExp` against `d localInverse`.

  On the strict minimizing domain, `ReducedLength.lCost_hasMFD` transports that
  derivative through `lCost_eq_branch`; `lCost_grad` raises the cotangent.
  `redLength_hasMFD` and `redLength_grad` apply the fixed
  `(2 * sqrt(tau))^-1` normalization.  Finally `Exp.lExp_vel_sqrt` proves the
  square-root/raw-time velocity conversion under only `0 < tau`, and
  `redLength_grad_ray` gives the textbook identity that the spatial reduced-
  length gradient equals the ordinary backward-time velocity of the minimizing
  L-exponential ray.

  All declarations in this substage are warning-free focused green and contain
  no placeholders or new frontier assumptions.  Targeted artifact refreshes
  were used only when the newly exported parameter-integral, branch-derivative,
  or velocity symbols had an actual downstream consumer.  The strict-region
  spatial differential/gradient substage is **100%**.  The next L6 stage is the
  backward-time derivative at fixed endpoint; its exact smallest producer is
  being audited against the existing action and local-inverse APIs before any
  new declaration is added.

  `redVolume_anti` remains unstated and unproved at **0%**.  Dedicated compact
  ordinary-flow L-geometry machinery is about **99%**; the generic parametric-
  integral, manifold differential, gradient, and reparameterization
  infrastructure reused by this substage is **100%**.  P2 remains below
  **1%**, and the whole Poincare program remains approximately **3--5%**.

- 2026-08-25 (strict-region time derivative and Hamilton--Jacobi green):
  `RayEndpoint.lRayAct_joint` now differentiates regularized ray action jointly
  in initial tangent and positive backward terminal time.  It rewrites the
  variable upper-limit action as a fixed `[0,1]` parameter integral, uses the
  checked parameter-integral derivative, identifies the tangent partial by
  endpoint first variation, and identifies the time partial by the fundamental
  theorem of calculus and the square-root derivative.

  `ReducedLength.lCost_hasDeriv` composes that joint derivative with
  `CutLocal.lExpTime_local`.  The inverse differential applied to the fixed-
  endpoint time direction forces the endpoint part of `d lExp` to vanish.  A
  single fixed later minimizing time keeps the inverse branch inside the open
  strict domain, so its action is eventually equal to L-cost.  The resulting
  checked formula is

  ```text
  partial_tau L = sqrt(tau) * (R - |X|^2).
  ```

  Differentiating the normalization gives `redLength_hasDeriv`, and combining
  it with `redLength_grad_ray` gives the pointwise strict-region
  `redLength_HJ` identity.  `lRayAct_joint`, `lCost_hasDeriv`,
  `redLength_hasDeriv`, and `redLength_HJ` are warning-free focused green,
  contain no placeholders or new frontier assumptions, and the exported
  `ReducedLength` module has been refreshed successfully.  The strict-region
  spatial/time differential and Hamilton--Jacobi substage is **100%**.

  The next exact L6 producer is `lActBranch_hess` in `LocalBranch.lean`: the
  Hessian of the inverse-L-exp action branch must be identified with the
  terminal metric pairing of the corresponding regularized L-Jacobi field.
  This is the smallest missing second-order endpoint API.  It is required
  before the canonical index-form comparison `lCost_hess_le`; the latter is
  unstated and unproved (**0%**) until that producer is green.  Only after the
  index-form comparison should the adapted-field ODE and trace contraction be
  introduced for the explicit Morgan--Tian Laplacian bound.  The existing
  fixed-endpoint second variation cannot replace this moving-endpoint Hessian
  bridge.

  `redVolume_anti` remains unstated and unproved at **0%**.  Dedicated compact
  ordinary-flow L-geometry machinery remains about **99%**; generic parametric-
  integral, manifold differential, local-inverse, gradient, and calculus
  infrastructure reused by this substage is **100%**.  P2 remains below
  **1%**, and the whole Poincare program remains approximately **3--5%**.

- 2026-08-25 (branch Hessian and abstract index comparison green):
  `BoundedCurve.exists_smooth_curve` now exposes the `C∞` regularity already
  supplied by its bounded chart-sine construction.  The one order-eight
  consumer in `RayEndpoint` explicitly downgrades this stronger result before
  forming its product parameter map; both the producer and consumer are
  warning-free focused green and refreshed.

  `LocalBranch.lActBranch_hess` identifies the Hessian of the inverse-L-exp
  action branch with the terminal metric pairing of the covariant derivative
  of the induced regularized L-Jacobi field.  Its proof constructs a global
  smooth endpoint curve in the local-inverse source, lifts it to initial
  tangent space, realizes the associated regularized-ray family inside one
  common clamped time domain, and uses intrinsic covariant commutation.  The
  branch theorem is warning-free focused green and the module refresh is
  successful.

  `ReducedLength.lCost_hess_le` is warning-free focused green under the honest
  germ interface.  For every field `W` that is `C⁸` on an open neighborhood
  of the compact strict minimizing-ray interval, with `W(0)=0` and prescribed
  terminal value `V`, it proves

  ```text
  Hess(L)(V,V) <= 2 * I(W,W).
  ```

  The proof uses `exists_lRay_germ_in` to globalize `J`, `W`, and `Q=W-J`
  while preserving their compact-interval germs and keeping the clamp range
  inside the supplied smooth neighborhood.  Thus it does not assume that the
  totalized raw regularized curve is smooth outside its maximal domain.  It
  proves `I(Q,Q) >= 0` from minimizing action, uses the Jacobi Green identity
  to obtain `I(J,Q)=0`, and combines the square expansion with
  `lActBranch_hess`.  `RegIndexSmooth.chartRep_diff_at` supplies the pointwise
  differentiability bridge from local `ContMDiffAt` data.

  The canonical scalar law `Hessian.hessFun_smul` is checked under its weakest
  assumptions.  `ReducedLength.redLength_hess_le` is also warning-free focused
  green and gives the normalized comparison

  ```text
  Hess(l)(V,V) <= I(W,W) / sqrt(tau).
  ```

  The next exact L6 producer is `exists_lAdapted` for the ordinary
  fixed-manifold square-root-time ODE at initial backward time zero.  Its first
  scalar cancellation brick is the adapted moving-inner-product derivative,
  followed by the adapted index identity and trace contraction giving the
  explicit Morgan--Tian Laplacian inequality.  That explicit trace theorem is
  still unstated and unproved (**0%**); it must not be counted complete merely
  from the abstract index comparison.  `redVolume_anti` remains unstated and
  unproved at **0%**.  Dedicated compact ordinary-flow L-geometry machinery
  remains about **99%**; reused generic infrastructure is **100%**.  P2 remains
  below **1%**, and the whole Poincare program remains approximately
  **3--5%**.

- 2026-08-25 (adapted-field producer and finite trace green):
  `CurvatureOperator.RicciSharpChart.ricciSharp_chart` now gives the fixed-
  trivialization scalar formula for the time-dependent Ricci sharp map.  Moving
  that algebra to its generic lower layer removed the deterministic heartbeat
  wall encountered by three consumer-local dependent-coordinate proofs.

  `AdaptedField.exists_lAdapted` constructs the actual square-root-time adapted
  field on an open neighborhood of a compact positive interval.  It uses a
  terminal-metric parallel orthonormal frame, solves the smooth finite-
  dimensional coefficient ODE, and reconstructs a field with prescribed
  terminal value.  `lAdapted_inner` and `lAdapted_inner_eq` prove the moving-
  pairing cancellation and closed-interval constancy.  All three theorems are
  warning-free focused green and the module refresh is green.

  `AdaptedIndex.lIndex_adapted_pt` and `lIndex_adapted` give the pointwise and
  integrated single-field Morgan--Tian identity.  `AdaptedTrace.lIndex_trace`
  sums it over a terminal orthonormal family, propagates orthonormality along
  the interval, contracts the terminal term to `finrank`, and contracts the
  Ricci diagonal sum to `S.scalar`.  Its focused check and exported refresh are
  warning-free green.  Thus the adapted-field producer, scalar cancellation,
  single-field identity, and finite adapted trace are each **100%**.

  The exact next L6 theorem is `redLength_lap_le` in a new
  `LGeometry/Laplacian.lean`: identify the strict-region Laplacian with the
  endpoint orthonormal Hessian trace, apply `redLength_hess_le` fieldwise, and
  substitute `lIndex_trace`.  The smallest prerequisite is a public local
  smoothness projection for reduced length from the already proved local
  inverse-action branch; global smoothness must not be assumed.  The later
  contraction of the retained finite sum of `lRegIndexInt` to Morgan--Tian's
  Hamilton `H(X)` expression is a separate time-Ricci/scalar-evolution stage.

  `redLength_lap_le` is still **0%** until stated and checked, and
  `redVolume_anti` remains unstated and unproved at **0%**.  Dedicated compact
  ordinary-flow L-geometry machinery remains about **99%**; reused generic
  infrastructure, including `ricciSharp_chart` and native curvature trace APIs,
  is **100%**.  P2 remains below **1%**, and the whole Poincare program remains
  approximately **3--5%**.

- 2026-08-25 (strict-region supplied-family Laplacian trace green):
  The local inverse-action smoothness already proved inside `LocalBranch` is now
  public as `lActBranch_smooth`.  `ReducedLength.lCost_smooth` transports it
  through strict-domain action equality, and `redLength_smooth` applies the
  fixed positive-time scalar normalization.  Each theorem returns a genuine
  open endpoint neighborhood; no global smoothness of cost or reduced length is
  assumed.  Their focused checks and exported refreshes are warning-free green.

  `Laplacian.redLength_lap_le` identifies the endpoint Laplacian with an
  orthonormal Hessian trace, applies `redLength_hess_le` fieldwise, sums the
  inequalities, and substitutes `lIndex_trace`.  Its public hypotheses retain
  only the supplied scaled-field `C8` regularity, adapted ODE, terminal
  orthonormality, and the two honest integrability families.  Regular Ricci-flow
  times and differentiability of the regularized L-ray are derived internally
  from `Z ∈ lInjDomain`; they are not repeated as consumer assumptions.  The
  resulting checked bound has the form

  ```text
  Delta l <= n/(2*tau) + (1/sqrt(tau)) * integral_0^sqrt(tau)
    [ (s/sqrt(tau))^2 * sum_i lRegIndexInt(P_i,P_i)
      - (2*s^2/tau) * R ].
  ```

  The supplied-family strict-region Laplacian trace theorem and its dedicated
  local-smoothness machinery are each **100%**.  The exact next theorem is
  `lIndexInt_trace` in a new `LGeometry/TraceDensity.lean`: under pointwise
  orthonormal adapted fields, contract the retained finite index-density sum to
  its scalar spatial expression using the native curvature trace, scalar
  Hessian trace, Ricci norm, and contracted-Bianchi APIs.  Only after that
  spatial theorem is green should scalar evolution rewrite the result as the
  Morgan--Tian Hamilton `H(X)` integrand.

  The final Hamilton-`H` Laplacian bound remains unstated and unproved at
  **0%**, and `redVolume_anti` remains unstated and unproved at **0%**.
  Dedicated compact ordinary-flow L-geometry machinery remains about **99%**;
  reused generic infrastructure is **100%**.  P2 remains below **1%**, and the
  whole Poincare program remains approximately **3--5%**.

- 2026-08-26 (Hamilton--`K` trace and strict-region Laplacian bound green):
  `TraceDensity.lIndexInt_trace` contracts the pointwise finite sum of adapted
  regularized index densities to the scalar spatial expression

  ```text
  2*s^2*|Ric|^2 - (1/2)*Ric(A,A) + s^2*Delta R.
  ```

  `HamiltonH.lTrace_deriv` combines that identity with scalar evolution and
  the square-root-time scalar chain rule.  Its polynomial form avoids division
  at `s = 0`; `lK_sq` records the exact change from the ordinary Hamilton
  integral to square-root time.  `TraceIntegral.lTraceInt_eq` derives all
  remaining scalar regularity from the smooth regularized ray and integrates
  the identity on a positive compact interval, without adding a new
  scalar-curvature integrability hypothesis.  `HamiltonBound.redLength_lap_K`
  substitutes the result into `redLength_lap_le` and proves

  ```text
  Delta l <= n/(2*tau) - R
    - K/(2*tau*sqrt(tau))
  ```

  on the strict minimizing domain with exactly the field smoothness, adapted
  ODE, terminal orthonormality, and honest index/Ricci integrability already
  required by the supplied-family comparison.  `lIndexInt_trace`, the
  Hamilton scalar/derivative layer, `lTraceInt_eq`, and `redLength_lap_K` are
  each **100%**.  Their focused checks are warning-free, their exported modules
  have been refreshed, and the umbrella focused check is green.

  The capstone `redVolume_anti` remains unstated and unproved at **0%**.  The
  exact next L7 stage is the moving-metric Jacobian density of `lExp` and its
  logarithmic derivative on the strict injectivity domain.  It must be derived
  from `lExp_jacobi`, the L-Jacobi endpoint fields, and the checked Hessian/
  Laplacian trace; it must not be introduced as a pointwise monotonicity
  assumption.  The source metric at time `T` and target metric at time
  `T - tau` must be normalized honestly before applying the native
  parametrization/change-of-variables API.  Dedicated compact ordinary-flow
  L-geometry machinery is about **99%**; reused generic infrastructure is
  **100%**.  P2 remains below **1%**, and the whole Poincare program remains
  approximately **3--5%**.

- 2026-08-26 (fixed-manifold reduced-volume monotonicity capstone green):
  `Jacobian.lExpTrace_eq`, `lExpJac_hasDeriv`, and `lExpLog_hasDeriv` identify
  the moving L-exponential determinant rate.  `Monotonicity` now internally
  constructs the canonical adapted terminal-orthonormal family and derives
  the required local index and Ricci integrability; consequently
  `lRedJac_deriv_le0` and `lRedJac_anti` have no supplied-field or
  pointwise-monotonicity hypotheses.

  The generic integration layer now exports `riemVol_param_lint`, a weighted
  partial-parametrization formula for arbitrary nonnegative extended-real
  integrands.  `ReducedVolume.lExpPartial` realizes fixed-time L-exp on the
  strict injectivity domain, and `lExpPartial_density` identifies its native
  parameter density with `lExpDensity`.  `lExp_inj_cover` and `lExp_inj_ae`
  prove that the complement of the strict target image is cut-image null;
  they deliberately make no claim that the complement of the tangent-space
  source domain is null.

  `redVolume_lint` combines full-measure target coverage, weighted change of
  variables, and the fixed source density.  For positive `tau1 <= tau2`, with
  the single honest regularity assumption

  ```text
  Icc (T - tau2) T subset D.regular,
  ```

  `redVolume_anti` compares the pulled-back integrands by `lRedJac_anti` on
  the later strict domain and then enlarges to the earlier nested domain.  It
  is **100%**: stated, proved without placeholders, warning-free focused
  green, exported through the umbrella, and axiom-audited with only `propext`,
  classical choice, and quotient soundness.

  The next follow-up outside the completed monotonicity capstone is the
  Euclidean small-time normalization theorem, tentatively
  `redVolume_zero_lim`, followed by the compact smooth-flow
  `smooth_nlc` producer.  Dedicated compact ordinary-flow L-geometry is about
  **99%** when that separate normalization follow-up is included; generic
  infrastructure used by the capstone is **100%**.  P2 remains below **1%**,
  and the whole Poincare program remains approximately **3--5%**.

- 2026-08-26 (Euclidean small-time normalization started):
  `SmallTime.lRayAct_zero_lim` proves

  ```text
  LRegAction(gamma_Z; 0,s) / (2*s) -> g(T)(Z,Z)
  ```

  from the right by joint ray-Lagrangian smoothness and the exact initial
  velocity `2 Z`.  `SmallTime.lRedLen_sq_lim` then uses one later strict
  minimizing witness, `lMinDomain_down`, and `lLength_sqrt` to identify
  reduced length at `tau = s^2` with that normalized action for all
  sufficiently small positive `s`.  Both public producers are warning-free
  focused green, and the `SmallTime` artifact has been refreshed.

  The generic SPD layer now exports checked `spdSqrt_det` and `gaussSPD_int`.
  `SourceGaussian.lSrcGram_pd`, `lSrcGauss`, and `lSrcGauss_mass` use those
  results plus the exact `modelHaar` pushforward to prove that the source
  Gaussian has total ENNReal mass one.  This source normalization brick and
  its generic Gaussian infrastructure are each **100%**.

  `SmallJacobian.lJacCoord_zero_lim` is focused green and gives the normalized
  first-order L-Jacobi limit in one fixed tangent trivialization.  The private
  normalized Gram-matrix limit has also elaborated successfully; the public
  `lExpDen_zero_lim` proof has been written but is **not yet counted complete**
  because its final focused verification is pending a safe Windows commit
  window.  The next exact pointwise theorem after that verification is
  `lRedJac_zero_lim`, combining `lExpDen_zero_lim`, `lRedLen_sq_lim`, and
  `lRedJac_mul_src` on the filter supplied by one later `lInjDomain` witness.

  For the separate global source-domain exhaustion,
  `ShortMinimizing.lRegInit_shrink` is warning-free focused green: an
  `O(b)` action bound on shrinking regularized intervals uniformly bounds the
  initial tangents.  The exact remaining producer is bounded-ball short-time
  endpoint injectivity for `W |-> lRegCurve S T x W b`.  Three routes reduce
  to the same missing generic calculus bridge: a compact-uniform removable
  quotient whose spatial derivative stays close to the invertible map
  `2 * id`, followed by a quantitative lower-Lipschitz/injectivity estimate.
  This is not replaced by an injectivity hypothesis or a consumer wrapper.

  Consequently `redVolume_anti` remains **100%**, while
  `redVolume_zero_lim` is still unstated and unproved at **0%** and
  `smooth_nlc` is still unstated and unproved at **0%**.  Dedicated pointwise
  zero-time machinery is about **70%**; dedicated global source-exhaustion
  machinery is about **35%**; reused generic Gaussian/change-of-variables
  infrastructure is **100%**.  P2 remains below **1%**, and the whole Poincare
  program remains approximately **3--5%**.

- 2026-08-26 (pointwise Euclidean normalization complete):
  `SmallJacobian.lExpDen_zero_lim` is warning-free focused green and its
  artifact has been refreshed.  It proves

  ```text
  lExpDensity(s^2) / (2*s)^n -> lSrcDensity.
  ```

  `SourceGaussian.lSrcGram_quad` identifies the coordinate Gram quadratic
  form with the intrinsic terminal metric norm, and `lSrcGauss_eq` exposes
  that intrinsic exponent.  Together with the already checked
  `lSrcGauss_mass`, the source Gaussian brick is warning-free focused green
  and refreshed.

  `SmallReduced.lRedJac_zero_lim` combines the density limit,
  `lRedLen_sq_lim`, and `lRedJac_mul_src` under one later strict-minimizing
  witness.  `SmallReduced.lRedJac_le_gauss` then applies `lRedJac_anti` and
  `ge_of_tendsto` to obtain the positive-time intrinsic Gaussian upper bound.
  Both declarations are warning-free focused green, their artifact is
  refreshed, and the L-geometry umbrella focused check is warning-free green.

  The dedicated pointwise zero-time machinery is therefore **100%**.  The
  next exact geometric producer remains bounded-ball short-time endpoint
  injectivity for `W |-> lRegCurve S T x W b`; this is the gate from the
  checked `lRegInit_shrink` bound to global strict-domain exhaustion.  Its
  smallest generic input is a compact-uniform derivative-closeness estimate
  yielding a quantitative lower-Lipschitz bound.  No injectivity hypothesis or
  consumer wrapper substitutes for that producer.

  Consequently `redVolume_anti` remains **100%**, while
  `redVolume_zero_lim` remains unstated and unproved at **0%** and
  `smooth_nlc` remains unstated and unproved at **0%**.  Dedicated global
  source-exhaustion machinery remains about **35%**; reused generic
  Gaussian/change-of-variables infrastructure is **100%**.  P2 remains below
  **1%**, and the whole Poincare program remains approximately **3--5%**.

- 2026-08-26 (strict source-domain exhaustion green):
  `Analysis.Calculus.paramInt_tendstoUnif` proves compact-uniform convergence
  of shrinking interval averages from joint continuity.  The new
  `SmallEndpoint.lEnd_inj_small` applies that interface to the normalized
  regularized endpoint chart, uses the native near-identity derivative
  estimate, and proves bounded-ball endpoint injectivity for every sufficiently
  small positive square-root time.

  `SmallExhaustion.lInj_eventually` is warning-free focused green and its
  artifact is refreshed.  It extracts a positive bad sequence tending to
  zero, chooses minimizing initial vectors at doubled backward times, bounds
  their actions by the fixed ray, applies `lRegInit_shrink`, and puts the
  minimizers together with the fixed tangent in one closed ball.  The checked
  endpoint injectivity then identifies each minimizer with the fixed tangent,
  producing the strictly later minimizing witness that contradicts badness.
  Thus the source-domain exhaustion theorem and its dedicated geometric
  machinery are **100%**, with no added assumption or wrapper.

  `SmallReduced.lRedJac_tau_lim` is checked and refreshed in the original
  backward-time parameter.  `SmallVolume.redVolume_le_one` is also checked and
  refreshed, proving the global upper bound by integrating the pointwise
  source-Gaussian estimate.  The exact active theorem is
  `SmallVolume.redVolume_zero_lim`: use `redVolume_lint`, eventual source-domain
  membership, pointwise `lRedJac_tau_lim`, the source Gaussian as a dominator,
  and `lSrcGauss_mass` in filter dominated convergence.  The theorem itself
  remains **0%** until stated and verified; its dedicated global-normalization
  assembly is about **70--75%**.  `redVolume_anti` remains **100%**,
  `smooth_nlc` remains **0%**, reused generic infrastructure is **100%**, P2
  remains below **1%**, and the whole Poincare program remains approximately
  **3--5%**.

- 2026-08-26 (small-time reduced-volume normalization green):
  `SmallVolume.redVolume_zero_lim` is now stated, warning-free focused green,
  and refreshed.  The proof rewrites reduced volume as a whole-source
  indicator integral, uses `SmallExhaustion.lInj_eventually` and
  `SmallReduced.lRedJac_tau_lim` for pointwise convergence, dominates by the
  checked source Gaussian through `lRedJac_le_gauss`, and closes with
  `lSrcGauss_mass` and filter dominated convergence.  The umbrella import is
  warning-free focused green as well.

  Therefore `redVolume_zero_lim` is **100%**, its dedicated pointwise,
  source-exhaustion, and global-normalization machinery is **100%**, and reused
  generic infrastructure is **100%**.  The next exact public theorem is
  `smooth_nlc : ... -> NoLocalCollapsing S rho`; it must be the L-geometry
  producer for the existing canonical predicate, not a wrapper around the
  already checked W-entropy producer.

  The live route audit found an honest missing-groundwork stop for direct
  assembly.  `redVolume_anti` together with `redVolume_zero_lim` gives only
  `redVolume <= 1`.  The L-route still needs (i) a uniform positive reduced-
  volume floor on compact regular spacetime slabs and (ii) a local upper bound
  `redVolume(alpha * r^2) <= C * volume(B) / r^n + gaussianTail(alpha)` under
  `FlowMetricBall.IsRmControlled`.  Only after those producers can the result
  be converted to `B.IsKappaNoncollapsed` and assembled with the early-time
  branch into `NoLocalCollapsing`.

  `SmoothNLC.redVolume_set_low` is now warning-free focused green and
  refreshed.  It proves that a measurable target set on which
  `redLength <= l0` contributes its volume times the exact standard reduced-
  density constant to `redVolume`, without `hS`, positive-time, regularity, or
  curvature assumptions.  This first reference-faithful input is **100%**.

  A separate native audit shows that the next uniform theorem
  `redVolume_unif_low` cannot yet be proved from the pointwise zero-time limit.
  The smallest missing producer is fixed-positive-time joint lower
  semicontinuity of `(T,x) |-> redVolume S T x tau`, tentatively
  `redVolume_lsc`.  The current cost, L-exponential, strict-domain exhaustion,
  and Jacobian-limit APIs all fix `T` and `x`; none supplies the required joint
  parameter stability.  The best route is `redVolume_lsc`, compact finite
  cover, then `redVolume_anti`, rather than an invalid uniformization of the
  pointwise DCT.  The smallest lower geometric input to audit next is a joint
  parameter upper-semicontinuity producer for L-cost, tentatively
  `lCost_lt_param` in `CostContinuity.lean`.

  Thus direct `smooth_nlc` assembly and `redVolume_unif_low` each meet an honest
  missing-API stop.  `smooth_nlc` remains **0%** until its declaration itself is
  proved; its dedicated reduced-volume-to-ball machinery is about **2--3%**,
  while the dedicated uniform-floor machinery is about **25--35%** once the
  already checked pointwise normalization and monotonicity are counted
  separately.  `redVolume_anti` remains **100%**, P2 remains below **1%**, and
  the whole Poincare program remains approximately **3--5%**.

- 2026-08-26 (status-routing refresh): all earlier dated percentages remain
  historical.  The current fixed compact-flow facts are:

  * `redVolume_anti`: **100%**, stated, focused-check green, and axiom-audited;
  * `redVolume_zero_lim`: **100%**, stated and focused-check green;
  * `smooth_nlc`: **0%**, unstated and unproved;
  * dedicated compact fixed-manifold L0--L7 machinery: about **99%**;
  * dedicated reduced-volume-to-noncollapse machinery: about **2--3%**.

  The exact next producer chain is

  ```text
  lCost_lt_param -> redVolume_lsc -> redVolume_unif_low
    + Rm-controlled-ball reduced-volume upper estimate
    -> IsKappaNoncollapsed -> smooth_nlc.
  ```

  `lCost_lt_param` first needs the reusable varying-length chart-action
  continuity theorem obtained by reparameterizing to one fixed interval.  The
  ball upper estimate is an independent branch and must not be replaced by a
  supplied noncollapse hypothesis.  The complete bounded-curvature L8 layer
  and surgery/eventwise L9 layer remain separate later endpoints.  Under the
  whole P0--P9 denominator, the final `poincare_of_inputs` theorem remains 0%
  and full-program infrastructure is estimated at **15--25%**; this supersedes
  the old 3--5% snapshots.

- 2026-08-27 (L8 endpoint and L9 parameter stability refresh): the complete
  bounded-curvature minimizer file now exports warning-free focused-green
  `exists_lRegMin_rm`, `exists_lMin_rm`, and `exists_lMinVec_rm`; its named
  artifact is refreshed.  The last theorem returns an actual
  `(Z, tau) ∈ lMinDomain S T x`, the endpoint equation, and the minimizing
  action data.  The action-regularity chain used by this endpoint was also
  generalized away from ambient `CompactSpace M` and checked bottom-up.  Thus
  this complete-flow minimizer endpoint is **100%**, but the later complete
  noncompact cost-Lipschitz/minimum/distributional/rigidity chain is not thereby
  complete.

  On the L9 parameter branch, `lCost_lt_param` and `redVolume_lsc` are **100%**:
  both are focused green and their named artifacts are refreshed.  The latter
  proves fixed-positive-time joint lower semicontinuity in `(T, x)` from the
  honest regular slab hypothesis.  Its targeted refresh reports only a local
  file-ending style warning, whose mechanical cleanup remains pending.  The
  compact finite-cover theorem `redVolume_unif_low` is now **100%** and
  warning-free focused green.  It is proved from `redVolume_zero_lim`,
  `redVolume_lsc`, a finite positive infimum, and two monotonicity transfers,
  with no uniform-limit hypothesis.  Its named artifact refresh is complete.
  The `RedVolumeParam` file-ending style warning has also been
  fixed and rechecked without changing any exported declaration.

  In parallel, `lRegRanges_compact` and `lRegRanges_of_rm` are warning-free
  focused green.  They put every member of an action-bounded family with common
  start into one compact reference-metric ball; the base `CompleteFlow`
  artifact and the `CompleteFlowBound` curvature-adapter artifact are both
  refreshed.  The next honest complete-flow input after them is a compact-target
  scalar-gradient bound in the canonical `MinMaxCompact` layer; that file
  currently has another lane's live claim and must not be duplicated elsewhere.

  On the scale-uniform ball branch, `lMetric_scale`, prefix-local
  `lRegSpeed_scale`, whole-range `lRegRange_scale`, and endpoint corollary
  `lExp_scale_ball` are warning-free focused green and refreshed.  The
  prefix-local form is essential: at a first exit one knows ball containment
  only on `Icc 0 s`, not on the whole future interval.  The proof was split at
  the substantive fixed-scale speed estimate to remove a deterministic
  heartbeat timeout without raising global limits.  Three further genuine
  lower producers are also warning-free green and refreshed:
  `scalar_ge_of_rm`, one-sided noncompact `volumeMeasure_le` (with the sharp
  square-root determinant factor), and the dimension-uniform source Gaussian
  tail `lSrcGauss_unif`.  Their compact-slab assembly `redVolume_ball_le` is
  now warning-free focused green, its named artifact is refreshed, and the
  umbrella import is warning-free focused green.  Its quantifiers are honest:
  the terminal `time` and one compact regular backward slab are fixed before
  the theorem chooses `eps0`; it does not claim one short-scale threshold for
  the half-open terminal-time interval.  The theorem splits the exact source
  domain into the localized ball part and its complement, bounds the latter by
  the uniform source-Gaussian tail, and obtains the checked terminal-ball
  volume factor plus `1 / 4`.  Thus `redVolume_ball_le` is **100%**, while
  `smooth_nlc` remains unstated/unproved at **0%**.

  The exact coordinated verification order is now:

  ```text
  verified moving-range / scalar / volume / Gaussian-tail producers
  -> compact-slab redVolume_ball_le [checked]
  -> half-open-time uniform floor -> smooth_nlc.
  ```

  The half-open-time arrow has now been audited separately.  The intended
  next theorem is `redVolume_late_low`: for fixed
  `0 < a0 < a < omega`, produce one positive reduced-volume floor for every
  terminal time `T ∈ [a, omega)` and every `tau ≤ T - a0`.  Compactness of
  `[a,b] × M` proves only a floor depending on `b < omega`, so it does not
  prove this statement.  The Morgan--Tian initial-slice route instead needs
  the genuine producer

  ```text
  exists_redLen_le : exists q, redLength S T x q (T - a1) <= finrank / 2
  ```

  for each terminal time.  Its missing input is the all-point spacetime weak
  upper-barrier inequality
  `partial_tau l + Delta l <= (n / 2 - l) / tau` across the cut locus.  The
  existing strict-domain Hamilton--Jacobi and Laplacian formulas, and the
  existing spatial branch upper support, do not yet supply this spacetime
  barrier.  Therefore `redVolume_late_low` and `smooth_nlc` both remain
  **0% theorem endpoints**; this is the current honest L9 frontier rather than
  a finite-cover or parameter-continuity gap.

  Honest aggregate status: `redVolume_anti` **100%**;
  `redVolume_zero_lim` **100%**; compact fixed-manifold L0--L7 about **99%**;
  `redVolume_ball_le` **100%**; dedicated L-geometry including the still-open
  complete-flow and half-open-time L8--L9 endpoints about **46--48%**; generic
  infrastructure reused by the checked bricks **100%**.
  `smooth_nlc`, the P2 conclusion, and the final `poincare_of_inputs` theorem
  remain **0% as theorem endpoints**; under the whole P0--P9 denominator the
  full-program infrastructure estimate remains **15--25%**.

- 2026-08-27 (positive-start Calabi and initial-slice splice producers):
  `exists_lTailFamily` is warning-free focused green and refreshed.  It uses
  `exists_lPhaseAt` at an arbitrary regular square-root time to produce a
  jointly smooth family with fixed position and varying actual velocity; it
  does not change the zero-base `2 * Z` convention.  The next family-extension
  theorem `lTailFamily_step` is source-written but not yet verified, so its
  theorem endpoint remains **0%** until a focused check passes.  The subsequent
  geometric gate is suffix-relative endpoint-differential injectivity from
  minimality, followed by the positive-start local inverse and tail-action
  branch.

  The downstream initial-slice action work is further advanced:
  `lRampAct_fwd`, `redLen_ramp_bound`, and `redLen_ball_bound` are warning-free
  focused green and refreshed.  Starting from a genuine minimizing-ray witness
  with a concrete reduced-length bound, they splice to a measurable nonempty
  inverse-chart ball, give one explicit reduced-length upper bound on that
  ball, and prove its fixed-time Riemannian volume is positive.  They do not
  assume or prove the missing witness.  The finite compact chart-cover theorem
  `finite_chart_balls` is currently source-written in `ChartBallCover.lean`
  but not yet focused green.

  At the generic scalar layer, `le_of_upper_support` is warning-free focused
  green and refreshed.  It proves by continuous interval induction that a
  continuous function cannot cross a level if every point strictly above the
  level admits a strictly decreasing right upper support.  This is the exact
  scalar fencing step needed after evaluating a spacetime Calabi barrier at a
  spatial minimizer; it does not supply the geometric barrier itself.

  Honest endpoint accounting is unchanged where it matters:
  `redVolume_anti` **100%**, `redVolume_ball_le` **100%**,
  all-point spacetime weak barrier **0%**, `exists_redLen_le` **0%**,
  `redVolume_late_low` **0%**, and `smooth_nlc` **0%**.  Dedicated L-geometry
  including the open complete-flow and half-open-time endpoints is about
  **47--49%**; reused generic infrastructure for these checked bricks is
  **100%**; the whole P0--P9 infrastructure estimate remains **15--25%**.

- 2026-08-27 (verified positive-start continuation and finite chart balls):
  `lTailFamily_step_of`, `lTailFamily_step`, and `lTailFamily_extend` are now
  warning-free focused green and their `CalabiBranch` artifact is refreshed.
  Together with `exists_lTailFamily`, they put an arbitrary prescribed regular
  positive-start L-solution into one jointly smooth family parametrized by its
  actual initial velocity, and continue that family to any later point of the
  connected regular square-root-time interval.  The proof uses compact uniform
  phase existence plus open/closed continuation and regular-solution
  uniqueness; it does not assume endpoint injectivity or nonconjugacy.  The
  next exact Calabi producer is therefore the suffix-relative endpoint
  differential injectivity theorem from minimizing-curve index theory, followed
  by the local inverse/tail-action upper branch.  Those endpoint theorems remain
  **0%** until stated and checked.

  `finite_chart_balls` is also warning-free focused green and its named artifact
  is refreshed.  From a fixed smooth metric and one point witnessing
  nonemptiness, it produces a finite nonempty coordinate-ball cover with
  positive radii and one strictly positive `ENNReal` lower bound for every
  inverse-chart ball volume.  Combined with the already checked
  `redLen_ball_bound`, the remaining initial-slice bookkeeping is finite-order
  assembly of chart/action constants and the half-open square-root-time
  arithmetic.  This does not supply the missing minimizing point with
  `redLength <= finrank / 2`.

  The umbrella now imports both verified modules and its post-import focused
  check is warning-free green.  Honest endpoint
  accounting remains: `redVolume_anti` **100%**, `redVolume_ball_le` **100%**,
  all-point spacetime weak barrier **0%**, `exists_redLen_le` **0%**,
  `redVolume_late_low` **0%**, `smooth_nlc` **0%**, P2 **0%**, and the final
  Poincare endpoint **0%**.  Dedicated L-geometry including open L8--L9 is now
  about **48--50%**; reused generic infrastructure is **100%**; whole P0--P9
  infrastructure remains **15--25%**.

- 2026-08-27 (complete-flow spatial reduced-length minimum attained):
  `RedMinCompact.exists_redMin_rm` is warning-free focused green and its named
  artifact is refreshed.  On a connected complete flow with a uniform Riemann
  bound on one positive backward slab, it proves that
  `y |-> redLength S T x y tau` attains its spatial minimum.  The proof does
  not assume the desired minimum or ambient compactness: `lRmFree_subseq`
  removes the fixed-terminal-endpoint restriction from the existing
  action-bounded Arzela--Ascoli argument, and `lRmFree_lsc` feeds that limit
  through the native finite-chart weak lower-semicontinuity theorem.  A free-
  endpoint action minimizing sequence then selects the minimizing spatial
  endpoint; connectedness supplies nonempty fixed-endpoint competitor classes.

  Compactness of the full set of minimizing `(tau, y)` pairs on a fixed compact
  positive `tau` interval is not claimed.  Existing `lCost_lt_event` and
  `lCost_lt_param` provide strict-upper-bound stability, hence the wrong
  semicontinuity direction for closing that pair set.  The exact remaining
  producer is joint lower semicontinuity of `(tau, y) |-> lCost S T x y tau`,
  together with uniform compact localization for varying positive `tau`.
  Fixed-time attainment is **100%** and its dedicated machinery is **100%**;
  the all-point spacetime weak barrier and `exists_redLen_le` remain **0%**.
  Dedicated complete-flow L8 machinery is about **40--45%**, dedicated
  L-geometry including the open L8--L9 endpoints is about **49--51%**, reused
  generic infrastructure is **100%**, and whole P0--P9 infrastructure remains
  **15--25%**.

- 2026-08-27 (finite uniform splice assembly):
  `FiniteSpliceBound.redLen_cover_bound` is warning-free focused green and its
  named artifact is refreshed.  It takes the finitely many chartwise
  `redLen_ball_bound` constants and radii supplied by `finite_chart_balls`,
  forms finite suprema, and turns any one concrete minimizing-ray witness into
  a measurable target set with the fixed positive volume floor and one
  chart-independent explicit reduced-length bound.  It neither assumes the
  witness exists nor states a reduced-volume endpoint.

  The two-fixed-slice specialization is also warning-free focused green and its
  named artifact is refreshed.  `sqrt_gap_low` rationalizes a uniform positive
  lower bound for `sqrt (T-a0) - sqrt (T-a1)`, and `redLen_slice_bound` uses it
  to control the splice expression uniformly for terminal `T` in the half-open
  interval.  Both declarations are therefore **100%**.  The umbrella imports
  the verified finite-splice and fixed-slice modules; its post-import focused
  check is warning-free green together with the other new public modules.

  `SliceVolumeLow.redVolume_slice_low` is warning-free focused green and its
  named artifact is refreshed.  It applies `redVolume_set_low` to the fixed
  measurable set and constants from `redLen_slice_bound`, then compares the
  explicit density factor at `T-a0` with the one at `omega-a0`.  Thus one
  concrete low-reduced-length minimizing ray now gives a single strictly
  positive reduced-volume floor uniform in terminal `T`.  It does not assume
  that such a ray exists, and the umbrella now imports this verified module.

  `redVolume_late_low` itself remains **0%**.  Its dedicated late-floor
  machinery is about **55--60%**; the remaining real producer is still the
  concrete low-reduced-length minimizing ray from the all-point spacetime
  barrier, followed by the checked slice estimate and `redVolume_set_low`.
  Dedicated L-geometry across open L8--L9 is about **51--53%**, reused
  generic infrastructure is **100%**, and whole P0--P9 infrastructure remains
  **15--25%**.

- 2026-08-27 (relative Calabi/index continuation producers):
  `CalabiBranch.lTailLine_deriv`, `lTailLine_dstart`, `lTailLine_jacobi`, and
  `exists_lTail_germ` are warning-free focused green and refreshed.  They turn
  an affine actual-velocity parameter line into the endpoint differential's
  Jacobi field, identify its initial covariant derivative with the parameter
  direction, and provide a global smooth clamped representative on a compact
  tail.  The germ theorem deliberately changes the base curve away from the
  retained interval, so it is not misreported as a global test field along the
  original curve.

  `IndexNegativeLeft.exists_lSplit_left` and `lIndex_cross_neg` are likewise
  warning-free focused green and refreshed.  They are the left-relative mirror
  of the existing conjugate-point algebra: a zero-index suffix Jacobi field
  with nonzero initial derivative gives a negative cross term, and a small
  positive scale then gives a negative pair of broken index directions.

  `TailFamilySpan.lTailFamily_ext_of` and `lTailFamily_span` are warning-free
  focused green and refreshed.  The supplied-family continuation retains its
  original time domain while extending to another target; applying it twice
  yields one actual-velocity family whose connected open domain contains
  `0`, the positive start, and the terminal endpoint.  This is exactly what
  lets a time clamp preserve the original minimizing ray on the whole action
  interval.  The umbrella imports all three verified modules and is
  warning-free focused green after the additions.

  The next local API brick is smoothness of the affine-line variation field
  from local joint smoothness of the family; it belongs canonically in the
  generic Variation layer.  After that, the checked producers assemble the
  genuine suffix endpoint-differential injectivity contradiction and then the
  positive-start inverse/tail-action branch.  Endpoint injectivity, local
  inverse, all-point spacetime weak barrier, and `exists_redLen_le` remain
  **0% theorem endpoints**.  Dedicated L-geometry across open L8--L9 is about
  **52--54%**, reused generic infrastructure is **100%**, and whole P0--P9
  infrastructure remains **15--25%**.

- 2026-08-27 (positive-start endpoint and spatial Calabi support complete):
  `CompleteActionBound.lRegCosts_bdd_rm`,
  `CutMinimizerRm.lMinVec_min_rm`, `TailEndpoint.exists_lTail_inj`,
  `TailLocalBranch.lTail_localDiffeo`, and the three public
  `TailActionBranch` declarations are warning-free focused green.  Their
  exported artifacts needed by downstream modules are refreshed, and the
  umbrella is warning-free focused green after importing the full chain.

  The geometric content is now honest and noncompact.  A minimizing positive-
  start suffix has injective endpoint differential by the left-relative
  negative-index contradiction; the native local inverse then parametrizes
  nearby endpoints.  The actual fixed-tail action is smooth in that parameter,
  and `exists_lCost_support` adds the fixed minimizing head to obtain a smooth
  local upper support which exactly touches `lCost` at the minimizing endpoint.
  No ambient `CompactSpace`, caller-supplied `BddBelow`, desired inequality,
  frontier wrapper, or stronger consumer assumption was added.

  The next exact theorem is the **all-point spacetime weak upper-support
  inequality** for reduced length: combine the checked spatial Calabi branch
  with the time direction and the strict-domain Hamilton--Jacobi/Laplacian
  formulas so that the scalar fencing lemma can be applied at spatial
  minimizers.  Only after that theorem is checked should the lane state
  `exists_redLen_le`, then feed the already checked slice-volume floor into
  `redVolume_late_low`.

  Honest endpoint accounting: positive-start endpoint injectivity **100%**,
  native local diffeomorphism **100%**, and `exists_lCost_support` **100%**;
  all-point spacetime weak barrier **0%**, `exists_redLen_le` **0%**,
  `redVolume_late_low` **0%**, `smooth_nlc` **0%**, P2 **0%**, and the final
  Poincare endpoint **0%**.  Dedicated L-geometry across open L8--L9 is about
  **54--56%**, reused generic infrastructure is **100%**, and whole P0--P9
  infrastructure remains **15--25%**.

- 2026-08-27 (joint-time and positive-start trace brick):
  `TailLocalBranch.lTailTime_local` is warning-free focused green.  It applies
  the native manifold inverse-function theorem to `(A,r) |-> (alpha(A,r),r)`
  and obtains a genuine joint endpoint-time local inverse from only the
  fixed-terminal endpoint derivative injectivity.  `TailActionBranch` now also
  has warning-free focused-green `lTailAct_joint`, the exact Frechet derivative
  of `(A,r) |-> lRegAction(alpha A,a,r)`; the initial boundary vanishes from
  the fixed start, and the central Euler equation removes the interior term.
  Neither new export has been named-refreshed yet because their first joint
  downstream consumer is still being assembled.

  `AdaptedIndex.lIndex_smul_pt` is warning-free focused green and refreshed;
  it gives the full pointwise scalar-multiple index identity without comparing
  moving tangent fibers.  `AdaptedTrace.lIndex_trace_pos` is warning-free
  focused green and gives the exact trace for
  `W_i(s)=((s-a)/(b-a)) P_i(s)`.  Finally, `TraceIntegral.lKTail`,
  `lKTail_sq`, and `lTraceInt_pos` are warning-free focused green.  With
  `G(s)=s(s-a)^2 R(s)`, the checked weighted identity is

  ```text
  integral_a^b A(s) ds
    = -b R(b) - lKTail(a,b) / (2 (b-a)^2),
  ```

  where `A` is exactly the scalar trace density returned by
  `lIndex_trace_pos`.  Weighted-H integrability is derived internally; no
  Hamilton bound or desired inequality is assumed.  `lKTail_sq` has only
  `0 <= a <= b` and the raw-time weight
  `sqrt(rho) * (sqrt(rho)-a)^2`.

  The next exact theorem is `lTailJoint_mfd`: compose `lTailAct_joint` with
  `lTailTime_local` and eliminate the local-inverse differential to obtain the
  endpoint-time branch differential.  The subsequent exact sequence is
  `lTailBranch_hess`, `lTail_hess_le`, `lTail_lap_le`, `lTail_lap_K`, and the
  genuine limit producer `lKTail_tendsto`, before assembling
  `exists_redWeak_sup`.  This chain remains noncompact and needs no
  `CompactSpace` assumption.  After the weak barrier, `exists_redLen_le` still
  separately needs lower-semicontinuity/continuity of the spatial minimum value
  and a small-time initial bound; the existing strict upper stability alone is
  not that API.

  Honest endpoint accounting: `lTailTime_local`, `lTailAct_joint`,
  `lIndex_smul_pt`, `lIndex_trace_pos`, `lKTail_sq`, and `lTraceInt_pos` are
  each **100%** theorem endpoints.  The endpoint-time branch differential,
  tail Hessian/Laplacian, all-point spacetime weak barrier,
  `exists_redLen_le`, `redVolume_late_low`, `smooth_nlc`, P2, and the final
  Poincare endpoint remain **0%** until their own declarations verify.
  Dedicated L-geometry across open L8--L9 is about **56--58%**, reused generic
  infrastructure is **100%**, and whole P0--P9 infrastructure remains
  **15--25%**.

- 2026-08-27 (positive-start Hamilton-tail limit):
  `TraceIntegral.lKTail_tendsto` is warning-free focused green.  For a
  canonical regularized L-ray and a fixed positive terminal square-root time,
  it proves

  ```text
  lKTail(a,b) -> lK(b)  as a -> 0+.
  ```

  The proof uses no continuity or boundedness assumption on `lHamSq`.  It
  rewrites the moving lower limit as a fixed `[0,b]` integral with the
  indicator `a < s`, dominates by `|lHamSq|`, and uses the checked
  `lRayHam_int` L1 producer.  The endpoint `s=0` is excluded by the interval
  integral's `Ioc` support, while every fixed `s>0` eventually sees the weight
  `((s-a)/s)^2` converge to one.  No named artifact refresh was run because no
  downstream check currently requires this new export.

  Thus `lKTail_tendsto` and its dedicated limit machinery are each **100%**.
  The all-point spacetime weak barrier, `exists_redLen_le`,
  `redVolume_late_low`, `smooth_nlc`, P2, and the final Poincare endpoint
  remain **0% theorem endpoints**.  Dedicated L-geometry across the still-open
  L8--L9 endpoints remains about **56--58%**, reused generic infrastructure is
  **100%**, and whole P0--P9 infrastructure remains **15--25%**.

- 2026-08-27 (positive-start fixed-time tail Hessian):
  `TailHessian.lTailBranch_hess` is warning-free focused green.  For a jointly
  smooth positive-start family with fixed initial position, regular times,
  injective terminal endpoint differential, and the honest hypothesis that
  every nearby parameter curve satisfies the regularized L-Euler equation on
  `[a,b]`, it identifies the fixed-`b` branch Hessian with the terminal metric
  pairing against the covariant derivative of the induced parameter-variation
  L-Jacobi field.  The proof differentiates the actual tail action throughout
  a local endpoint neighborhood, cancels the endpoint inverse differential,
  identifies the gradient with terminal L-velocity, and uses intrinsic
  covariant-derivative commutation.  It adds no `CompactSpace`, desired
  inequality, frontier wrapper, class, `sorry`, or `admit`.

  `lTail_hess_le` remains unstated and therefore **0%**.  The current audit does
  not identify a same-base cutoff-extension blocker: `TailEndpoint.lean`
  already globalizes the full span `[0,b]`, transports the regularized
  L-curve data and full-ray minimizing property, and reaches
  `lIndex_sum_nonneg`.  The next comparison brick should therefore be stated in
  that honest full-span original-minimizer context, use `J`, `Q = W - J`,
  `lRegIndex_jacobi`, and the zero-head plus `Q`-tail index inequality, and must
  not assume tail minimality or index nonnegativity from the caller.

  Honest endpoint accounting: `lTailJoint_mfd` and `lTailBranch_hess` are each
  **100% theorem endpoints**; `lTail_hess_le`, the tail Laplacian formulas, the
  all-point spacetime weak barrier, `exists_redLen_le`, `redVolume_late_low`,
  `smooth_nlc`, P2, and the final Poincare endpoint remain **0%**.  Dedicated
  L-geometry across open L8--L9 is about **57--59%**, reused generic
  infrastructure is **100%**, and whole P0--P9 infrastructure remains
  **15--25%**.

- 2026-08-27 (positive-start tail Hessian comparison):
  `TailHessian.lTail_hess_le` is warning-free focused green.  It works in the
  honest full-span original-minimizer context: the original regularized
  L-curve and its raw fixed-endpoint minimizing property are retained on
  `[0,b]`, while the positive-start family supplies the local endpoint branch
  on `[a,b]`.  The comparison field is only `C^8` on an open neighborhood of
  `[0,b]`, with zero value at `a` and prescribed terminal value; no global
  smoothness, tail minimality, desired inequality, or caller-supplied index
  nonnegativity is assumed.

  The proof uses the affine-line field from `lTailLine_jacobi` and
  `lTailLine_deriv`, globalizes only its smooth base/field pair on the
  intersection of the family and comparison-field time domains, and composes
  the `C^8` comparison field with the same clamp.  It transfers the full-ray
  geometry and minimizing property germwise, applies `lIndex_sum_nonneg` to a
  zero head on `[0,a]` and the `W-J` tail on `[a,b]`, transfers that tail index
  by `lIndex_germ_congr`, and closes with `lRegIndex_jacobi`,
  `lIndex_sq_add`, and `lTailBranch_hess`.  No new cutoff or same-base
  extension API was needed.

  Honest endpoint accounting: `lTailJoint_mfd`, `lTailBranch_hess`, and
  `lTail_hess_le` are each **100% theorem endpoints**.  The tail Laplacian
  formulas, all-point spacetime weak barrier, `exists_redLen_le`,
  `redVolume_late_low`, `smooth_nlc`, P2, and the final Poincare endpoint
  remain **0%** until their own declarations verify.  Dedicated L-geometry
  across open L8--L9 is about **58--60%**, reused generic infrastructure is
  **100%**, and whole P0--P9 infrastructure remains **15--25%**.

- 2026-08-27 (positive-start tail Laplacian comparison):
  `TailLaplacian.lTail_lap_le` is warning-free focused green.  It keeps the
  exact full-span original-minimizer and positive-start family assumptions of
  `lTail_hess_le`, adds a terminal-orthonormal family `P`, and applies the
  Hessian theorem to the scaled fields

  ```text
  W_i(s) = ((s-a)/(b-a)) P_i(s).
  ```

  The proof obtains smoothness of the same actual tail-action branch from
  `lTailBranch_smooth`, rewrites its Laplacian as the metric trace of its
  Hessian using `lap_eq_hess_on`,
  `metricTracePair0SAt_eq_sum_basis`, and `hessTensorAt_apply`, applies
  `lTail_hess_le` in each terminal basis direction, and sums.  It assumes no
  adapted ODE and no index-density integrability.  No named refresh was run
  because no downstream module yet consumes this export.

  Honest endpoint accounting: `lTail_lap_le` and its dedicated raw traced-index
  machinery are **100%**.  The exact next theorem
  `HamiltonBound.lTail_lap_K`, the all-point spacetime weak barrier,
  `exists_redLen_le`, `redVolume_late_low`, `smooth_nlc`, P2, and the final
  Poincare endpoint remain **0%** until their own declarations verify.
  Dedicated L-geometry across open L8--L9 is about **59--61%**, reused generic
  infrastructure is **100%**, and whole P0--P9 infrastructure remains
  **15--25%**.

- 2026-08-27 (positive-start Hamilton-tail Laplacian bound):
  `HamiltonBound.lTail_lap_K` is warning-free focused green.  It consumes the
  exact full-span minimizing-ray and positive-start family prefix of
  `lTail_lap_le`, together with a terminal-orthonormal adapted family which is
  only `C^8` near `[0,b]`, and proves the raw tail-branch inequality

  ```text
  Delta branch(alpha(A0,b))
    <= n/(b-a) - 2*b*R(alpha(A0,b))
         - lKTail(alpha(A0,-),a,b)/(b-a)^2.
  ```

  The proof derives the index-density and Ricci-density integrability inputs
  internally, transfers the family center to the canonical `lRegCurve` with
  existing germ congruence APIs, applies `lIndex_trace_pos` and
  `lTraceInt_pos`, and closes the raw comparison from `lTail_lap_le`.  Tangent
  fields are transferred through their model-space values rather than by
  unfolding a moving bundle or Hom object.  No `CompactSpace`, caller
  Hamilton-integrability, scalar sign, desired inequality, frontier wrapper,
  `sorry`, or `admit` was added.  No named refresh was run because no real
  downstream source currently imports the new declaration.

  The exact next small theorem is `lTailInv_slice`: local inverse uniqueness
  should identify the spatial component of `lTailTime_local`'s joint inverse
  with `lTail_localDiffeo`'s fixed-`b` inverse near the central endpoint.  This
  compatibility lets one support function consume both `lTailJoint_mfd` and
  `lTail_lap_K`; it must be proved rather than assumed as a new equality.

  Honest endpoint accounting: `lTail_lap_K` and its dedicated Hamilton-tail
  assembly are **100%**.  The all-point spacetime weak upper support,
  `exists_redLen_le`, `redVolume_late_low`, `smooth_nlc`, P2, the capstone
  `redVolume_anti`, and the final Poincare endpoint remain **0% theorem
  endpoints**.  Dedicated L-geometry across open L8--L9 is about **60--62%**,
  reused generic infrastructure is **100%**, and whole P0--P9 infrastructure
  remains **15--25%**.

- 2026-08-27 (half-open late floor and arbitrary-tail ball bound):
  `RedMinTime.redMinAct_lip`, `redMinVal_cont`,
  `RedLengthFence.exists_redLen_le`, and
  `LateVolumeLow.redVolume_late_low` are warning-free focused green and
  named-refreshed. The last theorem gives one `v0 > 0` for every
  `a <= T < omega`, basepoint, and `0 < tau <= T - a0`, assuming only
  `a0 < a < omega` and regularity of `Ico a0 omega`.

  `NLCBallUpper.redVolume_ball_eta` is also warning-free focused green and
  refreshed. It replaces the former hard-coded Gaussian tail `1/4` by an
  arbitrary prescribed positive `eta`; `redVolume_ball_le` remains its
  compatibility specialization. The updated umbrella is warning-free green.

  The exact next theorem remains `smooth_nlc`, still **0%** because it is not
  stated or proved. Its lowest missing producer is now precisely
  `shiRm1_ball`: a scale-invariant first-Rm-derivative bound on a strictly
  smaller cylinder inside an Rm-controlled parabolic ball. Its immediate
  adapter `lGrad_ball` supplies the scalar-gradient bound with later-half-time
  and half-radius losses, then feeds `lRegSpeed_unif`, `lMetric_ball`,
  `lRegRange_unif`, `lExp_ball_unif`, and `redVolume_ball_unif`. Every checked
  Shi producer instead assumes whole-manifold curvature control and concludes
  on `Set.univ`; restriction/pullback only transport an existing bound. A
  finite cover of `[a, omega)` is invalid, so this is a substantial spatial
  cutoff/local-maximum-principle API frontier rather than an elaboration issue.

  Honest accounting: `redVolume_anti`, `exists_redWeak_sup`,
  `exists_redLen_le`, `redVolume_late_low`, and `redVolume_ball_eta` are each
  **100%** and pass the P2 standard-axiom audit; `smooth_nlc`, P2, and final Poincare remain **0% theorem
  endpoints**. Dedicated L8--L9 machinery is about **76--78%**, reused generic
  infrastructure is **100%**, and whole P0--P9 remains **15--25%**.
