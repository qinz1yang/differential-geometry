# StepCCenterOfMass.lean — MSM135 Ch4 §6 Step C (center of mass / nonlinear averages)

## Implementation update (2026-07-13, selected inverse-vector equation)

`centerOfMass.invB_eqn` is implemented, focused-green, and sorry-free. It is
the weakest generic center-layer consumer: given differentiability of every
half-squared-distance summand and identities `grad_i = -v_i` for an arbitrary
tangent family at the selected center, it proves `sum mu_i • v_i = 0`.

The theorem reuses the checked global minimizer, `centerEnergy_diff`, and
`CenterOfMass.sum_grad_eq_zero`. It does not depend on `DiagInvBranch`,
`normalChartAt`, `eqnRadius`, or any radius hypothesis; the B1 consumer supplies
the selected inverse tangent family. This theorem is 100% complete. The
branch-native Gate 5 readout is completed separately in `StepCCmDomain.lean`.
The independent Hessian/Neumann producer remains open and is not implied by
this first-order equation.

Plan note (2026-06-22). Lean file not yet created — this records the **verified feasibility**,
decomposition, available infrastructure, and honest-input boundary, so C1 can be built cleanly.

## Goal

Step C (§6, book L2092–end): the center-of-mass averaging that turns the local maps
`F_{kℓ,β}^α → id` (lbl399, B-track) into the single averaged approximate isometry `F_{kℓ;r}`
(lbl397 = B1). Feeds B1 and Step D. Book results:
- **C1 = lbl429** (Existence of center of mass): for `q₁,…,qₖ ∈ B(p,r)`, `r < min{inj/3, π/(6√K)}`,
  weights `μᵢ ≥ 0`, `Σμᵢ > 0`, the energy `φ(q) = ½ Σ μᵢ d²(q,qᵢ)` has a UNIQUE minimizer
  `cm{q₁,…,qₖ} ∈ B(p,2r)`; and `cm → q*` as `qᵢ → q*` uniformly in weights.
- gradient: `grad φ(q) = -Σ μᵢ exp_q⁻¹ qᵢ`; minimizer ⟺ `Σ μᵢ exp_q⁻¹ qᵢ = 0`.
- **C2 = lbl430** (Dependence of cm on weights/points): smoothness of `cm` (IFT on `grad φ = 0`).
- **C3 = lbl434** (averaging maps): partition of unity `φ_k^α` + `cm` ⟹ the averaged map.
- **C4 = lbl436**: average of (`→ id`) maps `→ id`. ⟸ lbl399-`C∞` (COMPCONV brick).

## Feasibility: VERIFIED (2026-06-22). The geometry C1 needs is already built, sorry-free.

- **Properness / closed-ball compactness** (for existence of the minimizer): DONE, sorry-free —
  `Comparison/HopfRinowProper.lean`: `expImgClosedBall_compact`, `properSpace_riemMetric`,
  `riemMetricSpace`/`riemMetric_dist_eq`/`riemMetric_realizes`, `intermediateDist_riemMetric`.
  Rests on the **unconditional** intrinsic Hopf–Rinow `MinimizingGeodesic.lean:
  hopf_rinow_expMapIntrinsic_surjective_minimizing` (0 sorry). NOTE: this is ALSO what already
  discharged `GoodCoveringOrdered.exists_proper_realization` (sorry-free) — the Step-A Hopf–Rinow
  black box is CLOSED. (`Comparison/HopfRinow.lean`'s 4 sorries are a separate off-critical-path
  file, not consumed by the properness chain.)
- **Geodesic convexity of small balls** (`lbl417`): DONE-as-assembly —
  `Comparison/ConvexBalls.lean:isConvexWith_smallNormalBall`, taking the `lbl416` input
  ("d² convex along joining curves", from the `lbl413` Hessian comparison). `GeodesicConvexity.lean`:
  `IsGeodesicallyConvexWith`, `smallNormalBall`.
- **Distance / exp / exp⁻¹**: `riemannianEDist` (+ `riemMetric_dist_eq` real form),
  `Comparison/NormalCoordinates.normalChartAt` (= exp⁻¹), `expMapDiffeo`.
- **Gradient of d²** (`lbl411`): `grad(½d²(·,x)) = -exp_·⁻¹ x` — provable from the done
  Hopf–Rinow minimizing geodesics + Gauss lemma; not yet a named lemma (add it).

## Honest-input boundary for Step C (small — matches the plan's existing boundary)

ONLY the **strict convexity / Hessian positivity of the `d²` function** (`lbl416`, from the
`lbl413` Hessian comparison) — needed for uniqueness of the minimizer and the IFT smoothness.
The set-level convexity assembly (`lbl417`) already consumes it. Everything else (existence,
gradient characterization, the averaging construction) is provable.

## C1 proof route (the first brick to build)

1. **Existence**: `φ` is continuous; outside `B(p,2r)` we have `φ(q) > φ(p)` (book L2679), so a
   minimizer lies in the compact closed ball `closedBall p 2r` (from `properSpace_riemMetric` /
   `expImgClosedBall_compact`); extract via `IsCompact.exists_isMinOn`.
2. **Uniqueness**: `φ` is strictly convex on `B(p,2r)` — each `½d²(·,qᵢ)` strictly convex there
   (`lbl416` honest input, since `B(p,2r) ⊆ B(qᵢ,3r) ⊆ B(qᵢ,π/(2√K))`), `μᵢ ≥ 0`, `Σμᵢ > 0` ⟹
   `φ` strictly convex ⟹ unique minimizer. Reuse the convexity API in `ConvexBalls`/`GeodesicConvexity`.
3. **`cm ∈ B(p,2r)`** and **gradient characterization** `Σ μᵢ exp_cm⁻¹ qᵢ = 0` (from `lbl411`).
4. **Continuity** (`cm → q*`): apply the existence/uniqueness to shrinking balls `B(q*, r*)`.

## Dependency on the other parallel tracks

- C1–C3 are **independent** of COMPCONV (the Faà-di-Bruno composition-convergence brick) and of
  the (now-done) Hopf–Rinow handoff. Build them now.
- Only **C4** (`average of →id maps → id`, lbl436) consumes lbl399-`C∞` (the COMPCONV output).
- C1's existence uses the **done** properness; its uniqueness uses the `lbl416` convexity honest input.

## File placement

The center-of-mass theory is GENERAL Riemannian geometry (Karcher mean) → canonical home is
`Geometry/Comparison/CenterOfMass.lean` (next to `ConvexBalls`/`HopfRinowProper`, reusable).
The HCG-specific averaging maps (C3/C4, partition of unity over the Step-A cover) stay in
`C4/StepC*.lean`. (If kept all in `C4/` initially, mark the general part promotion-candidate to
`Comparison/`, like the `MapConvergence` engines.)

## Implementation update (2026-06-23)

General C1 infrastructure now lives in `DifferentialGeometry/Geometry/Comparison/CenterOfMass.lean`.

Done:

- finite weighted metric energy and the outside-`2r` estimate;
- Riemannian `centerEnergy` for an explicit smooth metric;
- continuity of `centerEnergy`;
- compact and closed-ball minimizer existence via the Hopf--Rinow proper metric;
- global minimizer existence in the closed `2r` ball;
- conditional uniqueness from midpoint-strict convexity of the weighted energy;
- finite-sum strict-convexity assembly in the natural input shape: if every
  `1/2 d^2(.,q_i)` summand satisfies midpoint strict Jensen on the closed
  `2r` ball, then the weighted center energy has a unique global minimizer;
- the native along-curve strict-convexity consumer: if every summand is
  `StrictConvexOn ℝ unitInterval` along the chosen joining curves, then the
  same unique global minimizer follows;
- finite weighted-sum gradient algebra in `Geometry/Operator/Operators.lean`,
  ready to consume the still-missing one-summand `grad(1/2 d^2)` theorem.

What changed in the feasibility assessment:

- The existence half of C1 is no longer just feasible; it is proved.
- The uniqueness argument itself is proved as an assembly lemma, including the
  bridge from the native along-curve `StrictConvexOn ℝ unitInterval` shape to
  the midpoint Jensen package. The strict along-curve producer for each
  `1/2 d^2` summand is still missing. The current `ConvexBalls.lean` API gives
  set convexity from a non-strict along-curve `ConvexOn` input; it does not
  produce the strict/strong convexity needed for uniqueness or the
  nondegenerate Hessian needed for C2.
- The gradient characterization is reduced to one named theorem for the
  gradient of `1/2 d(q,x)^2`; the finite weighted-sum gradient algebra is done.

Verification status: the focused Lean check and targeted module build for
`CenterOfMass.lean` passed, as did the focused check and targeted module build
for the new `Operators.lean` gradient finite-sum lemmas. Axiom print for the
new public endpoints is `[propext, Classical.choice, Quot.sound]`; no
`sorryAx` is introduced by these declarations. The targeted builds replayed
existing upstream warnings outside the edited declarations.

## Implementation update (2026-06-24)

The finite-gradient assembly was added to the general file
`DifferentialGeometry/Geometry/Comparison/CenterOfMass.lean`.

Done now:

- `grad_centerEnergy`: the gradient of the finite weighted center energy is the
  weighted sum of the one-point `halfSqDist` gradients.
- `sum_grad_eq_zero`: at a differentiable global minimizer, that weighted sum
  of one-point gradients is zero.
- `sum_expInv_eq_zero`: the conditional book equation
  `sum_i mu_i * exp_q^{-1}(q_i) = 0`, assuming the one-summand formula
  `gradientFun g (halfSqDist q_i) q = - normalChartAt g q q_i`.
- `grad_halfSqDist_of_flat` and `sum_expInv_of_flat`: the sharper covector-form
  consumer. Once first variation gives
  `(mfderiv (halfSqDist q_i) q).toLinearMap =
    metricFlatEquiv g q (-(normalChartAt g q q_i))`,
  the pointwise gradient formula and the weighted book equation follow.
- `metricEnergy_min_dist_le`: the metric core of the book's continuity clause.
  If all input points satisfy `dist qstar q_i <= epsilon`, then any global
  minimizer of the weighted metric energy satisfies
  `dist q qstar <= 2 * epsilon`, uniformly in the nonnegative weights as long
  as some weight is positive.
- `centerEnergy_min_dist_le`: the Riemannian version, obtained by rewriting
  through `centerEnergy_eq_dist` in the Hopf--Rinow metric realization.
- `exists_global_min_dist_le` and `exists_unique_min_dist_le`: the C1
  existence/strict-convexity uniqueness packages now return minimizers together
  with the same `2epsilon` stability bound.
- `exists_unique_jensen_dist_le` and `exists_unique_curve_dist_le`: the
  per-summand Jensen and along-curve C1 entrypoints also return the stability
  bound, so the book continuity clause is packaged at the same abstraction
  level as the current uniqueness assumptions.
- `gradientFun_eq_zero_of_isLocalMin` was placed in
  `Geometry/Operator/Operators.lean` so Step C can use the first-order
  minimizer fact without importing the Laplacian minimum-principle layer.

Honest remaining frontiers:

- The book formula
  `grad (1/2 d(., pt)^2) = - exp_q^{-1}(pt)` is still not available as a named
  theorem, and the algebraic part has now been reduced to the covector
  first-variation identity
  `(mfderiv (halfSqDist pt) q).toLinearMap =
    metricFlatEquiv g q (-(normalChartAt g q pt))`.
  That is the exact missing one-summand bridge needed to turn
  `sum_expInv_of_flat` into an unconditional book center-of-mass equation.
  Fixed-center normal-chart smoothness does not supply it; the missing content
  is first-variation control of the moving-base inverse exponential
  `q |-> normalChartAt g q pt`.
- The strict Hessian/strict along-geodesic convexity producer for the summands
  remains the C1 uniqueness/C2 nondegeneracy input. The current C1 uniqueness
  theorem consumes it cleanly but does not prove it.
- The convergence of centers as all points approach `qstar` is now available
  for any chosen global minimizer, and it has been packaged with the C1
  existence/uniqueness consumers. Packaging it as continuity of the actual `cm`
  function still depends on uniqueness/canonical choice, so the remaining
  blocker is the strict convexity/nondegeneracy producer, not another compactness
  or Arzela-Ascoli argument.
- C2 smooth dependence and C3 averaging are not started as Lean endpoints in
  this pass; they should wait for the one-summand gradient theorem and the
  strict Hessian/nondegeneracy producer.

Verification status: focused checks passed for the edited Lean files, and the
`CenterOfMass` targeted module refresh completed with a current olean. Axiom
print for `gradientFun_eq_zero_of_isLocalMin`, `grad_centerEnergy`,
`sum_grad_eq_zero`, `sum_expInv_eq_zero`, `gradientFun_eq_of_flat`,
`grad_halfSqDist_of_flat`, `sum_expInv_of_flat`, `metricEnergy_min_dist_le`,
`centerEnergy_min_dist_le`, `exists_global_min_dist_le`, and
`exists_unique_min_dist_le`, `exists_unique_jensen_dist_le`, and
`exists_unique_curve_dist_le` is `[propext, Classical.choice, Quot.sound]`; no
`sorryAx` is introduced by these declarations.

## Implementation update (2026-06-24, first-variation producer)

The `lbl411` plan was re-audited against the live variation/Gauss APIs.

What landed:

- `Variation.first_variation_geodesic_fixed_end` in
  `Geometry/Comparison/Variation/FirstVariation.lean`: for a unit-speed
  geodesic and a smooth variation with fixed final endpoint, the derivative of
  arc length is the negative initial boundary term. This is the moving-start
  first-variation producer needed for the distance-gradient theorem.

What changed in the feasibility assessment:

- The statement `grad (1/2 d(., pt)^2) = - exp_q^{-1}(pt)` is still feasible,
  but it is not a direct corollary of the fixed-base Gauss/radial-distance API
  currently exposed. The new first-variation lemma handles the analytic
  boundary term; the remaining missing bridge is the moving-base local
  minimizing-geodesic family: construct a smooth family of geodesics from a
  moving base curve to fixed `pt`, prove its arc length equals the local
  distance, and identify the initial unit velocity with the normalized
  `normalChartAt g q pt` vector.
- Existing public radial-distance theorems in the Gauss/minimizing-geodesic
  layer are fixed-center statements. They identify distance from a fixed center
  to radial exponential images, but do not by themselves differentiate the
  moving-base function `q |-> dist q pt`.
- C2 smooth dependence and C3 averaging remain deferred until this one-summand
  gradient theorem and the strict Hessian/nondegeneracy producer are available.

Verification status: the new first-variation theorem passed focused checking,
targeted module refresh, and an axiom print with `[propext, Classical.choice,
Quot.sound]`; no `sorryAx`.

Additional Step C progress in the variation layer:

- `Variation.dist_deriv_of_length`: differentiates the distance from a moving
  initial endpoint to the fixed final endpoint once a local
  length-equals-distance hypothesis is supplied for the fixed-endpoint geodesic
  variation.
- `Variation.halfSq_deriv_length`: differentiates `1/2 * d^2` in the same
  setup.

These are verified producer adapters toward `lbl411`, but not the full
`lbl411` theorem. The remaining bridge is still geometric: construct the local
smooth family of length-minimizing geodesics for a moving base curve, identify
its initial velocity with the inverse-exponential vector, and package the
curve-derivative result as the manifold `mfderiv` covector formula consumed by
`CenterOfMass.sum_expInv_of_flat`.

Audit of the existing exponential-variation layer: `ExpVariationSmooth.lean`
already proves joint smoothness for intrinsic exponential variations from a
smooth base curve and smooth tangent-bundle launch field. Therefore the next
missing theorem is not "make the variation smooth" in general; it is the local
smooth moving-base inverse-exponential section
`s |-> exp_{beta s}^{-1}(pt)`, together with endpoint, local minimizing, and
distance-equals-length facts for the corresponding geodesic family.

## Implementation update (2026-06-24, CenterOfMass first-variation adapter)

Added the CenterOfMass-facing adapter
`CenterOfMass.halfSqDist_deriv_of_lengthVariation`.

It consumes `Variation.halfSq_deriv_length` and rewrites the derivative into
the one-point energy summand `s |-> halfSqDist pt (beta s)`, assuming the
supplied fixed-end geodesic variation locally realizes distance by arc length.
This is a genuine Step C interface brick: the lower variation calculation now
talks directly to `centerEnergy`'s summands.

What remains unchanged:

- This is not the full `lbl411` gradient theorem. The moving-base
  inverse-exponential section still has to be constructed and converted from a
  curve derivative into the `mfderiv` covector identity consumed by
  `CenterOfMass.grad_halfSqDist_of_flat`.
- The strict Hessian/strict convexity producer remains the separate C1
  uniqueness and C2 nondegeneracy frontier.

Verification status: the focused Lean check passed, and an axiom probe for the
new theorem reported `[propext, Classical.choice, Quot.sound]`. The targeted
module build was interrupted by a tool timeout and left a stale Lake lock, which
was cleared after confirming the recorded PID was dead and the build workers had
exited.

## Implementation update (2026-06-24, moving-start variation constructor)

Added the variation-layer constructor needed by the next `lbl411` step:

- `Variation.exists_expVar_field`: from a smooth base curve and bundle-smooth
  launch field, constructs a smooth intrinsic-exponential variation realizing
  that field along the central curve. Endpoint fixing is conditional on the
  field vanishing at that endpoint.
- `Variation.exists_expVar_fixEnd`: the direct moving-start/fixed-final form.
  If `V L = 0`, the constructed variation fixes the final endpoint while the
  initial endpoint is allowed to move.
- The old endpoint-fixed theorem
  `Variation.exists_variation_realising_field_via_exp` is preserved as a
  wrapper, so second-variation consumers do not change.

Impact on Step C:

- The smoothness/existence of the fixed-final variation is no longer the
  missing theorem once a smooth launch field is supplied.
- The remaining `lbl411` producer is now sharper: build the local smooth
  moving-base inverse-exponential launch field for a fixed target `pt`, prove
  its endpoint equation, and prove local distance-equals-length for the
  resulting variation. After that, `CenterOfMass.halfSqDist_deriv_of_lengthVariation`
  can feed the covector identity needed by `grad_halfSqDist_of_flat`.

Verification status: focused check and targeted module build passed for
`SecondVariationMinimiser.lean`. Axiom prints for `exists_expVar_field`,
`exists_expVar_fixEnd`, and the preserved endpoint-fixed wrapper are
`[propext, Classical.choice, Quot.sound]`; no new `sorryAx`.

Post-audit of the next `lbl411` frontier:

- Fixed-base inverse-function infrastructure exists:
  `Geometry/Exponential/LocalDiffeomorphism.lean` proves the exponential map at
  a fixed base point is a local diffeomorphism near `0`, and the Step B input
  layer has fixed-base `normalChartAt` `C^\infty` smoothness on the normal
  ball.
- These are still fixed-base statements. They do not produce a smooth field
  along a moving base curve `beta`,
  `s |-> exp_{beta s}^{-1}(pt)`, nor a smooth local inverse for the diagonal
  map `(p, v) |-> (p, exp_p v)`.

Exact remaining theorem frontier:

```text
diagonal_exp_local_diffeomorphism:
  the map on the tangent bundle sending (p, v) to (p, exp_p v)
  is a local C^infty diffeomorphism near (q, exp_q^{-1}(pt)),
  with inverse giving the moving-base inverse-exponential section.
```

Once this theorem (or an equivalent moving-base inverse section) is available,
the route is now short: feed the section to `exists_expVar_fixEnd`, prove the
endpoint and local distance-equals-length facts, then consume
`CenterOfMass.halfSqDist_deriv_of_lengthVariation` to obtain the one-summand
covector identity.

## Implementation update (2026-06-24, field-level derivative reduction)

Added `Variation.exists_sqDeriv_field`.

It composes:

- `Variation.exists_expVar_fixEnd`, which constructs the moving-start,
  fixed-final smooth variation from a smooth launch field `V` with `V L = 0`;
- `Variation.halfSq_deriv_length`, which differentiates `1/2 * d^2` once the
  constructed variation locally realizes distance by arc length.

The conclusion rewrites the initial variation vector to the supplied field
value `V 0`, so the remaining one-summand gradient proof can work directly with
the launch field supplied by the future moving-base inverse exponential.

What remains:

- construct the correct local smooth launch field
  `s |-> exp_{beta s}^{-1}(pt)`;
- prove the endpoint equation and local distance-equals-length for the
  corresponding geodesic family;
- package the resulting curve derivative as the manifold `mfderiv` covector
  identity consumed by `CenterOfMass.grad_halfSqDist_of_flat`.

Verification status: focused check, targeted module build, and axiom print
passed for `exists_sqDeriv_field`; no new `sorryAx`.

## Implementation update (2026-06-24, diagonal exponential target)

Added the small exponential-layer object for the moving-base inverse frontier:

- `Exponential.diagExp`: the total-space map
  `u |-> (u.proj, expMapIntrinsic g hEnorm u.proj u.snd)`.
- `diagExp_apply`, `diagExp_fst`, and `diagExp_snd`: projection/simp facts for
  consumers.
- `diagExp_variation_contMDiffAt_of_smallField`: along a smooth base curve and
  smooth launch field, `(s,t) |-> diagExp <gamma t, s * V0 t>` is smooth into
  `M x M` for sufficiently small variation parameter.

This does not prove the moving-base inverse theorem. It makes the next
frontier precise in Lean terms: prove a local diffeomorphism/local inverse for
`diagExp` near `(q, exp_q^{-1}(pt))`, then use that inverse to build the smooth
launch field required by `Variation.exists_sqDeriv_field`.

Audit of the fixed-base IFT route shows the smallest missing producer for that
next frontier: a total-space chart theorem proving `diagExp` is `ContDiffAt` in
tangent-bundle/product charts, plus the derivative identification at the zero
section `(delta_p, delta_v) |-> (delta_p, delta_p + delta_v)`. The existing
variation theorem only gives smoothness after precomposing with a smooth
two-parameter launch field; it does not provide the total-space derivative
needed by the Banach inverse function theorem.

The endpoint-at-zero identity for `diagExp` is intentionally deferred to a
downstream layer that already imports the metric/Hopf-Rinow side
`expMapIntrinsic_zero`; importing that metric-geometric theorem into
`ExpVariationSmooth.lean` would put the dependency in the wrong direction.

Verification status: focused Lean check passed for the exponential-layer edit.

## Implementation update (2026-06-30, C4 wrapper layer)

Added the first C4 Step-C wrapper file:
`DifferentialGeometry/Geometry/Flow/RicciFlow/HCGCompactness/C4/StepCCenterOfMass.lean`.

Implemented:

- `CenterInput`, bundling the routine C1 hypotheses plus `StrictDistInput`;
- `CenterInput.exists_cm`;
- `centerOfMass`;
- `centerOfMass.mem`, `centerOfMass.min`, `centerOfMass.unique`;
- `centerOfMass.dist_le`, using the `2 epsilon` stability package;
- `centerOfMass.expInv_eqn`, the conditional book-form equation for the chosen
  center.

The strict Hessian/strict-convexity input lives in the new
`StepCInputs.lean` as `StrictDistInput`. It is intentionally shaped exactly
like the hypotheses consumed by `CenterOfMass.exists_unique_curve*`.

The equation remains conditional on differentiability of the center energy,
differentiability of the summands, and the one-summand gradient identity at the
selected center. This is intentional: `HalfSqDistGradMain.lean` proves the
first-variation identity under source/smallness/non-self hypotheses, but Step C
still needs a radius/source/smoothness producer to discharge those hypotheses
for every active summand.

Verification status: focused checks and the targeted module build passed. Axiom
prints for the new public endpoints reported `[propext, Classical.choice,
Quot.sound]`.

Implementation traps:

- The wrapper must open `DifferentialGeometry.Integral.Connection` to see
  `gradientFun`.
- `CenterOfMass.sum_expInv_eq_zero` is currently indexed by `κ : Type`, so this
  C4 wrapper also uses `ι : Type`, not an arbitrary universe-polymorphic index.

## Implementation update (2026-06-30, local equation bridge)

Added two more C1 equation-routing lemmas to `StepCCenterOfMass.lean`:

- `centerOfMass.grad_half_self`: the self-summand formula
  `grad (1/2 d(.,q)^2) q = -normalChartAt g q q`, proved by local minimality
  and `normalChartAt_centre`.
- `centerOfMass.centerEnergy_diff`: differentiability of the finite center
  energy follows from differentiability of all half-squared-distance summands.
- `centerOfMass.expInv_eqn_local`: an `exists rho > 0` bridge that discharges
  the raw one-summand gradient hypothesis in `centerOfMass.expInv_eqn`.
  Non-self summands use `HalfSqDistGradMain.grad_halfSqDist`; self summands use
  `grad_half_self`. This theorem now derives center-energy differentiability
  from the summand differentiability, so it no longer carries an `hdiffEnergy`
  hypothesis.

The theorem still deliberately requires the concrete Step-C radius/source and
differentiability inputs:

- each active summand lies in the normal-coordinate source at the chosen center;
- non-self summands are small relative to the produced local radius;
- all summands are differentiable at the chosen center.

Thus the remaining producer layer is now sharper: prove those source,
smallness, and differentiability facts for the concrete Step-C averaging
configuration, rather than carrying an opaque `hgrad` assumption.

Verification status: focused Lean check passed.

Follow-up verification status: the current `StepCCenterOfMass` module targeted
build passed, and a local scan of `StepCCenterOfMass.lean`/`StepCInputs.lean`
found no `sorry` or `admit`.  Axiom probes for `CenterInput.exists_cm` and
`centerOfMass.expInv_eqn_local` report only the usual project axioms.

## Implementation update (2026-07-03, C2 = lbl430 IFT core landed)

New file `C4/StepCSmoothness.lean`. `cmSolution_hasStrictFDerivAt` (green, `lake build`,
axiom-clean `[propext, Classical.choice, Quot.sound]`): the Banach-IFT extraction half of
lbl430(i). From an `ImplicitFunctionData 𝕜 (Ey × P) F P` for the "solve `G(y,params)=0` for
`y`" equation (leftFun = the E-valued chart-coordinate cm equation `Σ μᵢ exp_y⁻¹ qᵢ`,
rightFun = param projection), the parameter → center map
`params ↦ (implicitFunction (leftFun pt) params).1` (y-component = cm) is `HasStrictFDerivAt`
(C¹). Proof = `ContinuousLinearMap.fst.comp` of Mathlib
`ImplicitFunctionData.hasStrictFDerivAt_implicitFunction_fderiv`.

**Survey findings that shaped this (a9dacd23…):**
- Joint smoothness `(y,q) ↦ exp_y⁻¹ q` is **AVAILABLE**: `Exponential.diagExpInv` +
  `diagExpInv_contMDiffAt` (`ContMDiffAt (I.prod I) I.tangent 1 … (p,p)`) in
  `DiagExpDerivative.lean`; plus `diagExp_hasFDerivAt_zero_unipotent` (zero-section derivative
  `(z₁,z₂)↦(z₁,z₁+z₂)` = `unipotentCLE`).
- Mathlib IFT = `ImplicitFunctionData` (solve-for-y form), NOT the surjective
  `HasStrictFDerivAt.implicitFunction` (kernel/level-set form).
- **`StrictDistInput` has NO Hessian/invertibility field** — only qualitative strict convexity.
- `∂_y G ≈ -(Σμᵢ)id` (Hessian of ½d²) is **NOT formalized** (only first-variation
  `grad_halfSqDist`/`halfSqDist_flat`).

**Remaining C2 frontier (the concrete `ImplicitFunctionData` PRODUCER — multi-session):**
1. Assemble chart-level `HasStrictFDerivAt` of `G = Σ μᵢ (chart of exp_y⁻¹ qᵢ)` from
   `diagExpInv` (moving-base tangent space; `TangentSpace` defeq trap — fderiv of E→E maps, not
   the mfderiv composite) + linearity in μ. **Long pole.**
2. `∂_y G` invertibility — the `lbl413`-family Hessian input, pre-approved to add (extend
   `StrictDistInput` or a sibling `CmHessianInput`: the y-slice derivative of the chart equation
   is invertible, `≈ -(Σμᵢ)id`).
3. Build `ImplicitFunctionData` (leftFun=G, rightFun=param-proj; `range_leftDeriv`/`isCompl_ker`
   from invertibility) → `cmSolution_hasStrictFDerivAt` → connect to `centerOfMass` by
   uniqueness. C^p (all-order) route = the `ContDiff` IFT (`ImplicitContDiff.lean`); C¹ here
   suffices for B1.

This session delivered the IFT CONSUMER half (verified). The concrete producer (steps 1–3),
with step 1 the long pole, is the remaining lbl430 work.

## Implementation update (2026-07-10, named center-equation radius)

- Added `centerOfMass.eqnRadius` and `eqnRadius_pos`, a canonical positive
  choice of the radius formerly returned only existentially by
  `expInv_eqn_local`.
- `grad_eq_of_lt` exposes the corresponding one-summand gradient identity, and
  `expInv_eqn_of_lt` proves the selected center's inverse-exponential sum is zero
  from differentiability, moving normal-source membership, and the named
  smallness inequality.
- Downstream code can now state concrete configuration containment against a
  named radius instead of assuming the center equation under a new name.
- Focused verification and the targeted module build passed. The remaining
  work is to place the finite-hat configurations inside this radius; the root
  equation itself is no longer opaque.
