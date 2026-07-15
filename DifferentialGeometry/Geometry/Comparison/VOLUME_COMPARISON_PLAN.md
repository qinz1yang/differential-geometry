# VOLUME COMPARISON PLAN (Poincaré program P1a — first new lane)

Written 2026-07-05, after the asset audit below.  Goal chain: capped-scale
volume comparability → Bishop–Gromov relative monotonicity → Cheeger–Gromov–
Taylor injectivity decay.  Direct customers: the HCG honest inputs
(`VolumeComparisonInput`, `PackingBound`, later `InjRadiusDecayInput` — see
`…/HCGCompactness/PROJECT_MAP.md` §4), then `POINCARE_PLAN.md` P2/P3.

## 0. Asset audit (2026-07-05) — what exists, all verified 0-sorry

**Measure/integration layer** (`Analysis/Integration/`, whole tree 0-sorry):
`riemannianVolumeMeasure` = POU sum of chart-local measures with density
`chartDensity = √det (chart Gram matrix)`; atlas-independence
(`riemannianMeasure_independent_of_atlas`, `…_eq_of_pou_independent`);
σ-finite / locally finite / finite-on-compacts (`Properties.lean`); finset-sum
evaluation (`riemannianVolumeMeasure_eq_finset_sum`,
`integral_riemannianVolumeMeasure_eq_finset_sum`); disjoint-source chart-local
`apply`; divergence theorem (closed/boundary/Green) + IBP + L²;
`VolumeVariation` (∂ₜ vol = ½∫tr(∂ₜg)); **`JacobiFormula.lean` = the
log-Jacobian calculus** (`hasDerivAt_det_eq_det_mul_trace_inv_mul`,
`hasDerivAt_sqrt_det_eq_half_trace_inv_mul`) — exactly the Riccati-side
algebra of Bishop's argument.

**Comparison/Jacobi layer** (0-sorry): Jacobi fields + exp-variation-is-Jacobi
+ endpoint `J(1) = d(exp)w` (`Exponential/JacobiVariation`); second-order
Grönwall upper bounds (`Analysis/ODE/SecondOrderGronwall`); covariant Grönwall
lower bounds / nonvanishing (`Variation/CovariantGronwall`, the item-3a
keystone); conjugate-free ⟹ `d(exp)` injective (`ExpNonsingular`); parallel ON
frames (`Variation/PerpFrame`); Gauss lemma + `expMapC2Radius` (+positivity);
index form (`Variation/SecondVariation`); minimizing geodesics
(`Exponential/MinimizingGeodesic`, `IntrinsicExp`) + proper realization
(`HopfRinowProper`); normal charts/`expMapDiffeo`.

**Bonnet–Myers engine** (`Comparison/BonnetMyers/`): `RicciBoundedBelow`
predicate (`RicciBound.lean`, 0-sorry) and — the headline finding —
**`bonnet_myers_length_le_of_ricci_bound` is PROVED** (`LengthBound.lean`,
0-sorry, incl. `ricci_eq_sum_sectional_curvature_of_orthonormal_perp_frame`
and the summed index-form comparison).  The index-form-with-parallel-frame
comparison culture this lane needs is already alive in-tree.
(`Headlines.lean` carries 5 packaging sorries — diameter/compactness wrappers
routed through the dead-sorry `HopfRinow.lean`; not our concern here.)

**Available from Mathlib**: `MeasureTheory/Constructions/HaarToSphere.lean`
(polar decomposition of Haar measure, for Stage V2) and
`Analysis/SpecialFunctions/PolarCoord.lean`; `addHaar_smul`-family ball
scaling; `Function.Jacobian` change-of-variables (fallback only).

**Genuinely missing (the work):** the normal-chart specialization of the
measure (V1a), the Gram-of-Jacobi-fields representation of the normal-chart
metric (V1b), the two-sided Jacobian bounds/Riccati comparison (V1c/V2b), and
polar-coordinates transfer (V2a).  No new foundations required.

## Stage V0 — Integration-layer parametrization-evaluation API (ruled 2026-07-07)

The first executor run (Codex, 2026-07-07) stopped at V1a per protocol: the
Integration layer has canonical-chart evaluation only (`chartLocalMeasure_*`,
canonical-pair transition-density identities), no arbitrary-chart/normal-chart
evaluation.  Planner verified the gap (incl. `DivergenceTheorem/ChartInvariance`
and `ChartRegistration` — neither closes it) and ruled: add the canonical API
**at the Integration layer**, in parametrization form —

`riemannianVolumeMeasure g (Ψ '' B) = ∫⁻ w in B, ofReal (paramDensity g Ψ w) ∂modelHaar`

for `Ψ` a `C¹` partial diffeomorphism `E → M`, measurable `B ⊆ Ψ.source`,
`paramDensity = √det (pulled-back Gram)`.  Proof = POU/canonical decomposition
+ per-chart Euclidean change of variables along `chart_i ∘ Ψ` (Mathlib
`Function.Jacobian`) + the Gram transformation law (generalize the existing
canonical-pair density identity) + recombination.  New file
`Analysis/Integration/Measure/ParamEvaluation.lean`; kickoff prompt
`VOLCOMP_V0_API_HANDOFF.md`.  Serves V1a, V2a (polar), the entropy integrals,
and any future normal-coordinate integration.

## Stage V1 — capped-scale two-sided volume comparability (~2–4 weeks)

**Target:** under `‖Rm‖ ≤ C₀` and `HasInjRadiusAt g x s`, for
`s ≤ r₀(n, C₀) := c·min(1, C₀^{-1/2})`:
`c₁(n,C₀)·sⁿ ≤ (riemannianVolumeMeasure g) (ball x s) ≤ c₂(n,C₀)·sⁿ`.
No cut locus, no polar coordinates, no pushforward inequality.

Bricks:
- **V1a chart evaluation**: for `A ⊆` (normal chart image at `x`),
  `vol A = ∫_{(normalChartAt x)'' A} chartDensity dλ` — assemble from
  atlas-independence + the chart-local apply lemmas, specialized to an atlas
  containing the normal chart.  Mechanical against the existing layer.
- **V1b Gram = Jacobi Gram**: the normal-chart Gram matrix at `tv` is the Gram
  matrix of the Jacobi fields `J_i` along `t ↦ exp(tv)` with
  `J_i(0)=0, J_i'(0)=e_i` (from `JacobiVariation`'s exp-variation + endpoint
  identity; this is the `B0NormalCoordBounds.md` stage-2 blueprint, now for the
  measure rather than for `lbl395`).
- **V1c two-sided det bounds at capped scale**: `‖J‖ ≤ cosh`-type upper
  (SecondOrderGronwall) and `‖J_w(t)‖ ≥ c·t‖w‖` lower (CovariantGronwall) for
  `t ≤ r₀` give two-sided singular-value hence `det` bounds
  `(c₁')ⁿ t^{…} ≤ √det Gram(tv) ≤ (c₂')ⁿ …`.
- **V1d integrate + scale**: integrate V1c over the tangent ball with
  `addHaar` ball scaling.  Ball inside the chart via `HasInjRadiusAt` (lower
  bound) and minimizing-geodesic surjectivity below the scale (upper bound).

**V1e — discharge the HCG inputs.**  Producer instances for
`VolumeComparisonInput` and `PackingBound` from V1d, **after one more honest
statement refinement** (same audit rule as 2026-07-05): the `ballMult` guard
must be the joint cap `m * r ≤ r0` (not `r ≤ r0` — at fixed `r` and `m → ∞`
the packing region is again unbounded and the count exceeds any `Imult m`),
and the V1-route producer additionally wants inj control at the centers
(`HasInjRadiusAt … (centers i) r`-shaped hypothesis, which the Step-A
consumers can supply from A0-decay: the net's `λ ≤ inj` discipline is a
recorded `InjRadiusDecayInput` lemma).  Alternative: prove the uncut relative
BG of Stage V2 first and discharge the input without the inj hypothesis;
choose whichever refinement lands first, but do NOT leave the current guard
as-is when the producer lands.

## Stage V2 — Bishop–Gromov relative monotonicity (~1–2 months)

**Target:** `r ↦ vol(B(x,r)) / V_K(r)` non-increasing (K = Ricci lower bound),
Gromov's form, valid past the injectivity radius.
- V2a polar transfer: `∫_{ball} f dλ = ∫_{sphere} ∫_r` via Mathlib
  `HaarToSphere`, composed with V1a.
- V2b Riccati/trace comparison: `(log √det Gram)' ≤ (n-1)·(log s_K)'` before
  the first conjugate point — `JacobiFormula`'s trace formula + Jacobi ODE +
  index-form/Cauchy–Schwarz + the ON-frame Ricci trace lemma already proved in
  `BonnetMyers/LengthBound`.
- V2c segment domain: star-shaped a.e. domain `{tv : t < cutTime v}` with
  measurable `cutTime`, `exp` bijective a.e. onto `M` — the classically fiddly
  measure-theoretic brick; budget a design pass.
- V2d ratio monotonicity + corollaries (uncapped packing, doubling).

## Stage V3 — Cheeger–Gromov–Taylor injectivity decay (~2–3 months)

`|Rm| ≤ C₀` + `inj(O) ≥ ι₀` ⟹ `inj(x) ≥ a·min(ι₀,1)ⁿ·e^{-C·d(x,O)}` —
discharges HCG A0 (`InjRadiusDecayInput`), turning the conditional Theorem 3.9
fully volume-free of citations except `lbl395`/`lbl418`-class inputs.
Route: V2 + Cheeger's lemma (short geodesic loops vs volume; uses the closed
geodesic/loop machinery adjacent to `LengthBound`).  Plan in detail when V2
lands.

## Execution notes

- Lane home: `Geometry/Comparison/Volume/` (new subfolder; below Flow/, above
  Integration/ — imports both).  First file: `Volume/NormalChartMeasure.lean`
  (V1a+V1b), then `Volume/JacobianBounds.lean` (V1c), `Volume/BallVolume.lean`
  (V1d), `Volume/PackingProducers.lean` (V1e, imports HCGCompactness C4
  StepAInputs to instantiate the inputs).
- Statement-audit rule applies: every stage's target statement gets the
  "why true / at which scale / who consumes" docstring BEFORE proofs start.
- Parallelism: V1 is independent of every active lane; V2c (segment domain)
  is the only brick with design risk — do not start it before V1 lands.

## Status log

- 2026-07-05: plan + asset audit written.  User green-lit starting volume
  comparison (linear parabolic layer reported handled by a collaborator,
  pending merge — NLC route A's pole shrinks to integration-with-that-merge).
- 2026-07-07: current active status is Stage V1d shell work, not a restart at
  V0.  `Geometry/Comparison/Volume/NormalChartMeasure.lean`,
  `JacobianBounds.lean`, and `BallVolume.lean` now contain the conditional
  normal-chart evaluation, radial-Jacobi density upper/lower algebraic bridges, scaled
  coordinate/metric-ball consumers, realized Hopf-Rinow metric-ball bridges, and
  a local single-radius two-sided metric-ball assembly with metric-ball
  measurability discharged.  The lower-density side now also has the
  V1d-facing determinant bridge `density_ge_det_ball`, which turns a
  model-ball determinant lower bound for `radialJacobiGram` into the density
  lower hypothesis used by the ball-volume consumers.  The fixed-space
  Gronwall endpoint wrappers `gronwall_le_linear` and `gronwall_ge_linear`
  are also in place in `Analysis/ODE/SecondOrderGronwall.lean`, and
  `Variation/CovariantGronwall.lean` now exposes `covGronwall_bounds`, the
  corresponding parallel-frame transfer for `sqrt(g(J,J))` upper/lower
  endpoint estimates.  Next target: instantiate `covGronwall_bounds` against
  the radial Jacobi fields, including the parallel-frame, differentiability,
  covariant ODE-bound, and initial-condition hypotheses, to get radial-Jacobi
  endpoint length and determinant/eigenvalue/singular-value bounds feeding
  `density_ge_det_ball` and `normalDensity_ge_of_eigen_bound`, or package the
  explicit capped-scale radius/constants needed by the final V1d theorem; do
  not re-audit or redo V0/V1a/V1b shells.
- 2026-07-07: V1c producer infrastructure advanced one layer: fixed-space
  `gronwall_le_linear` / `gronwall_ge_linear` and covariant
  `covGronwall_bounds` are verified.  The final radial-Jacobi determinant
  theorem is still 0%: the next missing API is the radial instantiation package
  for `covGronwall_bounds` (parallel frame, `chartRepAt` differentiability for
  `J` and `D_tJ`, covariant ODE-bound from curvature control on `Ico 0 b`, and
  the `t = 0` Jacobi-ODE endpoint).  Current honest estimates: V1c producer
  infrastructure ~28%, V1c two-sided determinant theorem 0%, Stage V1 ~50%,
  whole volume-comparison lane ~28%.
- 2026-07-07: added `Volume/RadialGronwall.lean` with `radialJacobi_bounds`,
  the radial specialization of `covGronwall_bounds`.  This removes one
  assembly layer but does not prove the regularity, full parallel-frame, or
  curvature-bound hypotheses.  Next target: build the hypothesis package for
  `radialJacobi_bounds`, then specialize the `t = 1` upper/lower bounds for
  the basis fields entering `radialJacobiGram`.  Current honest estimates:
  V1c producer infrastructure ~34%, V1c two-sided determinant theorem 0%,
  Stage V1 ~51%, whole volume-comparison lane ~29%.
- 2026-07-07: added `radialJacobi_one_bounds`, the `t = 1` endpoint form
  closest to the `radialJacobiGram` basis fields.  Next target: supply the
  regularity/ODE/parallel-frame hypothesis package for this endpoint theorem,
  then derive a uniform endpoint-length upper bound for the basis fields.
  Current honest estimates: V1c producer infrastructure ~36%, V1c two-sided
  determinant theorem 0%, Stage V1 ~52%, whole volume-comparison lane ~29%.
- 2026-07-07: extended `Volume/RadialGronwall.lean` with `radialCurve_one`,
  `radialJacobi_one_le`, and `radialJacobi_fin_le`.  This now gives a verified
  conditional endpoint-length producer in the exact fixed-basis shape consumed
  by the existing V1c/V1d density upper-bound lemmas.  It still does not prove
  the analytic hypotheses or scalar model-bound input.  The next target is the
  honest hypothesis package for `radialJacobi_fin_le`: radial-curve regularity,
  parallel orthonormal frame, `chartRepAt` differentiability for each basis
  Jacobi field and its covariant derivative, ODE bound from curvature control,
  and an initial-speed/scalar bound.  Current API caveat: the available
  derivative-at-zero producer `exists_radialJacobi_deriv_radius` is a
  small-`w` radius statement, so it does not by itself discharge fixed
  `chartModelBasis` inputs.  Current honest estimates: V1c producer
  infrastructure ~39%, V1c two-sided determinant theorem 0%, Stage V1 ~53%,
  whole volume-comparison lane ~30%.
- 2026-07-07: extended `Volume/JacobianBounds.lean` with
  `density_le_gronwall`, a pointwise upper-density bridge that consumes
  `radialJacobi_fin_le` directly and feeds the existing normal-density upper
  bound.  This removes the manual endpoint-length hypothesis at the pointwise
  density layer, but still keeps the real producers explicit: radial regularity,
  parallel orthonormal frame, `chartRepAt` differentiability for each basis
  Jacobi field and its covariant derivative, the ODE bound, and the scalar
  Gronwall model bound.  Next target remains the honest analytic/initial-speed
  package for these hypotheses, not a new wrapper.  Current honest estimates:
  V1c determinant-bound algebraic bridge ~79%, V1c producer infrastructure
  ~40%, V1c two-sided determinant theorem 0%, Stage V1 ~54%, whole
  volume-comparison lane ~31%.
- 2026-07-07: added the scalar compression layer for the upper Gronwall route:
  `Analysis/ODE/SecondOrderGronwall.lean` now has
  `gronwallBound_zero_mono_eps`, `Volume/RadialGronwall.lean` has
  `radialJacobi_fin_le_of_init_bound`, and `Volume/JacobianBounds.lean` has
  `density_le_gronwall_of_init_bound`.  The upper-density route now needs only
  a uniform initial-speed bound `A` for the fixed basis Jacobi fields plus one
  scalar model comparison `A + gronwallBound 0 (max K 1) (K * (b * A)) 1 <= B`,
  instead of a separate scalar Gronwall expression for every basis vector.
  This still does not prove the fixed-basis initial-speed bound, radial
  regularity, parallel orthonormal frame, differentiability, or ODE-bound
  hypotheses.  Next target: produce or honestly package the fixed-basis
  initial-speed estimate and analytic hypothesis bundle.  Verification: focused
  checks and targeted builds passed through `Volume.BallVolume`; narrow search
  found no `sorry`/`axiom` in the edited volume/ODE files.  Current honest
  estimates: V1c Gronwall producer infrastructure ~43%, V1c determinant-bound
  algebraic bridge ~81%, V1c two-sided determinant theorem 0%, Stage V1 ~55%,
  whole volume-comparison lane ~32%.
- 2026-07-07: advanced the fixed-basis initial-speed interface without hiding
  the remaining producer.  `Volume/RadialGronwall.lean` now has
  `radialCurve_zero`, `radialJacobi_init_le_of_deriv_eq`, and
  `radialJacobi_fin_le_of_deriv_eq`; `Volume/JacobianBounds.lean` now has
  `density_le_gronwall_of_deriv_eq`.  The upper-density route can now consume
  fixed-basis derivative equalities `D_tJ_k(0)=e_k` plus a uniform `g_p`-length
  bound on the model basis, instead of the abstract initial-speed hypothesis
  `hinit`.  This still does not prove the derivative equalities from
  `exists_radialJacobi_deriv_radius`; that producer remains small-`w`, so the
  next target is either a fixed-basis radius bridge (prove every
  `chartModelBasis` vector is inside the radius in the chosen scale) or a
  scaling/linearity bridge that avoids requiring the raw basis vectors to be
  small.  Verification passed through the `Volume.BallVolume` target.  Current
  honest estimates: V1c Gronwall producer infrastructure ~46%,
  V1c determinant-bound algebraic bridge ~83%, V1c two-sided determinant
  theorem 0%, Stage V1 ~56%, whole volume-comparison lane ~33%.
- 2026-07-07: added the direct fixed-basis radius bridge.  `Volume/RadialGronwall.lean`
  now has `fin_deriv_radius` and `radialJacobi_fin_le_of_radius_deriv`;
  `Volume/JacobianBounds.lean` now has `density_le_gronwall_of_radius_deriv`.
  This consumes a small-radius derivative theorem directly but keeps the
  fixed-basis smallness side condition `‖chartModelBasis E k‖ < r` explicit.
  That confirms the direct radius route is only a partial bridge: for an
  arbitrary small derivative radius, the raw fixed model basis may not be
  inside it.  Next target: build a scaling/linearity bridge for radial Jacobi
  fields/initial derivative, or otherwise replace the raw-basis smallness
  requirement with a scaled-basis argument that still recovers endpoint
  bounds for the original basis.  Current honest estimates: V1c Gronwall
  producer infrastructure ~48%, V1c determinant-bound algebraic bridge ~84%,
  V1c two-sided determinant theorem 0%, Stage V1 ~56%, whole
  volume-comparison lane ~33%.
- 2026-07-07: added the scaled-basis upper route and updated this plan as the
  source of truth.  `Volume/NormalChartMeasure.lean` now has
  `radialJacobi_one_smul`; `Volume/RadialGronwall.lean` now has
  `radialJacobi_one_le_of_smul`, `radialJacobi_one_le_of_scaled_radius`, and
  `radialJacobi_fin_le_of_scaled_radius`; `Volume/JacobianBounds.lean` now has
  `density_le_gronwall_of_scaled_radius`.  This replaces the raw fixed-basis
  smallness obstruction on the upper route by an explicit positive scale `a`,
  scaled-basis smallness `‖a • chartModelBasis E k‖ < r`, scaled analytic
  hypotheses, and a scaled model comparison `... <= a * B`.  It does not start
  the two-sided capped Jacobian theorem and does not solve the lower determinant
  route.  Verification passed for focused checks and targeted builds through
  `Volume.BallVolume`.  Next target: build the analytic package for the scaled
  upper route and the determinant/eigenvalue lower route, including an explicit
  common scale and curvature/ODE inputs.  Current honest estimates: V1c
  Gronwall producer infrastructure ~52%, V1c determinant-bound algebraic bridge
  ~86%, V1c two-sided determinant theorem 0%, Stage V1 ~57%, whole
  volume-comparison lane ~34%.
- 2026-07-07: added the common-scale algebra for the scaled upper route.
  `Volume/RadialGronwall.lean` now has `basisScaleSmall`, which produces a
  positive common scale `a` with `‖a • chartModelBasis E k‖ < r` for every
  fixed basis vector whenever `0 < r`, and `basisInit_smul_le`, which converts
  an original center basis-length bound into the scaled initial-speed bound.
  This removes two bookkeeping inputs from the scaled upper route but does not
  provide the analytic package for scaled Jacobi fields, the scaled scalar
  model inequality, or any lower determinant control.  Verification passed for
  focused and targeted checks of `Volume.RadialGronwall`, plus downstream
  targeted builds through `Volume.JacobianBounds` and `Volume.BallVolume`.
  Next target: package
  the scaled analytic hypotheses (`J_{a e_k}`, `D_tJ_{a e_k}`, parallel frame,
  curvature/ODE bound) and separately build the determinant/eigenvalue lower
  producer.  Current honest estimates: V1c Gronwall producer infrastructure
  ~54%, V1c determinant-bound algebraic bridge ~86%, V1c two-sided determinant
  theorem 0%, Stage V1 ~58%, whole volume-comparison lane ~34%.
- 2026-07-07: added the lower-route Rayleigh bridge.  `Volume/JacobianBounds.lean`
  now has `eigenvalues_ge_of_rayleigh`,
  `sqrt_pow_le_sqrt_det_of_rayleigh`,
  `normalDensity_ge_of_rayleigh_bound`, and `density_ge_rayleigh_ball`, turning
  a unit-vector Rayleigh lower bound for `radialJacobiGram` into the existing
  eigenvalue/determinant/density lower consumers, with model-ball source and
  `C²`-radius side conditions discharged in the ball form.  This is still not
  the Jacobi/Gronwall lower producer: the next target is to prove or honestly
  package the singular-value/Rayleigh lower bound for the radial Jacobi Gram,
  while the scaled upper route still needs its analytic hypothesis package.
  Verification passed for focused and targeted `Volume.JacobianBounds`, plus
  downstream targeted build through `Volume.BallVolume`.  Current honest
  estimates: V1c Gronwall producer infrastructure ~54%, V1c determinant-bound
  algebraic bridge ~88%, V1c two-sided determinant theorem 0%, Stage V1 ~59%,
  whole volume-comparison lane ~35%.
- 2026-07-07: added the lower-route Jacobi-combination quadratic adapter.
  `Volume/JacobianBounds.lean` now has `radialJacobiGram_quadratic`,
  `normalDensity_ge_of_combo_bound`, and `density_ge_combo_ball`, identifying
  `vᵀ(radialJacobiGram)v` with the Riemannian norm-square of
  `∑ i, v_i J_i(1)` and feeding that combo norm lower bound into the density
  lower route.  This still does not prove the Jacobi/Gronwall lower norm bound
  for unit combinations.  Next target: produce or honestly package that lower
  norm bound; the scaled upper route still separately needs its analytic
  hypothesis package.  Verification passed for focused and targeted
  `Volume.JacobianBounds`, plus downstream targeted build through
  `Volume.BallVolume`.  Current honest estimates: V1c Gronwall producer
  infrastructure ~54%, V1c determinant-bound algebraic bridge ~90%, V1c
  two-sided determinant theorem 0%, Stage V1 ~59%, whole volume-comparison lane
  ~35%.
- 2026-07-07: added the endpoint finite-linearity and direction-field lower
  consumers.  `Volume/NormalChartMeasure.lean` now has
  `radialJacobi_one_sum`; `Volume/JacobianBounds.lean` now has
  `normalDensity_ge_of_dir_bound` and `density_ge_dir_ball`.  The lower route
  can now target a direct endpoint lower bound for
  `J_{sum_i v_i e_i}(1)` for every unit coefficient vector `v`, instead of an
  abstract Rayleigh/eigenvalue hypothesis.  This still does not prove that
  Jacobi lower norm bound.  Next target: produce or honestly package the lower
  radial-Jacobi endpoint norm estimate for unit coefficient directions; the
  scaled upper route still separately needs its analytic hypothesis package.
  Verification passed for focused and targeted `Volume.NormalChartMeasure`,
  focused and targeted `Volume.JacobianBounds`, plus downstream targeted build
  through `Volume.BallVolume`.  Current honest estimates: V1c Gronwall producer
  infrastructure ~55%, V1c determinant-bound algebraic bridge ~91%, V1c
  two-sided determinant theorem 0%, Stage V1 ~60%, whole volume-comparison lane
  ~35%.
- 2026-07-07: added the conditional lower endpoint Gronwall producer shape.
  `Volume/RadialGronwall.lean` now has `radialJacobi_one_ge`,
  `radialJacobi_sq_ge`, and `radialJacobi_dir_ge`, extracting the lower half of
  the endpoint Gronwall bound, squaring it under a nonnegative model lower
  bound, and packaging it for every unit coefficient direction.  This is still
  not the analytic package: the next target is to supply radial regularity,
  parallel-frame, ODE/curvature, initial-speed lower, and scalar model lower
  comparisons for `J_{sum_i v_i e_i}`.  The scaled upper route still separately
  needs its analytic hypothesis package.  Verification passed for focused and
  targeted `Volume.RadialGronwall`, plus downstream targeted builds through
  `Volume.JacobianBounds` and `Volume.BallVolume`.  Current honest estimates:
  V1c Gronwall producer infrastructure ~56%, V1c determinant-bound algebraic
  bridge ~91%, V1c two-sided determinant theorem 0%, Stage V1 ~60%, whole
  volume-comparison lane ~35%.
- 2026-07-07: added the coefficient-space initial-length lower bridge.
  `Volume/RadialGronwall.lean` now has `exists_unitCoeff_ge`, using the
  `toEuclidean.symm` realization of `chartModelBasis`, the anti-Lipschitz bound
  for that continuous linear equivalence, and `gpCoerciveConst_le` to produce a
  uniform positive lower bound for
  `sqrt (g_p (sum_i v_i e_i) (sum_i v_i e_i))` over all unit coefficient
  vectors.  This is still not the lower analytic package: the next target is to
  prove or package the Jacobi initial-derivative equality
  `D_t J_{sum_i v_i e_i}(0) = sum_i v_i e_i`, then combine it with radial
  regularity, parallel-frame, ODE/curvature, and scalar model-error inputs for
  `radialJacobi_dir_ge`.  The scaled upper route still separately needs its
  analytic hypothesis package.  Verification passed for focused and targeted
  `Volume.RadialGronwall`, plus downstream targeted builds through
  `Volume.JacobianBounds` and `Volume.BallVolume`.  Current honest estimates:
  V1c Gronwall producer infrastructure ~57%, V1c determinant-bound algebraic
  bridge ~91%, V1c two-sided determinant theorem 0%, Stage V1 ~60%, whole
  volume-comparison lane ~35%.
- 2026-07-08: added the conditional unit-direction initial-speed package.
  `Volume/RadialGronwall.lean` now has `dir_deriv_radius`, `dir_init_ge`, and
  `exists_dirInit_ge`: the first turns the small-radius radial-Jacobi initial
  derivative theorem into the unit-coefficient direction equality under the
  explicit side condition `||sum_i v_i e_i|| < r`; the latter two combine any
  supplied equality with `exists_unitCoeff_ge` to produce the lower-route
  initial-speed bound used by `radialJacobi_dir_ge`.  This is still not the
  final lower analytic package.  Next target: resolve the unit-direction
  smallness/scaling issue honestly, then combine that with radial regularity,
  parallel-frame, ODE/curvature, and scalar model-error inputs for
  `radialJacobi_dir_ge`.  Verification passed for focused and targeted
  `Volume.RadialGronwall`, plus downstream targeted builds through
  `Volume.JacobianBounds` and `Volume.BallVolume`.  Current honest estimates:
  V1c Gronwall producer infrastructure ~59%, V1c determinant-bound algebraic
  bridge ~91%, V1c two-sided determinant theorem 0%, Stage V1 ~60%, whole
  volume-comparison lane ~35%.
- 2026-07-08: resolved the lower-route unit-direction smallness/scaling bridge
  conditionally.  `Analysis/ODE/SecondOrderGronwall.lean` now has
  `gronwallBound_zero_mul_eps`, the zero-initial scalar scaling identity for
  the Gronwall error.  `Volume/RadialGronwall.lean` now has
  `unitDirScaleSmall`, `radialJacobi_one_ge_of_smul`,
  `radialJacobi_one_ge_of_scaled_radius`,
  `radialJacobi_dir_ge_of_scaled_radius`, `model_ge_of_smul`, and
  `dirModel_ge_smul`.  Together these replace the false-looking raw condition
  `||sum_i v_i e_i|| < r` by a common positive scale `a`, apply the derivative
  radius theorem to `a • sum_i v_i e_i`, divide the endpoint lower bound back
  using endpoint linearity, and scale the lower scalar model comparison.  This
  is still not the final lower analytic package: the next target is to produce
  or honestly package radial regularity, parallel-frame, `chartRepAt`
  differentiability, ODE/curvature, and an unscaled lower scalar model
  comparison for unit coefficient directions.  Verification passed for focused
  and targeted `SecondOrderGronwall`, targeted `Variation.CovariantGronwall`,
  focused and targeted `Volume.RadialGronwall`, plus downstream targeted
  builds through `Volume.JacobianBounds` and `Volume.BallVolume`.  Current honest
  estimates: V1c Gronwall producer infrastructure ~63%, V1c
  determinant-bound algebraic bridge ~91%, V1c two-sided determinant theorem
  0%, Stage V1 ~61%, whole volume-comparison lane ~36%.
- 2026-07-08: advanced the lower scalar model route from per-direction data to
  a uniform two-sided coefficient package plus one scalar smallness condition.
  `Volume/RadialGronwall.lean` now has `exists_unitCoeff_le`, the matching
  finite-dimensional upper bound for
  `sqrt (g_p (sum_i v_i e_i) (sum_i v_i e_i))` on unit coefficient vectors;
  `exists_unitCoeff_bounds`, which packages the lower constant `B0` and upper
  constant `D`; and `dirModel_ge_of_bounds`, which reduces the unscaled lower
  model comparison to
  `B <= B0 - gronwallBound 0 (max K 1) (K * (b * D)) 1`.  This is still not the
  final lower analytic package: the next target is to produce or honestly
  package the scaled radial regularity, parallel-frame, `chartRepAt`
  differentiability, ODE/curvature, and then choose parameters so the recorded
  scalar smallness inequality holds for unit coefficient directions.  Focused
  and targeted `Volume.RadialGronwall` verification passed, plus downstream
  targeted builds through `Volume.JacobianBounds` and `Volume.BallVolume`.
  Current honest estimates: V1c Gronwall producer infrastructure ~65%, V1c
  determinant-bound algebraic bridge ~91%, V1c two-sided determinant theorem
  0%, Stage V1 ~61%, whole volume-comparison lane ~36%.
- 2026-07-08: closed the lower-route scalar smallness choice as a checked
  existence brick.  `Analysis/ODE/SecondOrderGronwall.lean` now has
  `exists_gron_small`, a pure scalar lemma choosing `b > 0` and `B > 0` so the
  zero-initial Gronwall error is dominated by a positive lower bound.  Consuming
  it, `Volume/RadialGronwall.lean` now has `exists_dirModel_ge`, which combines
  `exists_unitCoeff_bounds`, `exists_gron_small`, and `dirModel_ge_of_bounds`
  to produce a positive lower scalar model bound for every unit coefficient
  direction.  This is still not the final lower analytic package: the next
  target is the scaled radial analytic package and Jacobi initial-derivative
  bridge, after which `dirModel_ge_smul` can transport this unscaled model
  bound to the scaled endpoint route.  Focused and targeted verification passed
  for `SecondOrderGronwall` and `Volume.RadialGronwall`, plus downstream
  targeted builds through `Volume.JacobianBounds` and `Volume.BallVolume`.
  Current honest estimates: V1c Gronwall producer infrastructure ~67%, V1c
  determinant-bound algebraic bridge ~91%, V1c two-sided determinant theorem
  0%, Stage V1 ~62%, whole volume-comparison lane ~37%.
- 2026-07-08: packaged the radial parallel-frame sub-block needed by the V1c
  analytic producer.  `Volume/RadialGronwall.lean` now has
  `exists_radialFrame`, which turns `C²` regularity of the radial curve on a
  positive interval into the full `hcard/hFdiff/hpar/hON` frame bundle consumed
  by the existing `radialJacobi_*` endpoint lemmas.  This reuses the existing
  orthonormal-basis producer and `Variation.PerpFrame.exists_parallel_frame`;
  it does not prove radial curve regularity, Jacobi-field differentiability, the
  Jacobi ODE/curvature hypotheses, or the Jacobi initial-derivative bridge.
  Next target: package radial curve regularity at the scaled radius and the
  `J`/`DJ` differentiability plus ODE/curvature hypotheses; then connect the
  Jacobi initial-derivative equality so `dirModel_ge_smul` can feed the scaled
  lower endpoint route.  Focused and targeted verification passed for
  `Volume.RadialGronwall`, plus downstream targeted builds through
  `Volume.JacobianBounds` and `Volume.BallVolume`.  Current honest estimates:
  V1c Gronwall producer infrastructure ~69%, V1c determinant-bound algebraic
  bridge ~91%, V1c two-sided determinant theorem 0%, Stage V1 ~62%, whole
  volume-comparison lane ~37%.
- 2026-07-08: closed the honest interval radial-regularity sub-block.
  `Volume/RadialGronwall.lean` now has `radialCurve_contMDiffOn_Icc`, proving
  `C²` regularity of `t ↦ expMap g p (t • x)` on `[0, 1]` under
  `‖x‖ < expMapC2Radius g p`.  The proof reuses the existing pointwise
  `radialCurve_contMDiffAt2` theorem and the elementary estimate
  `‖t • x‖ ≤ ‖x‖` for `t ∈ [0, 1]`.  This deliberately does not claim the
  global `ContMDiff` hypothesis still required by the current
  `exists_parallel_frame` wrapper; localizing that frame API or adding an
  honest smooth extension remains separate.  Next target: package the radial
  Jacobi-field side, namely `chartRepAt` differentiability for `J` and `DJ`
  plus the ODE/curvature hypotheses consumed by `radialJacobi_*`; then connect
  the Jacobi initial-derivative equality.  Focused and targeted verification
  passed for `Volume.RadialGronwall`, plus downstream targeted builds through
  `Volume.JacobianBounds` and `Volume.BallVolume`.  Current honest estimates:
  V1c Gronwall producer infrastructure ~70%, V1c determinant-bound algebraic
  bridge ~91%, V1c two-sided determinant theorem 0%, Stage V1 ~62%, whole
  volume-comparison lane ~37%.
- 2026-07-08: split the radial Jacobi ODE frontier from the curvature-bound
  frontier.  `Variation/JacobiField.lean` now has
  `ode_bound_of_isJacobiAt`, a generic projection from pointwise `IsJacobiAt`
  plus a curvature-term norm bound to the second-covariant-derivative norm
  bound used by Gronwall.  `Volume/RadialGronwall.lean` now has
  `radialJacobi_ode_of_curv`, the radial wrapper producing the exact `hODE`
  shape consumed by `radialJacobi_*`.  This does not prove the curvature-term
  bound, the `t = 0` Jacobi endpoint needed for `Ico`, or `chartRepAt`
  differentiability for `J` and `DJ`; those are now the honest next targets.
  Verification passed for focused and targeted `Variation.JacobiField` and
  `Volume.RadialGronwall`, plus downstream targeted builds through
  `Volume.JacobianBounds` and `Volume.BallVolume`.  Current honest estimates:
  V1c Gronwall producer infrastructure ~71%, V1c determinant-bound algebraic
  bridge ~91%, V1c two-sided determinant theorem 0%, Stage V1 ~63%, whole
  volume-comparison lane ~37%.
- 2026-07-08: packaged the interior radial-Jacobi ODE route while keeping the
  `t = 0` endpoint gap explicit.  `Volume/RadialGronwall.lean` now has
  `exists_jacobi_Ioo`, which restricts the existing radius theorem from
  `(0, 1)` to every smaller `(0, b)` with `b <= 1`, and
  `ode_Ico_of_Ioo_zero`, which builds the Gronwall `Ico 0 b` ODE input from
  open-interval Jacobi/curvature hypotheses plus a separate endpoint ODE bound
  at `0`.  This does not prove that endpoint bound, the curvature-term norm
  estimate, or the `J`/`DJ` `chartRepAt` differentiability inputs.  Next target:
  produce the endpoint ODE bound at `t = 0` or, if that exposes a real analytic
  gap, package the curvature-term bound on `(0, b)` and keep the endpoint as
  the single visible frontier.  Focused and targeted `Volume.RadialGronwall`
  verification passed, plus downstream targeted builds through
  `Volume.JacobianBounds` and `Volume.BallVolume`.  Current honest estimates:
  V1c Gronwall producer infrastructure ~72%, V1c determinant-bound algebraic
  bridge ~91%, V1c two-sided determinant theorem 0%, Stage V1 ~63%, whole
  volume-comparison lane ~37%.
- 2026-07-08: packaged the interior Jacobi data into the `Ico` ODE producer.
  `Volume/RadialGronwall.lean` now has `exists_ode_Ico`, which combines
  `exists_jacobi_Ioo` with `ode_Ico_of_Ioo_zero` and removes the explicit
  open-interval Jacobi predicate from future callers.  This still does not
  prove the endpoint ODE bound at `t = 0`, the curvature-term norm estimate on
  `(0, b)`, or the `J`/`DJ` `chartRepAt` differentiability inputs.  A direct
  endpoint route was inspected and currently appears to need a two-sided local
  rescale/geodesic identity near `0`; the public rescale wrapper only exposes
  `[0, 1]`, so the endpoint remains a visible API gap unless a different proof
  route is found.  Next target: package the curvature-term bound on `(0, b)`
  while keeping the endpoint gap visible.  Focused and targeted
  `Volume.RadialGronwall` verification passed, plus downstream targeted builds
  through `Volume.JacobianBounds` and `Volume.BallVolume`.  Current honest
  estimates: V1c Gronwall producer infrastructure ~73%, V1c determinant-bound
  algebraic bridge ~91%, V1c two-sided determinant theorem 0%, Stage V1 ~63%,
  whole volume-comparison lane ~37%.
- 2026-07-08: added the curvature norm-to-square packaging layer in
  `Volume/RadialGronwall.lean`.  `curv_sq_of_norm_Ioo` converts the natural
  square-root curvature-term bound on `(0, b)` into the squared `hODE`
  curvature input, and `exists_ode_Ico_of_curvNorm` packages that conversion
  with `exists_ode_Ico`; `radialCurvTerm` is only a private abbreviation for
  the existing `riemannOp(J, velocity, velocity)` term.  This does not prove
  the geometric curvature estimate itself, the endpoint ODE bound at `t = 0`,
  or the `J`/`DJ` `chartRepAt` differentiability inputs.  Next target: prove
  the actual radial curvature-term norm estimate on `(0, b)` using existing
  curvature operator/fibre-norm infrastructure where possible, while keeping
  the endpoint API gap visible.  Focused and targeted `Volume.RadialGronwall`
  verification passed, plus downstream targeted builds through
  `Volume.JacobianBounds` and `Volume.BallVolume`.  Current honest estimates:
  V1c Gronwall producer infrastructure ~74%, V1c determinant-bound algebraic
  bridge ~91%, V1c two-sided determinant theorem 0%, Stage V1 ~64%, whole
  volume-comparison lane ~38%.
- 2026-07-08: inspected the actual radial curvature-term estimate route after
  the norm-to-square packaging.  A direct model/operator-norm lemma for
  `R(J, velocity) velocity` was not kept: Lean does not synthesize the needed
  `Norm` instances for the nested tangent-space continuous-linear-map
  expression, and the existing curvature-estimate layer is the intrinsic
  `riemannianFiberNormSq`/orthonormal-frame API rather than model-space
  operator norms.  This is a layer/API issue, not a settled curvature estimate.
  Next target: use the existing fibre-norm curvature machinery, or add the
  smallest bridge from the tangent vector term `R(J, V) V` to that machinery,
  while keeping the endpoint ODE gap at `t = 0` visible.  Focused
  `Volume.RadialGronwall` verification passed after backing out the failed
  operator-norm attempt.  Current honest estimates remain: V1c Gronwall
  producer infrastructure ~74%, V1c determinant-bound algebraic bridge ~91%,
  V1c two-sided determinant theorem 0%, Stage V1 ~64%, whole
  volume-comparison lane ~38%.
- 2026-07-08: added the first intrinsic-lowering bridge for the radial
  curvature term.  `Tensor/RSTensor/CotangentRiemannian.lean` now exposes
  `cotangentSharp_dualToCotangent_tangentFlat_gen` and
  `cotangentInner_dualToCotangent_tangentFlat_gen`, proving that metric
  lowering then raising recovers the original tangent vector and that the
  cotangent metric of two lowered vectors is the original tangent metric.
  `Volume/RadialGronwall.lean` now defines `radialCurvTermFlat` and packages
  `curv_sq_of_flat_Ioo` plus `exists_ode_Ico_of_flat`, so a square-root bound
  on the lowered curvature one-form feeds the existing `Ico` ODE producer.
  This still does not prove the actual curvature estimate.  Next target: bound
  `radialCurvTermFlat` through the intrinsic fibre-norm/orthonormal-frame API
  and convert that bound to the flat/cotangent square-root hypothesis.  Focused
  checks passed for the edited Lean files, and targeted
  `Tensor.RSTensor.CotangentRiemannian` build passed.  Targeted
  `Volume.RadialGronwall` build hit a performance/tooling wall: three attempts
  timed out and left stale Lake locks after the build process exited; the stale
  locks were released.  Current honest estimates: V1c Gronwall producer
  infrastructure ~75%, V1c determinant-bound algebraic bridge ~91%, V1c
  two-sided determinant theorem 0%, Stage V1 ~64%, whole volume-comparison
  lane ~38%.
- 2026-07-08: advanced the radial curvature-term bridge to the canonical
  lowered-Riemann/fibre-norm interface.  `Volume/RadialGronwall.lean`
  now has private bridges identifying evaluation and components of
  `radialCurvTermFlat` with `metricRm04StdAt g q J V V W`, and public wrappers
  `curv_sq_of_fiber_Ioo` and `exists_ode_Ico_of_fiber` converting an intrinsic
  `(0,1)` `normSq0S` square-root bound into the existing ODE producer.  This is
  still infrastructure, not the geometric curvature estimate itself.
  Follow-up 8b added `abs_flat_apply_le_rm04`, bounding any evaluation of the
  lowered radial term by the canonical `metricRm04At` fibre norm and the four
  slot lengths via `abs_apply_le_sqrt_normSq0S`.  Focused verification passed
  for `Volume.RadialGronwall`.  Follow-up 8c verified the reusable low-layer
  aggregation lemma `normSq0S_le_card_of_component_bound` in
  `Tensor/RSTensor/Tensor0SRiemannian/Comparison.lean` and consumed it in
  `Volume/RadialGronwall.lean` as `radialCurvTermFlat_normSq_le_card`.  The
  next target is to simplify and uniformly bound the four slot-length product
  from `abs_flat_apply_le_rm04` under orthonormal basis vectors,
  radial-velocity bounds, and Jacobi-field length hypotheses.  Follow-up 8d
  completed that packaging with checked bridges
  `radialCurvTermFlat_normSq_le_card_of_bounds`,
  `radialCurvTermFlat_sqrt_le_card_of_velocity_bound`,
  `radialCurvTermFlat_sqrt_le_K`, and `curv_sq_of_rm04_velocity_Ioo`.  The
  next target is to feed this Ioo curvature input through the existing
  `exists_ode_Ico` packaging layer, while keeping the producers for pointwise
  orthonormal bases, radial-velocity bounds, Rm04 coefficient bounds, and the
  endpoint `t = 0` ODE input separate.  Follow-up 8e added and verified
  `exists_ode_Ico_of_rm04_velocity`, closing that packaging step.  The current
  next target is to build one of the real geometric producers separately.
  Follow-up 8f added and verified the radial-speed producer:
  `radial_speed_sq_eq` exposes the Gauss-lemma constant-speed theorem in the
  local `radialCurve`/`curveVelocity` form, `radial_speed_le` turns a
  launch-speed bound into a uniform radial-velocity bound on `(0, b)`, and
  `exists_ode_Ico_of_rm04_launch` consumes it in the Rm04 ODE package after
  shrinking the radius by `expMapC2Radius`.  The current next target is now one
  of the remaining real producers, preferably the pointwise orthonormal-frame
  supply or the Rm04 coefficient bound, while the endpoint `t = 0` ODE input
  remains a visible separate gap.  Follow-up 8g added and verified the
  pointwise ON-basis and Rm04-norm packaging layer: the private
  `exists_gON_tangentBasis_E` supplies a pointwise `Fin (finrank E)` ON basis;
  `exists_ode_Ico_of_rm04` chooses those bases internally; and
  `exists_ode_Ico_of_rm04_norm` reduces the Rm04 coefficient input to
  `sqrt(normSq0S metricRm04At) <= R` plus the algebraic coefficient bound
  `sqrt(card) * R * Vb^2 <= K`.  The remaining gaps are now genuine producers:
  a radial-image Rm04 norm bound from explicit curvature hypotheses, and the
  endpoint `t = 0` ODE input.  The live search found no static volume-lane
  Rm04 radial-image bound and no checked endpoint `D_t^2 J(0)=0` or
  `IsJacobiAt`-at-`0` producer; `exists_radial_jacobi_deriv_radius` currently
  gives only `D_t J(0)=w`.  Follow-up 8h added and verified the endpoint-shape
  adapters: `ode_Ico_of_Ioo_d2` replaces the opaque endpoint inequality with
  the concrete input `D_t^2 J(0)=0`; `d2_zero_of_jac0` proves that endpoint
  `IsJacobiAt ... 0` implies this input because `J(0)=0`; and
  `exists_ode_rm04_d2` / `exists_ode_rm04_jac0` expose the high-level package
  with the endpoint producer in that concrete form.  This still does not prove
  endpoint Jacobi at `0`; `JacobiVariation.md` records that this needs
  continuity of `D^2J` at `0`, and no checked continuity/API producer is
  currently available.  Current honest estimates: V1c Gronwall producer
  infrastructure ~82%, V1c determinant-bound algebraic bridge ~91%, V1c
  two-sided determinant theorem 0%, Stage V1 ~66%, whole volume-comparison
  lane ~40%.  Follow-up 8i added and verified the region-wise Rm04 packaging:
  `rm04_Ioo_of_region` turns a `metricRm04At` fibre-norm bound on an ambient
  set `U` plus radial-segment inclusion into the `(0, b)` pointwise Rm04 input,
  and `exists_ode_rm04_on` threads that through the high-level Jacobi-endpoint
  ODE package.  This does not prove the radial-image inclusion or endpoint
  Jacobi producer.  The next Rm04-side target is now a normal-coordinate or
  bounded-curvature region predicate/inclusion that can feed
  `exists_ode_rm04_on`; the endpoint `IsJacobiAt ... 0` route remains blocked
  on missing `D^2J` continuity API.  Current honest estimates: V1c Gronwall
  producer infrastructure ~83%, V1c determinant-bound algebraic bridge ~91%,
  V1c two-sided determinant theorem 0%, Stage V1 ~67%, whole
  volume-comparison lane ~41%.  Follow-up 8j added and verified the first
  concrete radial-image inclusion producer: `radial_mem_expBall` shows that
  `‖x‖ < ρ` and `b ≤ 1` put the open radial segment inside the `expMap` image
  of `{v | ‖v‖ < ρ}`, and `exists_ode_expBall` consumes an Rm04 fibre-norm
  bound on that image.  The next Rm04-side target is to connect the intended
  curvature hypothesis to this `expMap`-ball image bound.  The endpoint
  `IsJacobiAt ... 0` route still needs the missing `D^2J` continuity/API
  bridge.  Current honest estimates: V1c Gronwall producer infrastructure
  ~85%, V1c determinant-bound algebraic bridge ~91%, V1c two-sided determinant
  theorem 0%, Stage V1 ~68%, whole volume-comparison lane ~42%.  Follow-up 8k
  added and verified the global-curvature-bound entry point:
  `rm04Exp_of_global` restricts a global
  `sqrt(normSq0S metricRm04At) <= R` hypothesis to every `expMap` ball image,
  and `exists_ode_global` threads that input through `exists_ode_expBall`.
  This closes the current Rm04-side packaging route for the global `‖Rm‖ <= R`
  hypothesis shape.  Remaining V1c producer gaps are endpoint
  `IsJacobiAt ... 0` and the `J`/`DJ` `chartRepAt` differentiability inputs.
  Current honest estimates: V1c Gronwall producer infrastructure ~87%, V1c
  determinant-bound algebraic bridge ~91%, V1c two-sided determinant theorem
  0%, Stage V1 ~69%, whole volume-comparison lane ~43%.  The first
  differentiability-side bridge is now checked in `Exponential/JacobiVariation`:
  `chartRep_congr_curve` exports the clamped-to-clean `chartRepAt` eventual
  equality transfer that had previously only existed inside
  `covDerivAlong_congr_curve`.  This does not yet prove the clean radial
  `hJdiff`/`hDJdiff` producer; the next regularity target is to rebuild the
  clamped variation from `exists_radial_jacobi_radius`, use the existing
  clamped variation-field differentiability lemmas, and transfer them with
  `chartRep_congr_curve`.  Current honest estimates: V1c Gronwall producer
  infrastructure ~88%, V1c determinant-bound algebraic bridge ~91%, V1c
  two-sided determinant theorem 0%, Stage V1 ~69%, whole
  volume-comparison lane ~43%.  Follow-up 8l added and verified the clean
  radial regularity producer: `Exponential/JacobiVariation.exists_jacobi_diff`
  exports `hJdiff`/`hDJdiff` for the clean radial objects on every capped
  interval `[0,b]`, and `Volume/RadialGronwall.exists_radialJacobi_diff` exposes
  it in the local `radialCurve` / packaged `radialJacobiField` vocabulary.
  This closes the current `J`/`DJ` `chartRepAt` differentiability producer.
  The remaining V1c producer gap is now the endpoint `IsJacobiAt ... 0` /
  `D_t^2 J(0)=0` input.  Current honest estimates: V1c Gronwall producer
  infrastructure ~90%, V1c determinant-bound algebraic bridge ~91%, V1c
  two-sided determinant theorem 0%, Stage V1 ~71%, whole
  volume-comparison lane ~45%.  Follow-up 8m audited the endpoint routes and
  found no local consumer-side proof: the interior Jacobi proof needs a
  two-sided germ at `0`, while the currently packaged expMap/maximal-geodesic
  rescale theorem is `[0,1]`-only; the normal-coordinate route lacks a checked
  radial-center acceleration API; and the lower chart-flow negative-time route
  would need a new sign/negative-scale bridge before it can feed
  `covDerivAlong`.  Follow-up 8n added and verified the low-layer radial
  endpoint API in `Exponential/IntrinsicExp.lean`: `exp_eq_intr_of_small`
  packages the existing small chart-fixed/intrinsic exponential agreement with
  intrinsic foot-in-source confinement; `exp_radial_eq_intr` proves the
  two-sided germ `s |-> expMap g p (s • u) = intrinsicGeodesic g hEnorm p u s`
  near `0`; `exp_radial_geo_zero` proves the center
  `HasGeodesicEquationAt` for the chart-fixed radial exponential curve; and
  `exp_radial_d2_zero` proves zero covariant radial acceleration at `0`, using
  `radialCurve_contMDiffAt2` for the `C²` input.  The remaining endpoint bridge
  is downstream consumption in `JacobiVariation` to close the concrete
  `D_t^2 J(0)=0` input.  Current honest estimates: V1c Gronwall producer
  infrastructure ~92%, V1c determinant-bound algebraic bridge ~91%, V1c
  two-sided determinant theorem 0%, Stage V1 ~72%, whole volume-comparison lane
  ~46%.  Follow-up 8o then consumed this endpoint acceleration in
  `Exponential/JacobiVariation.lean`: `clamped_slice_covDeriv_velocity_zero_at_zero`
  transfers the clamped radial slice at `0` to `exp_radial_d2_zero`, and
  `exists_jacobi_zero` proves the radius-packaged endpoint `IsJacobiAt ... 0`
  theorem for the clean radial variation.  The mathematical endpoint Jacobi
  producer is now checked.  The remaining bridge is Volume-layer packaging:
  combine `exists_jacobi_zero` with the local `radialJacobiField` vocabulary
  and `d2_zero_of_jac0` in a context that already carries the full
  `IsContinuousRiemannianBundle` / `FiberBundle` / `VectorBundle` instance
  chain.  Direct wrappers in `RadialGronwall` and `NormalChartMeasure` were
  tried and reverted because their public theorem heads exposed that instance
  plumbing.  Updated honest estimates: endpoint Jacobi theorem 100%; Volume
  packaged endpoint `D_t^2 J(0)=0` wrapper 0%; V1c Gronwall producer
  infrastructure ~94%, V1c determinant-bound algebraic bridge ~91%, V1c
  two-sided determinant theorem 0%, Stage V1 ~72%, whole volume-comparison lane
  ~47%.
- 2026-07-08 follow-up 8p: Volume-layer endpoint packaging landed for the
  Rm04-norm and ambient-region ODE packages.  `Volume/NormalChartMeasure.lean`
  now exposes `exists_radialJacobi_zero_radius`, the local
  `radialJacobiField` form of the checked endpoint `IsJacobiAt ... 0`
  producer.  `Volume/RadialGronwall.lean` now exposes `exists_ode_rm04`, which
  combines that endpoint radius with `exists_ode_rm04_jac0` and
  `d2_zero_of_jac0`, and `exists_ode_rm04_on` carries the same endpoint-closed
  package for ambient curvature-control regions.  The expMap-ball and global
  wrappers are intentionally still endpoint-explicit: making them
  endpoint-closed exposed a tangent-ball norm compatibility issue between the
  project default tangent norm and the `RiemannianBundle` scoped norm used by
  `hEnorm`.  The next target is either a narrow norm-set compatibility lemma
  for expMap-ball/global packaging or, more directly, consuming
  `exists_ode_rm04` in the remaining radial analytic package before returning
  to determinant bounds.  Focused verification passed for
  `Volume.NormalChartMeasure` and `Volume.RadialGronwall`; targeted
  `Volume.NormalChartMeasure` verification passed; targeted
  `Volume.RadialGronwall` was attempted only for `.olean` refresh but timed
  out after focused verification and left a stale Lake lock, which was
  released.  Updated honest estimates: endpoint Jacobi theorem 100%; Volume
  packaged endpoint Rm04/region ODE wrapper 100%; expMap-ball/global
  endpoint-closed wrappers 0%; V1c Gronwall producer infrastructure ~95%,
  V1c determinant-bound algebraic bridge ~91%; V1c two-sided determinant
  theorem 0%; Stage V1 ~73%; whole volume-comparison lane ~48%.
- 2026-07-08 follow-up 8q: the endpoint-closed Rm04 ODE package is now
  consumed by the first radial analytic packages in `Volume/RadialGronwall.lean`.
  `exists_rm04_data` combines the checked radial `chartRepAt`
  differentiability radius with `exists_ode_rm04`, producing `hJdiff`,
  `hDJdiff`, and `hODE` under one radius.  `exists_rm04_basis` specializes
  that to scaled fixed model-basis directions, `exists_rm04_pack` synchronizes
  it with the small-radius `D_tJ(0)=w` producer, and
  `exists_fin_le_rm04` feeds the package into the existing upper fixed-basis
  endpoint bound.  This removes the repeated analytic hypotheses from that
  upper fixed-basis route; it does not solve the lower unit-direction route,
  parallel-frame supply, scalar model estimates, launch/Rm04 coefficient
  inputs, or the final determinant theorem.  The next target is the matching
  lower unit-direction package using the same endpoint-closed Rm04 data, or a
  shared unit-direction data wrapper, before determinant/eigenvalue assembly.
  Focused verification passed for `Volume.RadialGronwall`; no targeted module
  refresh was run in this pass.  Updated honest estimates: V1c Gronwall
  producer infrastructure ~96%; V1c determinant-bound algebraic bridge ~91%;
  V1c two-sided determinant theorem 0%; Stage V1 ~74%; whole
  volume-comparison lane ~49%.
- 2026-07-08 follow-up 8r: the matching lower unit-direction endpoint producer
  landed in `Volume/RadialGronwall.lean`.  `exists_dir_ge_rm04` consumes the
  endpoint-closed Rm04 data and the small-radius radial-Jacobi derivative
  producer through `radialJacobi_dir_ge_of_scaled_radius`, giving the squared
  lower endpoint bound for every unit coefficient direction without requiring
  callers to pass `hJdiff`/`hDJdiff`/`hODE`/`hderivRadius`.  Together with
  `exists_fin_le_rm04`, the radial Gronwall layer now has both the upper
  fixed-basis and lower unit-direction endpoint producer wrappers.  This is
  still not the V1c determinant theorem: the next target is to consume these
  wrappers in `Volume/JacobianBounds.lean` through the existing
  `normalDensity_le_of_radial_length_bound` and
  `normalDensity_ge_of_dir_bound` consumers.  That downstream edit should wait
  for a successful `Volume.RadialGronwall` `.olean` refresh, because previous
  targeted refreshes of that module timed out.  Focused verification passed for
  `Volume.RadialGronwall`; no targeted module refresh was run in this pass.
  Updated honest estimates: V1c Gronwall producer infrastructure ~97%; V1c
  determinant-bound algebraic bridge ~91%; V1c two-sided determinant theorem
  0%; Stage V1 ~75%; whole volume-comparison lane ~50%.
- 2026-07-08 follow-up 8s: the radial endpoint wrappers are now consumed by the
  pointwise density layer.  A targeted refresh of
  `Volume.RadialGronwall` succeeded, then `Volume/JacobianBounds.lean` added
  `exists_dens_le_rm04` and `exists_dens_ge_rm04`, which feed
  `exists_fin_le_rm04` and `exists_dir_ge_rm04` into the existing
  upper endpoint-length and lower unit-direction density consumers.  This
  removes the repeated `hJdiff`/`hDJdiff`/`hODE`/`hderivRadius` hypotheses from
  the direct pointwise density wrappers, but it still does not supply
  parallel-frame data, scalar model estimates, launch/Rm04 coefficient bounds,
  or a stated two-sided capped Jacobian theorem.  Next target: assemble the
  first shared capped-density hypothesis package around `exists_dens_le_rm04`
  and `exists_dens_ge_rm04`, keeping the theorem statement separate until the
  package is honest.  Focused and targeted verification passed for
  `Volume.JacobianBounds` after the downstream wrappers.  Current honest estimates: V1c Gronwall
  producer infrastructure ~97%; V1c determinant-bound algebraic bridge ~92%;
  V1c two-sided determinant theorem 0%; Stage V1 ~75%; whole
  volume-comparison lane ~50%.
- 2026-07-08 follow-up 8t: the pointwise density layer now has a shared-radius
  two-sided wrapper.  `Volume/JacobianBounds.lean` added
  `exists_dens_two_rm04`, which takes the minimum of the upper and lower Rm04
  density radii and returns both pointwise inequalities under one common
  hypothesis package.  This is not the final V1c theorem: it still assumes
  parallel-frame data, scalar model upper/lower estimates, launch/Rm04
  coefficient bounds, source/C2-radius membership, and explicit smallness for
  the scaled basis and unit directions.  Next target: consume this two-sided
  pointwise density wrapper in the existing `Volume.BallVolume` local
  two-sided volume wrappers, without hiding those geometric inputs.  Focused
  and targeted verification passed for `Volume.JacobianBounds`.  Current
  honest estimates: V1c Gronwall producer infrastructure ~97%; V1c
  determinant-bound algebraic bridge ~93%; V1c two-sided determinant theorem
  0%; Stage V1 ~76%; whole volume-comparison lane ~51%.
- 2026-07-08 follow-up 8u: the two-sided density package is now consumed by
  the local volume layer.  `Volume/BallVolume.lean` added
  `vol_le_ball_of_density`, `metricBall_vol_scale_density`,
  `exists_metricBall_vol_le_dens_local`, `exists_vol_two_dens`, and
  `exists_vol_two_rm04`.  The last theorem feeds
  `JacobianBounds.exists_dens_two_rm04` into the realized metric-ball
  two-sided local volume shell, while leaving the honest geometric inputs
  explicit: parallel-frame family, radial `chartRepAt` differentiability,
  scalar upper/lower model estimates, launch/Rm04 coefficient bounds, C2/source
  radii, and smallness of scaled basis/unit directions.  This is still not the
  final V1d theorem with explicit injectivity/capped constants.  Next target:
  package those remaining geometric inputs uniformly over a model ball and
  choose the final radius/scale constants.  Focused and targeted verification
  passed for `Volume.BallVolume`.  Current honest estimates: V1c Gronwall
  producer infrastructure ~97%; V1c determinant-bound algebraic bridge ~93%;
  V1d local volume shell machinery ~82%; V1c two-sided determinant theorem 0%;
  final V1d two-sided ball-volume theorem 0%; Stage V1 ~76%; whole
  volume-comparison lane ~51%.
- 2026-07-08 follow-up 8v: the remaining Rm04 local-volume inputs now have an
  explicit data/proof package interface.  `Volume/BallVolume.lean` added
  `Rm04FrameData`, `IsRm04VolHyp`, and `exists_vol_rm04_pkg`.  The data record
  stores the finite moving-frame family over the model ball; the proof
  predicate records the scalar/radius, launch, curvature, regularity,
  parallel-frame, orthonormality, differentiability, and scalar-model fields
  needed by `exists_vol_two_rm04`.  This is only packaging: it proves no new
  frame existence, scalar model estimate, or explicit constant choice.  Next
  target: produce one honest field family for `IsRm04VolHyp`, starting with
  radius/scale bookkeeping if possible before the harder parallel-frame and
  scalar-model producers.  Focused and targeted verification passed for
  `Volume.BallVolume`.  Current honest estimates: V1c Gronwall producer
  infrastructure ~97%; V1c determinant-bound algebraic bridge ~93%; V1d local
  volume shell/package machinery ~84%; V1c two-sided determinant theorem 0%;
  final V1d two-sided ball-volume theorem 0%; Stage V1 ~76%; whole
  volume-comparison lane ~51%.
- 2026-07-08 follow-up 8w: one `IsRm04VolHyp` field family now has a producer.
  `Volume/RadialGronwall.lean` added `basisUnitScaleSmall`, combining the
  earlier fixed-basis and unit-direction scale lemmas into one positive scale
  that makes both `a • e_k` and `a • sum_i v_i e_i` small for any prescribed
  positive radius.  This directly feeds the two smallness fields in the Rm04
  volume proof package.  It is only radius/scale bookkeeping: the parallel-frame
  data, scalar model upper/lower estimates, launch/Rm04 coefficient bounds, and
  final explicit capped constants remain open.  Focused and targeted
  verification passed for `Volume.RadialGronwall`.  Current honest estimates:
  V1c Gronwall producer infrastructure ~98%; V1c determinant-bound algebraic
  bridge ~93%; V1d local volume shell/package machinery ~85%; V1c two-sided
  determinant theorem 0%; final V1d two-sided ball-volume theorem 0%; Stage V1
  ~77%; whole volume-comparison lane ~52%.
- 2026-07-08 follow-up 8x: the scale producer is now connected to the volume
  package.  `Volume/BallVolume.lean` added `exists_rm04_scale` and
  `exists_vol_scale`, which choose the common positive scale using
  `basisUnitScaleSmall`, fill only the `ha`/basis-smallness/unit-direction
  smallness fields of `IsRm04VolHyp`, and then consume `exists_vol_rm04_pkg`.
  This is still interface/proof-package bookkeeping: every non-scale field
  (parallel frame, scalar upper/lower model estimates, launch/Rm04 coefficient
  bounds, C2/source radii, and final explicit constants) remains explicit.
  Focused verification with `-NoLakeLock` and targeted module refresh passed
  for `Volume.BallVolume`.  Next target: produce or package one non-scale field
  family for `IsRm04VolHyp`, preferably launch/Rm04 coefficient bounds or the
  scalar initial/model inequalities before attempting the parallel-frame
  producer.  Current honest estimates: V1c Gronwall producer infrastructure
  ~98%; V1c determinant-bound algebraic bridge ~93%; V1d local volume
  shell/package machinery ~86%; V1c two-sided determinant theorem 0%; final V1d
  two-sided ball-volume theorem 0%; Stage V1 ~78%; whole volume-comparison lane
  ~53%.
- 2026-07-08 follow-up 8y: the fixed-basis upper scalar/model fields now have
  a checked scaling bridge.  `Volume/RadialGronwall.lean` added
  `model_le_smul` and `basisModel_le_smul`, which transport an unscaled
  fixed-basis center-length bound and unscaled upper Gronwall model inequality
  to the scaled `hinit`/`hmodelLe` shape used by `IsRm04VolHyp` when the package
  parameter is chosen as `A = a * A0`.  This proves no unscaled basis bound and
  chooses no explicit constants; it only removes the scalar algebra from the
  later geometric producer.  Focused verification with `-NoLakeLock` and
  targeted module refresh passed for `Volume.RadialGronwall`.  Next target:
  package launch/Rm04 coefficient bounds or begin the parallel-frame producer;
  the latter is the first genuinely geometric field family still visible.
  Current honest estimates: V1c Gronwall producer infrastructure ~99%; V1c
  determinant-bound algebraic bridge ~93%; V1d local volume shell/package
  machinery ~86%; V1c two-sided determinant theorem 0%; final V1d two-sided
  ball-volume theorem 0%; Stage V1 ~78%; whole volume-comparison lane ~53%.
- 2026-07-08 follow-up 8z inspection: the next real producer is not a new
  scalar wrapper.  `Volume/RadialGronwall.lean` already has
  `exists_radialFrame`, which produces a full parallel orthonormal frame for
  one radial curve from `C²` radial-curve regularity and `0 < b`.  The next
  concrete target is to lift/thread that single-curve producer into the
  `BallVolume.Rm04FrameData` shape uniformly over `w ∈ Metric.ball 0 R`, while
  preserving the associated per-`w` regularity and `chartRepAt`
  differentiability fields.  This is the first genuine geometric packaging
  frontier after the scale and scalar-model algebra bricks; no Lean declaration
  was added in this inspection pass.
- 2026-07-08 follow-up 8aa: the single-radial-curve frame producer is now
  connected to the V1d volume package.  `Volume/BallVolume.lean` added
  `exists_rm04FrameData`, which chooses `exists_radialFrame` for each
  `w in Metric.ball 0 R`, packages the results into one `Rm04FrameData` record
  with uniform index type `ULift (Fin n)`, and returns the frame cardinality,
  parallelism, orthonormality, and `chartRepAt` differentiability fields needed
  downstream.  This is conditional geometric packaging: it assumes per-`w`
  radial `C^2` regularity and still does not prove launch/Rm04 coefficient
  bounds, scalar upper/lower model inequalities, final capped constants, or the
  final V1d two-sided ball-volume theorem.  Focused verification with
  `-NoLakeLock` and targeted module refresh passed for `Volume.BallVolume`.
  Next target: package radial-curve regularity over the model ball into the
  `hgamma2` input, preferably by reusing the existing
  `radialCurve_contMDiffOn_Icc` / `radialCurve_contMDiffAt2` route while
  keeping the local/global regularity mismatch explicit.  Current honest
  estimates: V1c Gronwall producer infrastructure ~99%; V1c determinant-bound
  algebraic bridge ~93%; V1d local volume shell/package machinery ~88%; V1c
  two-sided determinant theorem 0%; final V1d two-sided ball-volume theorem
  0%; Stage V1 ~79%; whole volume-comparison lane ~54%.
- 2026-07-08 follow-up 8ab: the model-ball local radial regularity producer is
  now checked and connected to the V1d package.  `Volume/RadialGronwall.lean`
  added `radialC2OnBallIcc`, proving `ContMDiffOn` `C^2` regularity on
  `Icc 0 b` for every `w in Metric.ball 0 R` from
  `R <= expMapC2Radius g p` and `b <= 1`.  `Volume/BallVolume.lean` added
  `IsRm04VolHyp.radialC2`, exposing that local regularity from the package's
  `hRC2` and `hb1` fields.  This resolves the honest local regularity
  producer, but it does not supply the global `ContMDiff` input still required
  by the current `exists_parallel_frame` / `exists_rm04FrameData` route.
  Focused checks with no global Lake lock and targeted module refreshes passed
  for `Volume.RadialGronwall` and `Volume.BallVolume`.  Next target: build the
  local-on-`Icc` parallel-frame API, or an honest smooth-extension bridge, so
  the checked local radial regularity can feed the frame-data producer without
  pretending it is global in time.  Current honest estimates: V1c Gronwall
  producer infrastructure ~99%; V1c determinant-bound algebraic bridge ~93%;
  V1d local volume shell/package machinery ~89%; V1c two-sided determinant
  theorem 0%; final V1d two-sided ball-volume theorem 0%; Stage V1 ~79%; whole
  volume-comparison lane ~54%.
- 2026-07-08 follow-up 8ac: started the honest smooth-extension bridge.
  `Variation/PerpFrame.lean` added `exists_time_clip`, a smooth bounded time
  reparametrization equal to the identity on `Icc 0 L`.
  `Volume/RadialGronwall.lean` added `exists_radial_clip`, which chooses such
  a time clip so the clipped radial launch vectors stay inside
  `expMapC2Radius g p` for all time while remaining unchanged on `Icc 0 b`.
  This is still infrastructure, not the frame producer itself: it does not yet
  prove global `ContMDiff` of the clipped radial curve or localize
  `exists_parallel_frame`.  Focused checks with no global Lake lock passed for
  the touched files; `PerpFrame` was also refreshed once as an upstream module
  because `RadialGronwall` consumed the new exported declaration.  No
  `RadialGronwall` targeted refresh was run because no downstream consumer
  used the new declaration yet.  Next target: prove the clipped radial curve is
  globally smooth, or add the local-on-`Icc` frame API directly.  Current
  honest estimates: V1c Gronwall producer infrastructure ~99%; V1c
  determinant-bound algebraic bridge ~93%; V1d local volume shell/package
  machinery ~89%; V1c two-sided determinant theorem 0%; final V1d two-sided
  ball-volume theorem 0%; Stage V1 ~79%; whole volume-comparison lane ~54%.
- 2026-07-08 follow-up 8ad: completed the clipped radial global-smoothness
  bridge.  `Volume/RadialGronwall.lean` added `radial_clip_contMDiff`, proving
  a clipped radial exponential curve is globally `C^2` when the time clip is
  smooth and all clipped launch vectors remain inside `expMapC2Radius g p`.
  It also added `exists_radial_ext`, which packages `exists_radial_clip` into
  a globally `C^2` curve equal to the usual radial curve on `Icc 0 b`.  This
  resolves the smooth-extension part of the local/global regularity mismatch,
  but still does not produce `Rm04FrameData`: the remaining frame-data
  frontier is dependent transport of the frame from the smooth extension back
  to the original radial curve on the equality interval, or a localized
  `Icc`-frame API.  Focused verification with no global Lake lock passed for
  `Volume.RadialGronwall`; no targeted refresh was run because no downstream
  file consumed these new declarations yet.  Current honest estimates remain:
  V1c Gronwall producer infrastructure ~99%; V1c determinant-bound algebraic
  bridge ~93%; V1d local volume shell/package machinery ~89%; V1c two-sided
  determinant theorem 0%; final V1d two-sided ball-volume theorem 0%; Stage V1
  ~79%; whole volume-comparison lane ~54%.
- 2026-07-08 follow-up 8ae: packaged smooth radial extensions and frames along
  them without pretending they are frames along the original radial curve.
  `Volume/BallVolume.lean` added `RadialExtData` and
  `exists_radialExtData`, producing a globally `C^2` extension for each launch
  vector in `Metric.ball 0 R` that agrees with the original radial curve on
  `Icc 0 b`.  It also added `ExtFrameData` and `exists_extFrameData`, using
  the generic `exists_parallel_frame` to construct parallel orthonormal frame
  data along those extension curves.  This is the honest intermediate layer
  after the smooth-extension bridge: it still does not close `Rm04FrameData`.
  The next real bridge is either a localized `Icc` frame/volume consumer API,
  or a dependent transport adapter from extension-frame data back to the
  original radial curve that preserves endpoint differentiability and
  `covDerivAlong` hypotheses.  Focused verification with no global Lake lock
  passed for `Volume.BallVolume` after one targeted upstream refresh of
  `Volume.RadialGronwall`.  Current honest estimates remain: V1c Gronwall
  producer infrastructure ~99%; V1c determinant-bound algebraic bridge ~93%;
  V1d local volume shell/package machinery ~89%; V1c two-sided determinant
  theorem 0%; final V1d two-sided ball-volume theorem 0%; Stage V1 ~79%; whole
  volume-comparison lane ~54%.
- 2026-07-08 follow-up 8af: closed the smooth-extension frame route.
  `Variation/PerpFrame.lean` added `exists_time_window_clip`, a bounded smooth
  time clip equal to identity on any closed window strictly inside
  `(-lam, lam)`.  `Volume/RadialGronwall.lean` added `exists_rclip_nbhd` and
  `exists_rext_nbhd`, producing globally `C^2` radial extensions that agree
  with the original radial curve on a neighborhood `Icc (-eps) (b + eps)` of
  the comparison interval.  `Volume/BallVolume.lean` strengthened
  `RadialExtData` with that neighborhood equality and added the germ-transfer
  bridge from extension frames back to original radial curves:
  `radialExt_eventuallyEq`, `radialFrameOfExt_evEq`,
  `rm04FrameDataOfExt_par`, `rm04FrameDataOfExt_diff`, and
  `rm04FrameDataOfExt_ON`.  The new `exists_rm04FrameData_radius` now produces
  the full `Rm04FrameData` package from `0 < b`, `b <= 1`, and
  `R <= expMapC2Radius g p`, without the old fake-global radial-curve
  regularity assumption.  Focused checks with no global Lake lock passed for
  the touched files; targeted module refreshes were used only for exported
  upstream declarations consumed downstream.

  Current honest estimates: V1c Gronwall producer infrastructure ~99%; V1c
  determinant-bound algebraic bridge ~93%; V1d local volume shell/package
  machinery ~91%; V1c two-sided determinant theorem 0%; final V1d two-sided
  ball-volume theorem 0%; Stage V1 ~80%; whole volume-comparison lane ~55%.
  Next target: thread `exists_rm04FrameData_radius` into the `IsRm04VolHyp`
  assembly path, then build the remaining real producers for launch bounds,
  Rm04 curvature coefficient bounds, scalar model inequalities, and final
  capped constants.
- 2026-07-08 follow-up 8ag: threaded the radius-form frame producer into the
  volume assembly wrappers.  `Volume/BallVolume.lean` added
  `exists_rm04_hyp`, which constructs `IsRm04VolHyp` while automatically
  obtaining `Rm04FrameData` from `exists_rm04FrameData_radius`.  It also added
  `exists_vol_frame`, a wrapper around `exists_vol_scale` that chooses both
  the common scale and the frame data automatically.  These are packaging
  bridges, not final comparison theorems: the caller still supplies the real
  non-frame producers for launch control, Rm04 coefficient bounds, the
  radial-curve regularity field, and scalar model continuation/inequalities.
  The checked proof fixed the internal frame-index universe explicitly at `0`
  for the existing scale/frame producers; this was an elaboration repair, not
  a mathematical frontier.

  Focused verification with no global Lake lock passed for
  `Volume.BallVolume`.  Current honest estimates: V1c Gronwall producer
  infrastructure ~99%; V1c determinant-bound algebraic bridge ~93%; V1d local
  volume shell/package machinery ~92%; V1c two-sided determinant theorem 0%;
  final V1d two-sided ball-volume theorem 0%; Stage V1 ~80%; whole
  volume-comparison lane ~55%.  Next target: choose and close one remaining
  non-frame producer bridge, preferably a scalar/Rm04 package already close in
  `RadialGronwall`, while keeping the global-vs-local radial-curve regularity
  mismatch visible.
- 2026-07-08 follow-up 8ah: closed a narrow scalar-model producer bridge.
  `Volume/BallVolume.lean` added `scalarModel_smul`, which combines the
  existing `RadialGronwall` lemmas `basisModel_le_smul` and
  `dirModel_ge_smul` to scale fixed-basis upper scalar data and
  unit-direction lower scalar data into the three scalar fields consumed by
  `IsRm04VolHyp`.  It also added `exists_rm04_scalar`, which constructs the
  Rm04 volume hypothesis package with radius-produced frame data and internally
  scaled scalar fields.  This removes scalar packaging from the fixed-scale
  `IsRm04VolHyp` assembly path, but it does not prove the final volume
  comparison theorem and it does not hide the remaining geometric producers.

  Focused verification with no global Lake lock passed for
  `Volume.BallVolume`; no targeted module refresh was needed because no
  downstream file consumed the new declarations yet.  Current honest
  estimates: V1c Gronwall producer infrastructure ~99%; V1c
  determinant-bound algebraic bridge ~93%; V1d local volume shell/package
  machinery ~93%; V1c two-sided determinant theorem 0%; final V1d two-sided
  ball-volume theorem 0%; Stage V1 ~80%; whole volume-comparison lane ~56%.
  Next target: either thread this fixed-scale scalar bridge into a volume
  wrapper that chooses the scale-dependent upper constant honestly, or close
  one of the remaining geometric producer fields (`hlaunch`, `hKbound`, `hRm`,
  or the still-visible radial-curve regularity input).
- 2026-07-08 follow-up 8ai: threaded the scalar bridge into the volume wrapper
  and removed the explicit launch-speed producer from the newest interface.
  `Volume/BallVolume.lean` added `exists_vol_scalar`, which bypasses the older
  `exists_vol_scale` continuation shape, chooses the common small scale
  directly, invokes `exists_rm04_scalar`, and exposes unscaled scalar model
  data instead of the three scale-dependent scalar fields.  It then added
  `exists_vol_launch`, which sets `Vb := rho` and uses the already-present
  `hρball` radius hypothesis to prove the launch-speed bound.  The resulting
  coefficient condition is honest and explicit:
  `sqrt(card) * Rm * rho^2 <= K`.

  Focused verification with no global Lake lock passed for
  `Volume.BallVolume`.  An attempted op-norm launch route failed at
  typeclass synthesis for `||g.inner p||`; it was abandoned in favor of the
  simpler radius-bound route, leaving no unresolved Lean error.  Current honest
  estimates: V1c Gronwall producer infrastructure ~99%; V1c
  determinant-bound algebraic bridge ~93%; V1d local volume shell/package
  machinery ~94%; V1c two-sided determinant theorem 0%; final V1d two-sided
  ball-volume theorem 0%; Stage V1 ~81%; whole volume-comparison lane ~57%.
  Next target: close a real remaining producer, most likely the Rm04
  coefficient field or the still-visible radial-curve regularity input, before
  attempting final capped constants.
- 2026-07-08 follow-up 8aj: closed the algebraic Rm04 coefficient bridge in
  the latest volume wrapper.  `Volume/BallVolume.lean` added
  `exists_vol_coeff`, which sets
  `K = sqrt(card (Fin 1 -> Fin n)) * Rm * rho^2` and consumes
  `exists_vol_launch`; callers no longer supply a separate `hKbound` field.
  The scalar model assumptions are still explicit, now at that chosen
  coefficient constant, so this does not hide the analytic scalar producer.
  The first attempted statement used a theorem-local `let K := ...` binder and
  misaligned introduced hypotheses; the checked version expands the coefficient
  expression directly in the statement.

  Focused verification with no global Lake lock passed for
  `Volume.BallVolume`.  Current honest estimates: V1c Gronwall producer
  infrastructure ~99%; V1c determinant-bound algebraic bridge ~93%; V1d local
  volume shell/package machinery ~95%; V1c two-sided determinant theorem 0%;
  final V1d two-sided ball-volume theorem 0%; Stage V1 ~81%; whole
  volume-comparison lane ~58%.  Next target: replace the radial-image `hRm`
  input by a cleaner global or region Rm04 norm-bound producer, or confront
  the still-visible radial-curve regularity input.
- 2026-07-08 follow-up 8ak: replaced the radial-image Rm04 input by reusable
  region/global norm-bound wrappers.  `Volume/BallVolume.lean` added
  `exists_vol_regionRm`, which takes a region `U`, radial-segment inclusion in
  `U`, and a bound for `sqrt(normSq0S metricRm04At)` on `U`, then supplies the
  old radial-image `hRm` field to `exists_vol_coeff`.  It also added
  `exists_vol_globalRm` as the `U = univ` specialization.  These wrappers do
  not prove curvature boundedness from compactness or continuity; they give the
  volume lane the intended theorem-facing curvature-bound vocabulary while
  keeping the scalar model assumptions and the radial-curve `C^1` input
  explicit.

  Focused verification with no global Lake lock passed for
  `Volume.BallVolume`.  The remaining radial-curve regularity route was
  inspected: the available exponential-map smoothness APIs prove local
  `ContMDiffAt` / `ContMDiffOn` on the small comparison interval, but the
  current `radialJacobi_bounds` consumer still requires global `ContMDiff` of
  the original radial curve.  This is not a direct local producer; the next
  honest target is either a localized Gronwall/Jacobian consumer or a
  smooth-extension transport interface that removes the global-regularity
  assumption downstream.  Current honest estimates: V1c Gronwall producer
  infrastructure ~99%; V1c determinant-bound algebraic bridge ~93%; V1d local
  volume shell/package machinery ~96%; V1c two-sided determinant theorem 0%;
  final V1d two-sided ball-volume theorem 0%; Stage V1 ~82%; whole
  volume-comparison lane ~59%.
- 2026-07-08 follow-up 8al: started the localized Gronwall route rather than a
  smooth-extension transport route.  `Variation/FirstVariation.lean` added
  `inner_deriv_at`; `Variation/CovariantGronwall.lean` added
  `covGronwall_bounds_at` / `covGronwall_ne_zero_at` with compatibility
  wrappers preserving the old global names; `Volume/RadialGronwall.lean` added
  `radialJacobi_bounds_at` plus `radialCurve_contMDiffAt_Icc`.  Ordinary
  focused checks were run with no global Lake lock.  One minimal targeted
  refresh of `Variation.CovariantGronwall` was needed so downstream imports
  could see the new exported theorem.

  This removes the global radial-curve regularity assumption at the first
  Gronwall specialization layer, but not yet from the top-level volume
  wrappers.  The current blocker is propagation, not mathematics: the `_at`
  interface must be threaded through `radialJacobi_one_bounds`, one-sided
  endpoint lemmas, finite-direction wrappers, and the density layer before
  `BallVolume.IsRm04VolHyp.hγ` can be changed from global `ContMDiff` to local
  pointwise regularity.  Current honest estimates: V1c Gronwall producer
  infrastructure ~99.5%; V1c determinant-bound algebraic bridge ~93%; V1d local
  volume shell/package machinery ~96%; V1c two-sided determinant theorem 0%;
  final V1d two-sided ball-volume theorem 0%; Stage V1 ~82%; whole
  volume-comparison lane ~59%.  Next target: add and verify
  `radialJacobi_one_bounds_at`, then continue the `_at` thread through the
  finite/density consumers before editing `BallVolume` package fields.

- 2026-07-08 follow-up 8am: completed the `_at` propagation through
  `Volume/RadialGronwall.lean` endpoint and Rm04 package wrappers.  The file
  now has localized interfaces for the one-sided, squared, unit-direction,
  finite-basis, scaled-radius, and packaged Rm04 endpoints, including
  `exists_fin_le_rm04_at` and `exists_dir_ge_rm04_at`; the old global names
  are compatibility wrappers using `hγ.contMDiffAt`.  Focused verification
  passed with `lake-locked check -NoLakeLock`; no targeted module refresh was
  run because no downstream file has consumed the new exported declarations
  yet.

  This removes the global radial-curve regularity assumption from the
  RadialGronwall consumer stack, but it has not yet changed the density or
  volume package APIs.  Next target: consume `exists_fin_le_rm04_at` /
  `exists_dir_ge_rm04_at` in the density and `Volume.BallVolume`
  `IsRm04VolHyp` layer, replacing the remaining global `ContMDiff` package
  field with the checked local pointwise radial-curve regularity.  Current
  honest estimates: V1c Gronwall producer infrastructure ~99.7%; V1c
  determinant-bound algebraic bridge ~93%; V1d local volume shell/package
  machinery ~96.5%; V1c two-sided determinant theorem 0%; final V1d two-sided
  ball-volume theorem 0%; Stage V1 ~82%; whole volume-comparison lane ~60%.

- 2026-07-08 follow-up 8an: consumed the localized regularity interfaces
  through `Volume/JacobianBounds.lean` and `Volume/BallVolume.lean`.
  `JacobianBounds` now has `exists_dens_le_rm04_at`,
  `exists_dens_ge_rm04_at`, and `exists_dens_two_rm04_at`, with old global
  names preserved as compatibility wrappers.  `BallVolume.IsRm04VolHyp.hγ`
  now stores the local pointwise `ContMDiffAt` field on `Icc 0 b`, and
  `exists_vol_two_rm04_at` / `exists_vol_rm04_pkg` consume the localized
  density package directly; old global volume entrypoints convert by
  `hγ.contMDiffAt`.

  Focused checks passed for `JacobianBounds.lean` and `BallVolume.lean`; a
  targeted refresh of `Volume.JacobianBounds` passed because `BallVolume`
  needed the newly exported density declarations.  The local/global
  regularity mismatch is now removed from the current Gronwall-density-volume
  package stack, but the final capped V1d theorem is still not stated/proved.
  Next target: fill the new local `IsRm04VolHyp.hγ` field automatically from
  the existing radius field via `IsRm04VolHyp.radialC2` /
  `radialCurve_contMDiffAt_Icc`, then continue removing manual package fields
  one honest producer at a time.  Current honest estimates: V1c Gronwall
  producer infrastructure ~99.7%; V1c determinant-bound algebraic bridge
  ~93.5%; V1d local volume shell/package machinery ~97%; V1c two-sided
  determinant theorem 0%; final V1d two-sided ball-volume theorem 0%; Stage V1
  ~83%; whole volume-comparison lane ~61%.

- 2026-07-08 follow-up 8ao: completed the local radial-curve regularity
  producer for the current volume package stack.  `Volume/BallVolume.lean`
  added `radialC1AtBall`, deriving the local pointwise `ContMDiffAt` field
  on `Metric.ball 0 R` and `Icc 0 b` from `R <= expMapC2Radius g p` and
  `b <= 1` via `radialCurve_contMDiffAt_Icc`.  The constructors
  `exists_rm04_hyp` and `exists_vol_frame` now fill `IsRm04VolHyp.hγ`
  internally, and the higher wrapper chain through `exists_vol_globalRm` no
  longer exposes any radial-curve regularity input.  The old compatibility
  theorem `exists_vol_two_rm04` remains available for callers that still have
  global `ContMDiff`.

  Focused verification with no global Lake lock passed for
  `Volume.BallVolume`; no targeted module refresh was needed.  Current honest
  estimates: V1c Gronwall producer infrastructure ~99.8%; V1c
  determinant-bound algebraic bridge ~93.5%; V1d local volume shell/package
  machinery ~97.3%; V1c two-sided determinant theorem 0%; final V1d
  two-sided ball-volume theorem 0%; Stage V1 ~83%; whole volume-comparison
  lane ~61.5%.  Next target: either add the next capped wrapper above
  `exists_vol_globalRm` or close the scalar/capped-constant inputs that it
  still exposes; curvature boundedness should remain an honest theorem input
  until a compactness/continuity producer is proved.

- 2026-07-08 follow-up 8ap: added the next time-one wrapper above the global
  Rm04 volume route.  `Volume/BallVolume.lean` now has
  `exists_vol_globalRm1`, which specializes `exists_vol_globalRm` to `b := 1`.
  This removes a redundant theorem-facing time parameter because the parent
  interface already required both `b <= 1` and `1 <= b`.  The wrapper does not
  prove new scalar or curvature estimates; it preserves the global Rm04 bound,
  source/radius hypotheses, and scalar model inequalities as honest inputs.

  Focused verification with no global Lake lock passed for
  `Volume.BallVolume`; no targeted module refresh was needed.  Current honest
  estimates: V1c Gronwall producer infrastructure ~99.8%; V1c
  determinant-bound algebraic bridge ~93.5%; V1d local volume shell/package
  machinery ~97.6%; V1c two-sided determinant theorem 0%; final V1d two-sided
  ball-volume theorem 0%; Stage V1 ~83.3%; whole volume-comparison lane ~62%.
  Next target: add a genuine capped-radius wrapper above
  `exists_vol_globalRm1`, or discharge the remaining scalar model inequalities
  using a reusable smallness/positivity lemma.  Do not hide the global Rm04
  boundedness input until a compactness or continuity producer exists.

- 2026-07-08 follow-up 8aq: audited the next capped-radius/scalar route above
  `exists_vol_globalRm1` and found a real missing scalar API rather than a
  local wrapper.  A direct radius cap is not currently local because the
  available model/`g_p` comparison in `BallVolume.lean` controls Euclidean norm
  from `sqrt(g.inner p w w)`, not the upper `g_p`-length bound needed for
  `hρball`.  The existing `exists_dirModel_ge` route chooses a small time
  `b`, while the current theorem-facing route is already specialized to
  `b = 1`.  The available Gronwall smallness lemmas provide monotonicity,
  scalar scaling, and small-time existence, but not the time-one small-`K`
  theorem needed to close the lower scalar model at fixed time.

  Next target: prove the pure scalar time-one smallness bridge before adding
  another final-looking volume wrapper.  The desired producer should use the
  unit-coefficient lower/upper initial bounds and a sufficiently small
  coefficient `K = sqrt(card) * Rm * rho^2` to produce the lower scalar model
  inequality for every unit coefficient vector at `b = 1`.  Until then,
  `exists_vol_globalRm1` correctly leaves the scalar model inequalities
  explicit.

- 2026-07-08 follow-up 8ar: closed the time-one lower scalar model producer and
  consumed it in the global Rm04 volume route.  `Analysis/ODE/SecondOrderGronwall.lean`
  added `exists_gron_smallK`, a pure scalar lemma choosing a positive
  coefficient cap so the endpoint-time `1` Gronwall error is dominated.
  `Volume/RadialGronwall.lean` added `exists_dirModel_ge1`, which uses the
  unit-coefficient lower/upper initial bounds to produce the lower scalar model
  inequality for every unit coefficient vector whenever `0 <= k <= K`.
  `Volume/BallVolume.lean` added `exists_vol_rm1_ge`, which chooses the
  coefficient cap and endpoint constant `B`, discharges `hmodelGe` by requiring
  `sqrt(card) * Rm * rho^2 <= kappa`, and keeps the upper scalar compatibility
  inequality for the same `B` explicit.

  Focused checks passed for `SecondOrderGronwall.lean`,
  `RadialGronwall.lean`, and `BallVolume.lean`; targeted refreshes of
  `SecondOrderGronwall` and `RadialGronwall` passed before downstream use.
  Current honest estimates: V1c Gronwall producer infrastructure ~99.85%;
  V1c determinant-bound algebraic bridge ~93.5%; V1d local volume
  shell/package machinery ~98%; V1c two-sided determinant theorem 0%; final
  V1d two-sided ball-volume theorem 0%; Stage V1 ~83.6%; whole
  volume-comparison lane ~62.5%.  Next target: prove or package the remaining
  upper scalar compatibility `A + gronwallBound ... <= B` for the same
  produced endpoint constant `B`, or keep it visibly explicit; do not claim the
  scalar constants are fully automatic until this compatibility is checked.

- 2026-07-08 follow-up 8as: resolved the same-constant scalar compatibility
  issue by preserving the natural split between lower and upper constants at
  the density and local volume layers.  `Volume/JacobianBounds.lean` added
  `exists_dens_pair_rm04_at`, which combines the lower and upper Rm04 density
  producers with separate constants `Blo` and `Bhi`.  `Volume/BallVolume.lean`
  added `exists_vol_pair_rm04_at`, which consumes that split density wrapper
  through `exists_vol_two_dens` and proves the corresponding local two-sided
  volume bounds without forcing the lower endpoint constant to also dominate
  the upper Gronwall expression.

  Focused checks passed for `JacobianBounds.lean` and `BallVolume.lean` with
  no global Lake lock; a targeted refresh of `JacobianBounds` passed before
  downstream use.  Current honest estimates: V1c Gronwall producer
  infrastructure ~99.85%; V1c determinant-bound algebraic bridge ~94%; V1d
  local volume shell/package machinery ~98.4%; V1c two-sided determinant
  theorem 0%; final V1d two-sided ball-volume theorem 0%; Stage V1 ~83.9%;
  whole volume-comparison lane ~63%.  Next target: decide whether to refactor
  the high-level `IsRm04VolHyp` / `exists_rm04_*` package to carry split
  constants, or keep the split local wrapper as the theorem-facing route.  Do
  not resume by trying to auto-prove the old same-`B` compatibility unless a
  new compatibility theorem has been explicitly identified.

- 2026-07-08 follow-up 8at: started the high-level split-package refactor
  without breaking the old same-constant API.  `Volume/BallVolume.lean` now has
  `IsRm04VolPairHyp`, a split-constant analogue of `IsRm04VolHyp` whose scalar
  fields use `Blo` for the lower endpoint bound and `Bhi` for the upper
  endpoint bound.  `exists_rm04_pair_hyp` constructs this package while
  producing the same radial frame and local radial-curve regularity fields as
  the old package constructor.  `exists_vol_rm04_pair_pkg` consumes the split
  package through `exists_vol_pair_rm04_at`, so the packaged layer can now
  prove split two-sided volume bounds directly.

  Focused verification passed for `BallVolume.lean` with no global Lake lock.
  No targeted refresh was needed in this pass because no downstream file was
  checked against the new declarations.  Current honest estimates: V1c
  Gronwall producer infrastructure ~99.85%; V1c determinant-bound algebraic
  bridge ~94%; V1d local volume shell/package machinery ~98.7%; V1c two-sided
  determinant theorem 0%; final V1d two-sided ball-volume theorem 0%; Stage V1
  ~84.1%; whole volume-comparison lane ~63.5%.  Next target: add split
  versions of `exists_vol_scale`, `exists_vol_scalar`, and then the
  launch/coefficient/global wrappers, preserving the old same-constant wrappers
  only as compatibility entrypoints.

- 2026-07-08 follow-up 8au: completed the split-constant wrapper chain through
  the current global Rm04 time-one route.  `Volume/BallVolume.lean` added
  `exists_vol_pair_scale`, `exists_vol_pair_scalar`,
  `exists_vol_pair_launch`, `exists_vol_pair_coeff`,
  `exists_vol_pair_regionRm`, and `exists_vol_pair_globalRm`, mirroring the old
  same-constant package stack while preserving separate lower/upper constants.
  It then added `exists_vol_pair_globalRm1`,
  `exists_vol_pair_rm1_ge`, and `exists_vol_pair_rm1_auto`: the lower endpoint
  constant is produced by the time-one small-coefficient lower scalar theorem,
  and the upper endpoint constant is chosen explicitly by a `max`, so no scalar
  model inequality remains as a theorem-facing input in this split route.

  Focused verification passed for `BallVolume.lean` with no global Lake lock.
  Current honest estimates: V1c Gronwall producer infrastructure ~99.9%; V1c
  determinant-bound algebraic bridge ~94%; V1d local volume shell/package
  machinery ~99%; V1c two-sided determinant theorem 0%; final V1d two-sided
  ball-volume theorem 0%; Stage V1 ~84.5%; whole volume-comparison lane ~64%.
  Next target: inspect the remaining coefficient-cap/source-radius frontier.
  The live obstruction is now `sqrt(card) * Rm * rho^2 <= kappa`, plus the
  source/radius hypotheses; do not return to same-`B` scalar compatibility.

- 2026-07-08 follow-up 8av: added the missing two-radius density-volume shell
  `exists_vol_two_dens_pairR` in `Volume/BallVolume.lean`.  It combines the
  existing lower density metric-ball consumer and upper density metric-ball
  consumer while keeping the lower model radius `Rlo` separate from the upper
  normal-coordinate radius `Rup`.  Focused verification passed for
  `BallVolume.lean` with no global Lake lock.

  The remaining finalization attempt now has three checked route failures:
  (1) same-radius finalization is the wrong denominator because lower
  containment and upper normal-coordinate containment pull `R` in opposite
  directions; (2) shrinking the exposed radius cannot prove the coefficient cap
  in the current chain, since the cap uses `Vb := rho` and hence
  `sqrt(card) * Rm * rho^2`; (3) the existing metric comparison API only gives
  the coercive lower direction
  `||w|| <= sqrt(g.inner p w w) / sqrt(gpCoerciveConst)`, not the upper
  `sqrt(g.inner p w w) <= C * ||w||` producer needed to make `Vb` shrink with
  the chosen model radius.  Current honest estimates: V1c Gronwall producer
  infrastructure ~99.9%; V1c determinant-bound algebraic bridge ~94.2%; V1d
  local volume shell/package machinery ~99.1%; V1c two-sided determinant
  theorem 0%; final V1d two-sided ball-volume theorem 0%; Stage V1 ~84.8%;
  whole volume-comparison lane ~64.5%.  Smallest next theorem: prove a local
  upper `g_p`/Euclidean norm comparison and use it to build a radius-dependent
  launch bound, or deliberately change the final capped theorem quantifier
  order so the comparison radius can depend on `Rm`.

- 2026-07-08 follow-up 8aw: resolved the missing upper `g_p`/Euclidean norm
  comparison route in `Volume/BallVolume.lean`.  The file now has private
  `sqrt_inner_le_opNorm_const`, a pointwise estimate from the operator norm of
  the continuous bilinear form `g.inner p`, and
  `exists_metric_upper_launch_const`, which packages it as
  `sqrt(g.inner p w w) <= C * R` on model balls.  The public split wrappers
  `exists_pair_rlaunch`, `exists_pair_rcoeff`, and `exists_pair_rglobal` add a
  radius-dependent route where the curvature coefficient cap is
  `sqrt(card) * Rm * (C * R)^2`, not `sqrt(card) * Rm * rho^2`.

  Focused verification passed for `BallVolume.lean` with no global Lake lock.
  Current honest estimates: V1c Gronwall producer infrastructure ~99.9%; V1c
  determinant-bound algebraic bridge ~94.4%; V1d local volume shell/package
  machinery ~99.25%; V1c two-sided determinant theorem 0%; final V1d
  two-sided ball-volume theorem 0%; Stage V1 ~85.2%; whole
  volume-comparison lane ~65%.  Next target: add the radius-dependent
  time-one wrappers consuming `exists_dirModel_ge1` with the cap
  `sqrt(card) * Rm * (C * R)^2 <= kappa`, then choose the upper endpoint
  constant by `max` as in `exists_vol_pair_rm1_auto`.  Do not restart the old
  same-radius or `Vb := rho` route.

- 2026-07-08 follow-up 8ax: extended the radius-dependent route through the
  time-one global Rm04 layer.  `Volume/BallVolume.lean` added
  `exists_pair_rglobal1`, `exists_pair_rrm1_ge`, and `exists_pair_rrm1`.
  The lower endpoint constant is produced from `exists_dirModel_ge1` with the
  cap `sqrt(card) * Rm * (C * R)^2 <= kappa`, and the upper endpoint constant
  is chosen by the same `max` pattern as the older `exists_vol_pair_rm1_auto`
  route.  Focused verification passed for `BallVolume.lean` with no global
  Lake lock.

  Current honest estimates: V1c Gronwall producer infrastructure ~99.9%; V1c
  determinant-bound algebraic bridge ~94.6%; V1d local volume shell/package
  machinery ~99.35%; V1c two-sided determinant theorem 0%; final V1d
  two-sided ball-volume theorem 0%; Stage V1 ~85.6%; whole
  volume-comparison lane ~65.5%.  Next target: state the final small-radius
  theorem with quantifiers ordered so `R` can be chosen after `Rm` and the
  fixed comparison constant `C`, while keeping lower and upper model radii
  separate through `exists_vol_two_dens_pairR`.

- 2026-07-08 follow-up 8ay: audited the final small-radius route and confirmed
  that directly wrapping `exists_pair_rrm1` would reintroduce the same-radius
  failure: the lower side wants `C * R < s`, while the upper side wants
  `s / sqrt(gpCoerciveConst) < R`.  The final theorem still needs separate
  lower and upper model radii.

  `Volume/BallVolume.lean` added private scalar helpers
  `exists_pos_lt_mul_sq_le` and `exists_radius_coeff_cap`.  The latter chooses
  a positive radius after `C`, `kappa`, `rho`, and the curvature coefficient,
  with `R < rho`, `C * R < rho`, and the coefficient cap all satisfied.
  Focused verification passed for `BallVolume.lean` with no global Lake lock.
  Current honest estimates: V1c Gronwall producer infrastructure ~99.9%; V1c
  determinant-bound algebraic bridge ~94.7%; V1d local volume shell/package
  machinery ~99.4%; V1c two-sided determinant theorem 0%; final V1d
  two-sided ball-volume theorem 0%; Stage V1 ~85.8%; whole
  volume-comparison lane ~65.8%.  Next target: build the double-radius
  density/volume wrapper, using a small lower radius for `C * Rlo < s` and a
  separate upper radius for `s / sqrt(gpCoerciveConst) < Rup`; do not use
  `exists_pair_rrm1` as a final single-radius theorem.

- 2026-07-08 follow-up 8az: added `exists_pairR_rm04_at`, the double-radius
  Rm04 density-volume wrapper in `Volume/BallVolume.lean`.  It consumes
  `exists_dens_pair_rm04_at` separately on `Rlo` and `Rup`, then feeds
  `exists_vol_two_dens_pairR`, so the lower estimate uses `Rlo` and the upper
  estimate uses `Rup`.  The shared launch/Rm/frame hypotheses are stated on
  the union of the two model balls.  Focused verification passed for
  `BallVolume.lean` with no global Lake lock.

  Current honest estimates: V1c Gronwall producer infrastructure ~99.9%; V1c
  determinant-bound algebraic bridge ~94.8%; V1d local volume shell/package
  machinery ~99.55%; V1c two-sided determinant theorem 0%; final V1d
  two-sided ball-volume theorem 0%; Stage V1 ~86.2%; whole
  volume-comparison lane ~66.3%.  Next target: add a double-radius proof
  package/automatic wrapper that supplies the union launch/Rm/frame hypotheses
  from the radius-dependent global Rm04 route, then choose `Rlo` by the scalar
  cap helper and `Rup` from the metric-ball upper containment constraints.

- 2026-07-08 follow-up 8ba: added `exists_pairR_rglobal` in
  `Volume/BallVolume.lean`.  This is the verified double-radius global-Rm04
  wrapper: `Rlo` feeds the lower density and lower volume estimate, while
  `Rup` feeds the upper containment and the shared radial frame data.  The
  proof builds frame data on `Rup`, lifts the union hypotheses through
  `Rlo <= Rup`, uses the fixed launch constant `C`, and consumes a global Rm04
  bound on radial curves.  This is the intended replacement for trying to use
  the old same-radius `exists_pair_rrm1` route.

  Focused verification passed for `BallVolume.lean` with no global Lake lock.
  Current honest estimates: V1c Gronwall producer infrastructure ~99.9%; V1c
  determinant-bound algebraic bridge ~94.95%; V1d local volume shell/package
  machinery ~99.7%; V1c two-sided determinant theorem 0%; final V1d
  two-sided ball-volume theorem 0%; Stage V1 ~86.7%; whole
  volume-comparison lane ~67%.  Next target: choose `Rlo` using
  `exists_radius_coeff_cap` and choose `Rup` from the metric-ball upper
  containment inequalities, then package `exists_pairR_rglobal` into the final
  small-radius time-one theorem with separate lower/upper model radii.

- 2026-07-08 follow-up 8bb: added `exists_pairR_rm1` in
  `Volume/BallVolume.lean`.  This time-one double-radius wrapper consumes
  `exists_pairR_rglobal`, produces the positive lower endpoint `Blo` via
  `exists_dirModel_ge1`, and chooses the upper endpoint constant by the
  existing `max` pattern.  The coefficient cap is now correctly attached to
  `Rup`, the upper radius that controls the shared launch/frame package.

  Focused verification passed for `BallVolume.lean` with no global Lake lock.
  Current honest estimates: V1c Gronwall producer infrastructure ~99.9%; V1c
  determinant-bound algebraic bridge ~95.1%; V1d local volume shell/package
  machinery ~99.78%; V1c two-sided determinant theorem 0%; final V1d
  two-sided ball-volume theorem 0%; Stage V1 ~87%; whole
  volume-comparison lane ~67.4%.  Next target: prove the radius-existence
  wrapper that, for sufficiently small metric radius `s`, chooses `Rup` with
  the upper containment and coefficient cap and then chooses a smaller `Rlo`
  with `C * Rlo < s`.

- 2026-07-08 follow-up 8bc: added `exists_pairR_small` in
  `Volume/BallVolume.lean`.  This is the verified small-radius existence form
  of the double-radius time-one route.  For each global Rm04 bound and scalar
  initial upper bound it chooses a positive metric-radius threshold `delta`;
  every `0 < s < delta` admits existential model radii `Rlo` and `Rup` with
  `Rlo <= Rup`, upper containment through `Rup`, and lower smallness through
  `C * Rlo < s`.  The proof chooses `Rup` by `exists_radius_coeff_cap` against
  `min rho expMapC2Radius`, and chooses `Rlo` using the new private helper
  `exists_pos_le_mul_lt`.

  Focused verification passed for `BallVolume.lean` with no global Lake lock.
  Current honest estimates: V1c Gronwall producer infrastructure ~99.9%; V1c
  determinant-bound algebraic bridge ~95.3%; V1d local volume shell/package
  machinery ~99.9%; V1c two-sided determinant theorem 0%; final V1d
  two-sided ball-volume theorem 0%; Stage V1 ~87.8%; whole
  volume-comparison lane ~68%.  Next target: decide the final public statement
  shape: either keep existential `Rlo/Rup` as the theorem-facing API, or add
  explicit constants that eliminate the existential radii from the user-facing
  volume comparison statement.

- 2026-07-08 follow-up 8bd: added `exists_pairR_scaled` in
  `Volume/BallVolume.lean`, the explicit scaled-radius public wrapper for the
  double-radius time-one route.  It fixes constants `C`, `D`, and `Blo`, then
  for each global Rm04 bound and scalar initial upper bound chooses a small
  threshold `delta`; every `0 < s < delta` satisfies the two-sided volume
  estimate with lower radius `Rlo = s / (2 * C)` and upper radius
  `Rup = D * s`.  The chosen `D` dominates both the upper containment factor
  and the lower-radius inclusion factor, while the threshold handles
  source/C2/rho and coefficient-cap smallness.

  Focused verification passed for `BallVolume.lean` with no global Lake lock.
  Current honest estimates: V1c Gronwall producer infrastructure ~99.9%; V1c
  determinant-bound algebraic bridge ~95.5%; V1d local volume shell/package
  machinery ~100%; V1d explicit scaled two-sided ball-volume theorem: stated
  and proved under the current global Rm04/scalar-initial hypotheses; V1c
  two-sided determinant theorem 0%; Stage V1 ~89%; whole volume-comparison lane
  ~69.5%.  Next target: decide whether to export `exists_pairR_scaled` through
  an umbrella/API file now, or first eliminate/standardize the remaining global
  Rm04 and scalar initial hypotheses before treating it as the final
  user-facing comparison theorem.

- 2026-07-08 follow-up 8be: exported the Volume comparison stack through
  `DifferentialGeometry.lean` by adding imports for
  `Volume.NormalChartMeasure`, `Volume.RadialGronwall`,
  `Volume.JacobianBounds`, and `Volume.BallVolume`.  This exposes
  `exists_pairR_scaled` through the project umbrella without adding a competing
  overview or wrapper file.

  Focused verification passed for `DifferentialGeometry.lean` with no global
  Lake lock.  Current honest estimates: V1c Gronwall producer infrastructure
  ~99.9%; V1c determinant-bound algebraic bridge ~95.5%; V1d local volume
  shell/package machinery ~100%; V1d explicit scaled two-sided ball-volume
  theorem: stated, proved, and root-exported under the current global
  Rm04/scalar-initial hypotheses; V1c two-sided determinant theorem 0%; Stage
  V1 ~89.2%; whole volume-comparison lane ~70%.  Next target: standardize or
  discharge the remaining theorem-facing inputs (`Rm` global bound and scalar
  initial upper bound `A`) if the desired final statement should no longer
  expose them.

- 2026-07-08 follow-up 8bf: added `exists_pairR_autoA` in
  `Volume/BallVolume.lean`.  This keeps the explicit scaled-radius public
  shape but discharges the scalar initial frame-bound input by producing `A`
  from the fixed `chartModelBasis` and the existing operator-norm pointwise
  bound.  The caller still supplies the global Rm04 bound `Rm`; that is the
  remaining honest geometric input, not a local algebraic basis-bound
  artifact.

  Focused verification passed for `BallVolume.lean` with no global Lake lock.
  Current honest estimates: V1c Gronwall producer infrastructure ~99.9%; V1c
  determinant-bound algebraic bridge ~95.7%; V1d local volume shell/package
  machinery ~100%; V1d explicit scaled two-sided ball-volume theorem: stated,
  proved, root-exported, and equipped with a verified auto-`A` public wrapper;
  V1c two-sided determinant theorem 0%; Stage V1 ~89.7%; whole
  volume-comparison lane ~70.8%.  Next target: decide whether the remaining
  global Rm04 bound `Rm` should remain the theorem-facing local-comparison
  input, or should be supplied later by a separate geometric producer in the
  final application layer.

- 2026-07-08 follow-up 8bg: added `Rm04GlobalBound` and `exists_pairR_bound`
  in `Volume/BallVolume.lean`.  The local comparison endpoint now has a named
  predicate for the remaining global pointwise Rm04 norm bound and a
  predicate-facing public wrapper that still chooses the scalar initial
  constant `A` internally.  This records the design decision that global Rm04
  boundedness is an honest geometric/application input, not a hidden local
  algebraic artifact.

  Focused verification passed for `BallVolume.lean` with no global Lake lock.
  Current honest estimates: V1c Gronwall producer infrastructure ~99.9%; V1c
  determinant-bound algebraic bridge ~95.8%; V1d local volume shell/package
  machinery ~100%; V1d explicit scaled two-sided ball-volume theorem: stated,
  proved, root-exported, auto-`A`, and equipped with a named global-Rm
  predicate-facing entrypoint; V1c two-sided determinant theorem 0%; Stage V1
  ~90%; whole volume-comparison lane ~71.2%.  Next target: move to the
  application side that supplies `Rm04GlobalBound`, or wire this local endpoint
  into the HCG compactness input layer without replacing the real curvature
  producer by a consumer-side assumption wrapper.

- 2026-07-08 follow-up 8bh: wired the named global-Rm predicate to the existing
  HCG bounded-geometry layer.  `HCGCompactness/BoundedGeometry.lean` now imports
  `Volume.BallVolume` and proves `rm04Bound_of_curv0`, `rm04Bound_of_geom`, and
  `rm04Bound_of_seq`, showing that zeroth-order `HasCurvDerivBound`,
  `BoundedGeometry`, and `SeqBoundedGeometry` supply
  `VolumeComparison.Rm04GlobalBound`.

  The upstream `Volume.BallVolume` module was refreshed once so the downstream
  file could read the new predicate.  Focused verification passed for
  `BoundedGeometry.lean` with no global Lake lock.  Current honest estimates:
  V1c Gronwall producer infrastructure ~99.9%; V1c determinant-bound algebraic
  bridge ~95.8%; V1d local volume shell/package machinery ~100%; V1d explicit
  scaled two-sided ball-volume theorem: stated, proved, root-exported, auto-`A`,
  named global-Rm predicate-facing, and now connected to HCG bounded-geometry
  curvature inputs; V1c two-sided determinant theorem 0%; Stage V1 ~90.5%;
  whole volume-comparison lane ~71.8%.  Next target: decide the correct
  application file for consuming `exists_pairR_bound` with a pointed metric
  object, because that requires the Riemannian metric-space/enorm hypotheses in
  addition to the curvature bridge now supplied by bounded geometry.

- 2026-07-08 follow-up 8bi: added the C4 application bridge
  `HCGCompactness/C4/VolumeComparisonBridge.lean`.  The theorem
  `exists_pairR_of_boundedGeometry` consumes `MetricComplete`, connectedness,
  and `BoundedGeometry` for one `PointedRiemannianManifold`, installs the
  Riemannian metric-space/tangent-enorm context, and calls
  `VolumeComparison.exists_pairR_bound` with the curvature input supplied by
  `rm04Bound_of_geom`.

  Focused verification passed for `VolumeComparisonBridge.lean` with no global
  Lake lock.  The explicitly named upstream `.olean` refreshes for
  `BallVolume` and `BoundedGeometry` were also run without the global Lake lock
  after downstream checks exposed stale exported declarations.  Current honest
  estimates: V1c Gronwall producer infrastructure ~99.9%; V1c
  determinant-bound algebraic bridge ~95.8%; V1d local volume shell/package
  machinery ~100%; V1d explicit scaled two-sided ball-volume theorem: stated,
  proved, root-exported, auto-`A`, named global-Rm predicate-facing, connected
  to HCG bounded-geometry curvature inputs, and now consumable by a pointed
  metric object under completeness/connectedness; V1c two-sided determinant
  theorem 0%; Stage V1 ~91%; whole volume-comparison lane ~72.5%.  The target
  theorem `StepAInputs.VolumeComparisonInput` is still 0% proved from this
  infrastructure; its dedicated local-volume machinery is now roughly 35%.
  Next target: bridge the local small-ball volume estimate to the bounded
  packing/multiplicity shape of `StepAInputs.VolumeComparisonInput`, or add the
  smaller sequence-level wrapper first if that is the next planned lane.

- 2026-07-08 follow-up 8bj: added
  `HCGCompactness/C4/VolumeComparisonBridge.exists_pairR_of_seqBoundedGeometry`,
  the sequence-level wrapper for the pointed local-volume theorem.  It consumes
  `SeqMetricComplete`, per-member connectedness, and `SeqBoundedGeometry`, then
  applies `exists_pairR_of_boundedGeometry` to `X.obj k`.  The wrapper keeps the
  comparison constants separate from the uniform curvature constant `hgeom.C 0`.

  Focused verification passed for `VolumeComparisonBridge.lean` with no global
  Lake lock.  Current honest estimates: V1c Gronwall producer infrastructure
  ~99.9%; V1c determinant-bound algebraic bridge ~95.8%; V1d local volume
  shell/package machinery ~100%; V1d explicit scaled two-sided ball-volume
  theorem: stated, proved, root-exported, auto-`A`, named global-Rm
  predicate-facing, connected to HCG bounded-geometry curvature inputs, and now
  available termwise for a `PointedRiemannianSeq`; V1c two-sided determinant
  theorem 0%; Stage V1 ~91.2%; whole volume-comparison lane ~73%.  The target
  theorem `StepAInputs.VolumeComparisonInput` remains 0% proved; its dedicated
  local-volume machinery is now roughly 40%.  Next target: identify or state the
  exact finite-packing lemma needed to convert disjoint lower-volume balls plus
  an upper-volume containing ball into the `ballMult` cardinality bound, without
  pretending the Bishop--Gromov/packing step is already discharged.

- 2026-07-08 follow-up 8bk: added `Volume/Packing.lean` with the checked
  arithmetic gate `VolumeComparison.card_le_of_mul_lt`.  This lemma converts
  `(n : Real) * L <= U`, `0 < L`, and `U < (N + 1) * L` into `n <= N`.  It is
  the last numeric step needed after a future measure argument derives the
  lower-volume-times-cardinality bound from disjoint small balls and an upper
  volume bound on a containing ball.

  Focused verification passed for `Volume/Packing.lean` with no global Lake
  lock.  The new module was root-exported through `DifferentialGeometry.lean`;
  its `.olean` was refreshed via an explicitly named `build -NoLakeLock`, and
  the root import file focused-check passed.  Current honest estimates: V1c
  Gronwall producer infrastructure ~99.9%; V1c determinant-bound algebraic
  bridge ~95.8%; V1d local volume shell/package machinery ~100%; V1e
  packing/multiplicity infrastructure ~10% (arithmetic gate only; no
  disjoint-union measure bridge yet); Stage V1 ~91.5%; whole
  volume-comparison lane ~73.5%.  The target theorem
  `StepAInputs.VolumeComparisonInput` remains 0% proved.  Next target: state
  and prove the measure inequality
  `(J.card : Real) * lowerVolume <= upperVolume` from pairwise disjoint
  measurable small balls contained in a measurable large ball, or identify the
  exact Mathlib lemma that already supplies it.

- 2026-07-08 follow-up 8bl: extended `Volume/Packing.lean` with
  `VolumeComparison.mul_lower_le_upper`, the abstract finite disjoint-measure
  bridge.  It consumes a finite family of pairwise disjoint measurable small
  sets contained in a large set, plus a uniform real-measure lower bound `L` on
  each small set, and proves `(J.card : Real) * L <= μ.real large`.  The proof
  reuses Mathlib's finite disjoint-union real-measure equality and real measure
  monotonicity, then leaves the final count cap to `card_le_of_mul_lt`.

  Focused verification passed for `Volume/Packing.lean` with no global Lake
  lock.  The module `.olean` was refreshed through an explicitly named
  `build -NoLakeLock`, and the root import file focused-check passed, also with
  no global Lake lock.  Current honest estimates: V1c Gronwall producer
  infrastructure ~99.9%; V1c determinant-bound algebraic bridge ~95.8%; V1d
  local volume shell/package machinery ~100%; V1e packing/multiplicity
  infrastructure ~25% (generic disjoint-measure inequality plus arithmetic
  count gate are checked; geometric ball instantiation and ball-multiplicity
  packaging remain); Stage V1 ~91.8%; whole volume-comparison lane ~74%.  The
  target theorem `StepAInputs.VolumeComparisonInput` remains 0% proved.  Next
  target: instantiate `mul_lower_le_upper` for the packing balls used by
  `StepAInputs.VolumeComparisonInput.ballMult`, proving the concrete
  disjointness, containment, measurability, lower-volume, and upper-volume
  hypotheses or isolating the smallest missing geometric ball API lemma.

- 2026-07-08 follow-up 8bm: extended `Volume/Packing.lean` from abstract
  measurable sets to metric balls.  New checked lemmas:
  `VolumeComparison.balls_disjoint` proves radius-`r/2` balls are pairwise
  disjoint for an `r`-separated finite center family;
  `VolumeComparison.balls_subset_ball` proves the selected small balls lie in
  the radius `(m + 1/2) * r` ball around `z` when their centers lie within
  `m * r` of `z`; and `VolumeComparison.ball_mul_le` packages these with
  `mul_lower_le_upper` into the metric-ball real-measure packing inequality.

  Focused verification passed for `Volume/Packing.lean` with no global Lake
  lock.  The module `.olean` was refreshed through an explicitly named
  `build -NoLakeLock`, and the root import file focused-check passed, also with
  no global Lake lock.  Current honest estimates: V1c Gronwall producer
  infrastructure ~99.9%; V1c determinant-bound algebraic bridge ~95.8%; V1d
  local volume shell/package machinery ~100%; V1e packing/multiplicity
  infrastructure ~38% (metric-ball disjointness/containment/measurability,
  generic measure inequality, and arithmetic count gate are checked; ENNReal to
  real-volume conversion, constant choice, and final `ballMult` packaging
  remain); Stage V1 ~92%; whole volume-comparison lane ~74.8%.  The target
  theorem `StepAInputs.VolumeComparisonInput` remains 0% proved.  Next target:
  add the small bridge that turns the existing local two-sided ENNReal ball
  estimates into the real constants consumed by `ball_mul_le`, then compose
  that with `card_le_of_mul_lt` to state the first concrete `ballMult` producer.

- 2026-07-08 follow-up 8bn: strengthened `Volume/Packing.lean` so the packing
  measure bridge no longer assumes a globally finite measure.  The generic
  set-level `mul_lower_le_upper` and metric-ball `ball_mul_le` now require only
  finite measure of the containing set/ball, which is the correct shape for
  noncompact Riemannian volume.  Added `VolumeComparison.ball_card_le_of_vol`,
  the capped metric-ball cardinality gate: ENNReal lower bounds on the small
  balls, an ENNReal upper bound on the containing ball, positive lower constant
  `L`, nonnegative upper constant `U`, and strict numeric cap
  `U < (N + 1) * L` prove `J.card <= N`.

  Focused verification passed for `Volume/Packing.lean` with no global Lake
  lock.  The module `.olean` was refreshed through an explicitly named
  `build -NoLakeLock`, and the root import file focused-check passed, also with
  no global Lake lock.  Current honest estimates: V1c Gronwall producer
  infrastructure ~99.9%; V1c determinant-bound algebraic bridge ~95.8%; V1d
  local volume shell/package machinery ~100%; V1e packing/multiplicity
  infrastructure ~55% (generic metric-ball cardinality gate from ENNReal volume
  bounds is checked; uniform bounded-geometry constant choice and final
  `VolumeComparisonInput.ballMult` packaging remain); Stage V1 ~92.5%; whole
  volume-comparison lane ~76%.  The target theorem
  `StepAInputs.VolumeComparisonInput` remains 0% proved.  Next target: in the
  C4 bridge layer, use `exists_pairR_of_seqBoundedGeometry` to pick uniform
  local volume constants and define a candidate `Imult m`, or identify the
  precise obstruction if those constants are only pointwise in the center.

- 2026-07-08 follow-up 8bo: checked the C4 bridge route from
  `exists_pairR_of_seqBoundedGeometry` toward
  `StepAInputs.VolumeComparisonInput.ballMult`.  The direct route is blocked by
  missing uniformity, not by a local Lean proof issue.  The existing local
  two-sided ball-volume theorem chooses constants after the center point `p`;
  its constants and smallness radius depend on pointwise normal-coordinate data
  such as `gpCoerciveConst g p` and `exists_basis_upper_const g p`.
  `SeqBoundedGeometry` currently gives only uniform curvature-derivative bounds,
  not uniform lower bounds for those normal-coordinate constants/radii across
  all centers and sequence members.

  No new Lean theorem was added in `VolumeComparisonBridge.lean` during this
  feasibility pass.  Current honest estimates remain: V1e
  packing/multiplicity infrastructure ~55% checked generic core; the
  `VolumeComparisonInput` target theorem remains 0% proved.  Next target:
  either formalize the book-faithful Bishop--Gromov relative volume/packing
  theorem under Ricci lower-bound hypotheses, or add an explicit uniform
  local-volume-comparison input carrying constants and a radius `r0` uniform in
  `k` and center, then consume `VolumeComparison.ball_card_le_of_vol`.

- 2026-07-08 follow-up 8bp: added the explicit uniform-input route.  In
  `Volume/Packing.lean`, `VolumeComparison.ball_card_le_meas` is the
  explicit-measurability version of the capped metric-ball cardinality gate;
  the old `ball_card_le_of_vol` remains as the Borel convenience wrapper.  This
  avoids topology-instance ambiguity when C4 supplies a metric for balls while
  the pointed manifold keeps its stored topology/measurable structure.

  In `HCGCompactness/C4/VolumeComparisonBridge.lean`, added
  `UniformBallPack`, an honest uniform local-volume packing input carrying the
  Step A distance, a concrete metric for balls, uniform `r0`, `Imult`, lower
  and upper constants `L m r`/`U m r`, small-ball measurability, ENNReal
  lower/upper volume estimates, and the strict cap
  `U m r < (Imult m + 1) * L m r`.  Added
  `UniformBallPack.toVCInput`, which produces
  `StepAInputs.VolumeComparisonInput` by applying
  `VolumeComparison.ball_card_le_meas`.

  Focused verification passed for `Volume/Packing.lean` and
  `VolumeComparisonBridge.lean` with no global Lake lock.  The explicitly
  named modules `DifferentialGeometry.Geometry.Comparison.Volume.Packing` and
  `DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.VolumeComparisonBridge`
  were refreshed with `build -NoLakeLock`; the root import focused-check passed
  because root exports `Volume/Packing.lean`.  Current honest estimates: V1e
  packing/multiplicity infrastructure ~70% (checked generic core plus explicit
  uniform-input-to-A0' producer); `StepAInputs.VolumeComparisonInput` remains
  0% proved from `SeqBoundedGeometry`; the missing mathematical producer is
  still the uniform comparison input itself, preferably Bishop--Gromov relative
  packing under Ricci lower-bound hypotheses.  Stage V1 ~92.8%; whole
  volume-comparison lane ~77%.  Next target: either formalize a
  Bishop--Gromov/Ricci-lower-bound producer for `UniformBallPack`, or wire
  `UniformBallPack` into `MetricCompactnessInputs` as the precise A0' producer
  assumption without pretending it follows from current `SeqBoundedGeometry`.

- 2026-07-08 follow-up 8bq: wired `UniformBallPack` into
  `MetricCompactnessInputs` and then corrected the A0' cap shape to the
  planned joint cap.  `StepAInputs.VolumeComparisonInput.ballMult` now requires
  `m * r <= r0`, not merely `r <= r0`; `GoodCovering.net_multiplicity` consumes
  the concrete `4 * lambda[R] <= r0` cap; `GoodCoveringSeq.inter_count`
  consumes the concrete `50 * exp(C * 20 * lambda[0]) * lambda[0] <= r0` cap;
  and `MetricCompactnessInputs` records this as `stepA_cap_le`, the maximum
  Step-A ratio times `lambda[0]` bounded by the producer cap.  The explicit
  `UniformBallPack` fields and `toVCInput` now use the same joint-cap shape.

  Focused checks and targeted module builds passed through
  `C4.MetricCompactnessInputs`, all with no global Lake lock.  This is an
  interface correctness fix and wiring step: `VolumeComparisonInput` from
  `SeqBoundedGeometry` remains 0% proved, and the missing mathematical producer
  is still Bishop--Gromov or an equivalent uniform comparison theorem supplying
  `UniformBallPack`.  V1e packing/multiplicity infrastructure is about 78%;
  Stage V1 about 93%; whole volume-comparison lane about 78%.

- 2026-07-08 follow-up 8br: added the small checked projection layer for the
  joint Step A cap inside `MetricCompactnessInputs`.  The bundle now exposes
  `cap_four`, `cap_four_of_nonneg`, and `cap_inter`, which are the exact
  consumer shapes for the `m = 4` multiplicity cap and the item-5 intersection
  cap.  Focused verification and the targeted `C4.MetricCompactnessInputs`
  module build passed, both with no global Lake lock.

  This remains infrastructure only: `VolumeComparisonInput` from
  `SeqBoundedGeometry` is still 0% proved, `metricCompactness` is still 0%
  proved, and the missing mathematical producer is still Bishop--Gromov or an
  equivalent uniform comparison theorem supplying `UniformBallPack`.  V1e
  packing/multiplicity infrastructure is about 78.5%; Stage V1 about 93%;
  whole volume-comparison lane about 78%.

- 2026-07-08 follow-up 8bs: added checked bundle-level Step A adapters in
  `MetricCompactnessInputs`: `net_mult`, `inter_count`, `exists_net_data`,
  `exists_stable_net`, and `exists_stepA_net`.  The D6 assembly can now start
  from a single `MetricCompactnessInputs` value to obtain the stable Step A
  `NetLimitData` and the item-5 intersection bound, instead of manually
  rethreading `decay`, `pack`, `volume`, `dist_eq`, and the joint-cap
  projections.

  Focused verification and the targeted `C4.MetricCompactnessInputs` module
  build passed, both with no global Lake lock.  This is still assembly
  infrastructure only: `VolumeComparisonInput` from `SeqBoundedGeometry`
  remains 0% proved, `metricCompactness` remains 0% proved, and the missing
  mathematical producer remains Bishop--Gromov or an equivalent uniform
  comparison theorem supplying `UniformBallPack`.  V1e packing/multiplicity
  infrastructure is about 79%; Stage V1 about 93%; whole volume-comparison
  lane about 78.2%.

- 2026-07-08 follow-up 8bt: added D6-facing reindexing and endpoint-hypothesis
  wrappers.  `StepBInputs` now has checked `subseq` wrappers for
  `ExpInverseDerivBoundInput` and `NormalCoordMetricBoundInput`, and
  `MetricCompactnessInputs` now has `subseq`, `properMetrics`, and `stepA_net`.
  This lets D6 carry the full conditional input bundle through composed
  subsequences, build the per-member `ProperMetricOn` family from
  `SeqMetricComplete` plus connectedness, and obtain the Step A net package
  directly from the endpoint hypotheses.

  Focused checks passed for `StepBInputs.lean` and `MetricCompactnessInputs.lean`;
  targeted module builds passed for both, all with no global Lake lock.  This
  is still D6/Step-A assembly infrastructure only: `VolumeComparisonInput` from
  `SeqBoundedGeometry` remains 0% proved and `metricCompactness` remains 0%.
  V1e packing/multiplicity infrastructure is about 79.5%; Stage V1 about 93%;
  whole volume-comparison lane about 78.4%.
