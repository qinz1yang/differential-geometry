# NormalChartMeasure

## 2026-07-07 V1a/V1b normal-chart specialization

Status: `NormalChartMeasure.lean` now verifies the V1a specialization of the
Integration-layer V0 API and the first V1b endpoint/density form of the
normal-Gram/radial-Jacobi identification.

Completed:

- Defined `normalChartDensity g p` as
  `paramDensity g (NormalCoordinates.expMapDiffeo g p)`.
- Defined `normalGramMatrix g p` and `radialJacobiGram g p x`.
- Proved `normalChart_volume_eq`: for a measurable set
  `A ⊆ (normalChartAt g p).source`, the Riemannian volume of `A` is the
  model-Haar integral over `(normalChartAt g p) '' A` of
  `ENNReal.ofReal (normalChartDensity g p)`.
- Proved `expDiffeo_mfderiv`, the germ-local derivative equality between
  `expMapDiffeo g p` and the actual exponential map on the diffeomorphism
  source.
- Proved the pointwise, matrix, density, and integral V1b forms:
  `normalGram_radial`, `normalGram_radialMat`, `normalDensity_radial`, and
  `normalChart_volume_radial`.
- Added Gronwall-facing wrappers for the packaged field:
  `radialJacobi_zero`, `exists_radialJacobi_radius`, and
  `exists_radialJacobi_deriv_radius`.
- Added `exists_radialJacobi_zero_radius`, the endpoint `IsJacobiAt ... 0`
  radius wrapper for the packaged `radialJacobiField` vocabulary.
- Added `radialJacobi_one_smul`, the endpoint linearity bridge
  `J_{a • w}(1) = a • J_w(1)` obtained from `radialJacobi_one` and linearity
  of the vector-slot `mfderiv`.
- Added `radialJacobi_one_sum`, the endpoint finite-linearity bridge for
  coefficient combinations of `chartModelBasis E`.  This is the normalization
  adapter needed by the lower direction-bound density route.

Route:

- This is a direct specialization of
  `riemannianVolumeMeasure_param_target_eq` with
  `Ψ := NormalCoordinates.expMapDiffeo g p`.
- The old V1a blocker was an Integration-layer API gap; it is now discharged by
  `ParamEvaluation.lean`.
- V1b is a direct use of `JacobiVariation.lean`'s endpoint identity
  `radial_jacobi_one`: at `t = 1`, the packaged radial variation field is the
  vector-slot derivative of `expMap`.
- The endpoint scaling bridge is deliberately endpoint-only: it does not prove
  linearity of the full Jacobi field or of `D_tJ(0)`, but it is enough for the
  scaled-basis upper-density route in V1c.
- The endpoint finite-linearity bridge is also endpoint-only.  It turns
  `J_{sum_i v_i e_i}(1)` into the sum of endpoint basis fields, but it does
  not prove any lower norm estimate for that combination.
- The initial-condition and Jacobi-equation wrappers are direct restatements of
  the existing `JacobiVariation.lean` producers under the `radialJacobiField`
  name used by the volume-comparison layer.
- The endpoint-zero wrapper follows the same route, but its theorem head must
  use the `Bundle` scoped Riemannian-bundle instances while disabling the
  project tangent-space norm instances, matching `JacobiVariation.exists_jacobi_zero`.

Current blocker / next frontier:

- V1a and the endpoint/density part of V1b are proved.  The next V1c frontier
  is the two-sided determinant/Jacobian bound at capped scale.  That is not a
  measure-theory or normal-chart rewriting step: it must instantiate the
  existing `SecondOrderGronwall` / `CovariantGronwall` / parallel-frame assets
  against the radial Jacobi fields with the same curvature-bound hypothesis
  shape those files already use.
- The Gronwall-ready center vanishing, interior Jacobi equation, endpoint
  Jacobi equation, and derivative-at-zero radius wrappers are now surfaced
  here.  V1c still has to instantiate the Gronwall/parallel-frame estimates
  with curvature-bound inputs and turn them into entry or singular-value bounds.
- The next lower-route target is not more normal-chart rewriting: it is the
  analytic lower endpoint norm estimate for `J_{sum_i v_i e_i}(1)` for every
  unit coefficient vector `v`.

Progress estimates:

- V1a theorem: 100% complete in Lean.
- V1b endpoint/density theorem: 100% complete in Lean (`normalChart_volume_radial`).
- V1b/V1c Gronwall-ready endpoint machinery: about 90% complete; the direct
  wrappers, endpoint-zero Jacobi wrapper, endpoint scaling, and endpoint
  finite-linearity adapter exist, but the full analytic hypothesis package is
  not built.
- V1c determinant-bound theorem: 0% complete; no `JacobianBounds.lean` theorem
  is stated yet.
- Stage V1: about 60% complete.  Normal-chart measure transfer, endpoint
  Jacobi-density rewriting, V1d conditional integration shells, and much of
  the V1c algebraic consumer layer are in place; the analytic Gronwall
  producers and final capped two-sided theorem remain.
- Whole volume-comparison lane: about 35% complete.  V0, V1a, endpoint V1b,
  V1c algebraic upper/lower consumers, and V1d conditional integration shells
  are in place, but Gronwall comparison, explicit capped constants,
  Bishop-Gromov, and CGT stages remain.

Verification: focused verification and targeted module verification passed for
`NormalChartMeasure.lean` after adding `radialJacobi_one_smul`; focused
verification and targeted module verification passed again after adding
`radialJacobi_one_sum`.  Downstream targeted verification through
`DifferentialGeometry.Geometry.Comparison.Volume.BallVolume` passed after the
direction-bound lower-density consumer imported this bridge.  No `sorry` or
`axiom` occurs in this file.

2026-07-08 update: focused verification passed after adding
`exists_radialJacobi_zero_radius`, and targeted module verification passed for
`Volume.NormalChartMeasure`.  No new blocker remains in this file.

## 2026-07-07 V1a audit (historical, superseded)

Historical status: this audit identified the missing Integration-layer API
before `ParamEvaluation.lean` existed.  The blocker below is superseded by the
V0 API and the current V1a specialization above.

Stage V1 is blocked at V1a before a sound Lean statement can be added.  The
requested normal-coordinate formula needs a public measure theorem for an
arbitrary smooth chart or `PartialDiffeomorph` chart:

```text
riemannianVolumeMeasure g (Phi.symm '' B)
  = integral over B of sqrt(det normal/pulled-back Gram)
```

The existing Integration assets provide the canonical-chart ingredients:
`chartLocalMeasure_lintegral`,
`chartLocalMeasure_lintegral_U_eq_setLIntegral_image`,
`chartLocalMeasure_lintegral_eq_of_support_in_overlap`,
`riemannianMeasure_lintegral_eq`, POU independence, and the canonical
chart-transition density identity.  They do not currently expose a global
`riemannianVolumeMeasure` formula for a supplied maximal-atlas chart or a
normal-chart `PartialDiffeomorph`.

I also found a canonical-chart support theorem in the Sobolev/elliptic layer,
but it is not the needed normal-chart statement and is not an appropriate
Comparison dependency.  `Geometry/Coordinates/ChartRegistration.lean` can
register smooth partial diffeomorphisms as maximal-atlas charts, but it is not
connected to `chartDensity`, `chartLocalMeasure`, or `riemannianVolumeMeasure`.

Smallest remaining frontier: add an Integration/Measure API theorem, or approve
adding its equivalent in this lane, that evaluates `riemannianVolumeMeasure`
against an arbitrary smooth local chart with density given by the pullback Gram.
After that, `normalChartAt` can be substituted and V1b can identify the pulled
back Gram with the Jacobi-field Gram.

Verification: no Lean file was added; no Lean check was run.  This is a missing
API/layering blocker, not a failed proof obligation.

Progress estimate: V1a theorem itself is 0% complete because no public Lean
statement was added.  Its dedicated asset audit is about 70% complete.  Stage
V1 remains about 0% complete; the V1-through-V3 volume-comparison lane remains
about 0%; the broader Poincare/HCG input program remains only at the planning
and adjacent-infrastructure stage for this lane.

## 2026-07-07 planner ruling (gap verified, API approved)

Planner re-verified the audit: `DivergenceTheorem/ChartInvariance.lean` is
canonical-chart-pair only (overlap-support + Voss–Weyl shapes), the transition
determinant identities in `Measure/Invariance.lean` (:349/:523/:548) are
canonical-pair only, and `ChartRegistration` has no measure connection.  The
gap is REAL — do not re-audit.

**Ruling: add the canonical API at the Integration layer** (new
`Analysis/Integration/Measure/ParamEvaluation.lean`), in PARAMETRIZATION form
(`Ψ : E → M` a `C¹` partial diffeomorphism, the `expMapDiffeo` shape), NOT
chart form.  Execution prompt: `Geometry/Comparison/VOLCOMP_V0_API_HANDOFF.md`
(brick V0).  V1a then becomes a one-line specialization at
`Ψ := expMapDiffeo g x`; V1b–V1d resume per `VOLUME_COMPARISON_PLAN.md`.
