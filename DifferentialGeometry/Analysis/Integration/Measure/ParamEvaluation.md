# ParamEvaluation

## 2026-07-07 V0d global recombination completed

Status: `DifferentialGeometry/Analysis/Integration/Measure/ParamEvaluation.lean`
now verifies with the full global V0 parametrized volume formula stated and
proved.

Completed in this pass:

- Added chart-piece a.e.-measurability for the parameter-side density times a
  pulled-back POU weight, including the zero-extended indicator form needed for
  `lintegral_tsum`.
- Proved `riemannianMeasure_param_summand_eq`, the single POU summand formula
  converting the weighted chart-local contribution on `Ψ '' B` into the
  weighted parameter integral over `B ∩ Ψ ⁻¹' (chartAt H α).source`.
- Proved the support-restriction helpers
  `param_pou_piece_zero` and `tsum_param_pou_piece_eq_subtype`, reducing the
  parameter-side POU sum to the countable nonempty-support subtype.
- Proved `tsum_param_pou_piece_indicator_eq`, the pointwise collapse of the
  chart-piece indicator sum to the bare density on `B`.
- Proved the global V0 formulas:
  `riemannianMeasure_image_param_eq` for an arbitrary chart-subordinate POU and
  `riemannianVolumeMeasure_image_param_eq` for the canonical Riemannian volume
  measure.
- Added the set-form convenience API requested by the V0 handoff:
  `measurableSet_symm_image_param` and
  `riemannianVolumeMeasure_param_target_eq`, deriving the volume of a measurable
  target subset `A ⊆ Ψ.target` from the source integral over `Ψ.symm '' A`.

Current blockers:

- No blocker remains for the V0 global parametrized volume evaluation theorem
  in this file.
- The next frontier is downstream consumption: specialize this theorem to the
  normal-coordinate parametrization needed by the volume-comparison lane, then
  connect it to the Bishop-Gromov/Jacobian comparison estimates.

Current progress estimates:

- Full V0 evaluation theorem: 100% complete, because both
  `riemannianVolumeMeasure_image_param_eq` and the requested set-form corollary
  `riemannianVolumeMeasure_param_target_eq` are stated and proved in Lean.
- Dedicated V0 machinery: about 95% complete.  The theorem and recombination
  are checked; remaining polish is only downstream-facing adapters if later
  files need a slightly specialized statement.
- Volume-comparison measure-transfer brick: about 60% complete.  The global
  measure formula is now available, but normal-chart specialization and
  comparison-estimate integration are still absent.
- Whole volume-comparison lane: about 12% complete.  This closes the
  integration/measure foundation for parametrized images, not the
  Bishop-Gromov comparison theorem itself.

## 2026-07-07 V0 local parametrized volume API (historical pre-V0d snapshot)

Status: the file is verified so far with no local Lean errors.

Completed infrastructure:

- Defined `paramGramMatrix` and `paramDensity` for a `C^1` parametrizing
  `PartialDiffeomorph`.
- Proved source positivity: `paramDeriv_ker`, `paramGramMatrix_posDef`,
  `paramGramMatrix_det_pos`, and `paramDensity_pos`.
- Proved V0a Gram and density transformation in a fixed canonical chart:
  `paramGramMatrix_pullback_eq_mul`,
  `paramGramMatrix_det_pullback`, and
  `paramDensity_eq_abs_det_mul_chartDensity`.
- Proved V0b Euclidean chart-image change of variables:
  `lintegral_image_paramChartMap_chartDensity_eq`, plus the weighted form
  `lintegral_image_paramChartMap_mul_chartDensity_eq`.
- Proved V0c chart-local measure formulas:
  `chartLocalMeasure_image_param_eq_t2` and the weighted form
  `chartLocalMeasure_lintegral_image_param_eq_t2`.
- Added Borel-image and chart-piece helpers:
  `measurableSet_image_param_global`,
  `measurableSet_image_param`, and
  `measurableSet_param_chartPiece`.
- Added chart-local density regularity:
  `paramChartMap_contDiffOn`,
  `paramDensity_continuousOn_chart`, and
  `aemeasurable_ofReal_paramDensity_on_chart`.

Historical status: this section records the local API that existed before the
V0d recombination pass.  The former blocker and estimates are superseded by the
current V0d completion section above.
