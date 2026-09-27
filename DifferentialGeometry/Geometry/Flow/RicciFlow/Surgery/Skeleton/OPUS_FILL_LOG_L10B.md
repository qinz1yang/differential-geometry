# OPUS_FILL_LOG_L10B (slab-start slice bounds at `t₀ = a`)

## 2026-09-26 entry 1 (start)

Read: AGENTS.md, NAMING.md §2–6, L10 log, `DerivativeBoundExtension.lean` (uncommitted), EventData
(`IncomingSlab`, `MetricSmoothUpTo`, `MetricCutCapEvent.old_metric_eq`), `IsSolutionOn` (the metric
equation is imposed only at `RegularTime`, i.e. on `Ioo a s`; `scalarTime`/`scalarCont` hold on the
closed carrier), G1b (`ChartCurvatureRegularity`), `DerivativeRegularity`, `ScalarDerivativeBounds`
(terminal jets route), `TerminalTimeExtension` (`extendedMetric`, jointly smooth up to the end),
`UniformBounds`/`DensityRegularity` (`normSq0S_jointContMDiffOn`, `nablaKRmChartJoint`: jets jointly
smooth on any `J` from the chart Gram), C3B2 log (target quantifier shape).
Plan: (1) `hreg` from `smoothUpTo` via G1b on `J = Ico a s` (scalar and |∇R|²); (2) the start
derivative is bounded by the start metric's curvature jets (continuity of `∂ₜR` and of the jets
up to `a`, interior bound `abs_deriv_scalar_le_of_curvature_jets`); (3) `hstart` from
scale-invariant jet bounds of the post-event metric; (4) corollary with L10 `_of_slice`.
Compile: scratch module copy of L10 (`L10bScratch.L10`) in `scratchpad/l10b`.

## 2026-09-26 entry 2 (progress, 06:20 PDT)

Compiled in scratch (`L10bScratch.Start` on top of verbatim `L10bScratch.L10`): both `hreg`
(right time derivative of `R`, and `|∇R|²`, jointly continuous on `Ici a ×ˢ univ` at `(a, y)`)
from `smoothUpTo` via G1b on `J = Ico a s` only (no flow equation needed at `a`); joint continuity
of the curvature jets on `Ico a s ×ˢ univ` (`normSq0S_jointContMDiffOn` + `nablaKRmChartJoint`);
the start derivative bounded by the start metric's jets
`|∂ₜ⁺R(a,y)| ≤ n⁶ √|∇²Rm|²(a,y) + 2n⁴ |Rm|²(a,y)` (limit of the interior bound, no equation at `a`).
Next: scale-invariant packaging, the `_of_slice` corollary, retained-core supply.

## 2026-09-26 entry 3 (delivered, 06:15 PDT; failures first)

### NOT proved: `hstart` on the whole post-event slice from the tree's class data
- Derivative-matching route (brief): blocked. `IsSolutionOn` imposes `∂ₜg = -2Ric` only at
  `RegularTime` (open interior); a metric-only formula for `∂ₜR` at either endpoint would need
  continuity of `ΔR + 2|Ric|²` up to the endpoint (no chart formula/joint smoothness for `ΔR` in
  the tree) plus its invariance under the survivor partial diffeomorphism. The old slab's
  `DerivativeBoundBefore` bounds only `∂ₜR`, which is not a function of the metric alone, so it
  cannot be transported across the event without that formula.
- Route taken: the start derivative is bounded by the start metric's curvature jets (proved, no
  equation at `a` needed), so `hstart` follows from scale-invariant jets of the post-event metric
  above the threshold: `q < R(a,y) → ∀ k ≤ 2, |∇ᵏRm|²(g_a, y) ≤ K R(a,y)^(k+2)`, with `C` depending
  only on `K`. Remaining inputs (precise):
  (R) retained core: proved for every `y` that is a `RegularCrossing` image, given the old slab's
      jets clause near its end at the source point (`∀ᶠ t in 𝓝[<] a, q < R(t,p) → |∇ᵏRm|²(t,p) ≤
      K R(t,p)^(k+2)`). That clause is NOT in the tree's induction data (only derivative/gradient
      clauses are); it must come from the canonical-neighborhood witnesses (normalized-jet bounds of
      κ-solution models), no tree lemma found.
  (C) caps/collars (points of `Q` that are not regular crossings: static-cap images and the
      boundary of `old`): OPEN. Needs `|∇ᵏRm|² ≤ K R^(k+2)` for the glued cap from the
      `StaticCapWitness` `C^m` closeness (`modelOrder ≥ …`) at the neck scale plus the standard
      cap's positive scalar curvature and bounded jets; not attempted.

### Proved
File `Surgery/Topology/SlabStartSliceBounds.lean` (306 lines, new, unregistered; namespace
`…OrientedThreeStage.IncomingSlab`):
- `continuousWithinAt_derivWithin_Ici_scalar_at_start` = `hreg` (derivative), exact L10 shape.
- `continuousWithinAt_gradient_normSq_at_start` = `hreg` (gradient), exact L10 shape.
  Both from `smoothUpTo` only (G1b on `J = Ico a s`, `normGradSqFun_eq_chartInvGram_sum`).
- `curvDerivNormSq_continuousOn` (jets jointly continuous on `Ico a s ×ˢ univ`).
- `abs_derivWithin_Ici_scalar_le_curvature_jets_at_start`:
  `|∂ₜ⁺R(a,y)| ≤ n⁶ √|∇²Rm|²(g_a,y) + 2n⁴ |Rm|²(g_a,y)`.
- `abs_derivWithin_Ici_scalar_le_at_start_of_curvature_jets`,
  `abs_scalarDifferential_le_at_start_of_curvature_jet` (scale-invariant forms).
- `exists_slice_bounds_at_slab_start (K) (hK) : ∃ C : ℝ≥0, 0 < C ∧ ∀ {P a s q} (G), 0 ≤ q →
  jets(K) → hreg ∧ hstart ∧ hreg_grad ∧ hstart_grad` (L10 shapes, `C` uniform in the slab).
- `exists_derivativeBoundBefore_extend_at_start`: same `C`, `0 < q`, jets(K) →
  `∃ η, 0 < η ∧ a + η < s ∧ DerivativeBoundBefore (2C) (2q) (a+η) ∧ GradientBoundBefore …`
  (L10 `_of_slice` at `t₀ = a`; the `…Before … a` input is vacuous).
File `Surgery/Topology/RetainedCrossingJets.lean` (148 lines, new, unregistered):
- `CheegerGromovCompactness.curvDerivNormSq_restrictOpen` (promotion candidate: belongs in
  `Curvature/CurvatureOperator/Derivatives/Restriction.lean`).
- `TerminalLimitMetric.tendsto_curvDerivNormSq`, `.tendsto_scalar`,
  `.curvDerivNormSq_le_of_eventually` (jets of the terminal metric are limits along the slab).
- `MetricCutCapEvent.RegularCrossing.curvDerivNormSq_eq` (jets preserved by the survivor map),
  `curvDerivNormSq_output_le_of_regularCrossing`, `curvDerivNormSq_le_at_slab_start_of_regularCrossing`
  (supplier (R) for the next slab `G : Q.IncomingSlab s s'` with `G.flow.base.metric s = outputMetric`).

Compile: file 2 in place `LEAN_NUM_THREADS=2 lake env lean -DmaxSynthPendingDepth=3
-Dweak.linter.mathlibStandardSet=true`: no output. File 1 imports the uncommitted
`DerivativeBoundExtension` (no olean): scratch-module pattern, `scratchpad/l10b`
(`L10bScratch.L10` = verbatim L10 file; `L10bScratch.Start` = file 1 with only the import line
changed, checked by `diff`), same flags: no output. Audit: `#print axioms` (7 headline decls):
propext, Classical.choice, Quot.sound; `#lint` 0 errors (11 + 7 decls, 14 linters). Lines ≤ 100,
no comments/sorry/options beyond `autoImplicit false`; public names grep-unique. No `lake build`,
no git writes, nothing else edited.
