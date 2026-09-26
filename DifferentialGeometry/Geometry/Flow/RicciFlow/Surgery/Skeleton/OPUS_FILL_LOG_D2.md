# OPUS fill log D2 — CapWindow derivative and gradient bounds (entry 20)

2026-09-26
- New module `Surgery/Topology/CapWindowDerivativeBounds.lean` (380 lines). Nothing else edited.
- Headline `RetainedCoreHistory.exists_derivative_gradient_bounds_of_cap_window_trace`: the bridge's
  hypotheses (with `ε η N` instantiated internally: `ε = η = min` of the jet and scalar thresholds,
  `N = 4`) ⇒ `c·scale ≤ R`, `|∂ₜR| ≤ C'R²`, `|dR(v)| ≤ C'R√R|v|` at `(y, t)` on `Gk.flow`.
  `Cbirth c C'` chosen after `Θ C` and before `D`; `C'` depends only on `Θ` (standard-solution
  bounds on `[0, Θ]`, `Θ < 1 = uniformStandardLifetime`).
- Jet source: not `exists_uniform_prepared_incoming_cap_curvature_derivative_bound` (its own small
  `η` age range only). Used the bridge's `C⁴` closeness to `Q` on `[0, Θ]` via new
  `StandardCap.exists_uniform_curvature_derivative_bound_of_standard_metric_close_on_opens`
  (generalizes `exists_uniform_curvature_bound_of_standard_metric_close_on_opens` to order `j`).
  Scalar lower bound: `exists_uniform_standard_metric_scalar_lower_comparison` +
  `exists_standard_scalar_lower_bound`.
- No time transport needed: jets transported spatially (`curvDerivNormSq_localPullMetric_scaleMetric`,
  `ObservedHistory.curvDerivNormSq_backwardSurvivorIncomingMetric_terminal`, scalar analogues), then
  `abs_deriv_scalar_le_of_curvature_jets` / `abs_scalarDifferential_le_of_curvature_jet` applied to
  `Gk.flow` at the interior time `t ∈ (time k, s)`; scale-invariant forms via
  `abs_derivWithin_scalar_le_of_scaled_curvature_jets`, `abs_scalarDifferential_le_of_scaled_curvature_jet`.
- Compile: bridge and `StandardActionComparison` (+ `Unweighted`, `ParabolicScaling`) have no olean;
  compiled a scratch concatenation (5 files, outside repo) with `LEAN_NUM_THREADS=2 lake env lean`:
  0 errors, 0 warnings. Axioms of all 8 new declarations: propext, Classical.choice, Quot.sound.
  `#lint only` (unusedArguments simpNF checkType synTaut unusedHavesSuffices impossibleInstance
  nonClassInstance): passed. Module build and 13-linter audit left to lead.
