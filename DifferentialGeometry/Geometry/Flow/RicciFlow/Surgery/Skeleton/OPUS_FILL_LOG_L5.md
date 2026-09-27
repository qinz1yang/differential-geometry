# OPUS_FILL_LOG_L5 (brick L5 of DESIGN_C3B: time shift and convergence)

## 2026-09-26

- Placement: DESIGN_C3B names no file for L5. New file
  `Perelman/StandardSolution/StandardWindowShiftConvergence.lean` (173 lines, not registered in the
  root aggregate, nothing else edited, no git writes, no `lake build`). It does not import L1/L4/L7
  (those have no oleans); L1's output is a hypothesis in L1's exact shape.
- (1) `StandardSolution.eventually_shifted_window_metricDerivNormSupOn_lt`: fixed window
  `W := standardCapWindow D`, `Θ < 1`, `0 < a`, `T n ≤ Θ`, `T n → T₀`, `J ⊆ Icc a T₀`;
  `hQ` = L1's conclusion for `Q` (pass `Q ∘ ρ`); `hclose : ∀ p e, 0 < e → ∀ᶠ n, ∀ τ ∈ Icc 0 (T n),
  ∀ i ≤ p, ∀ v, metricDerivNorm i (g n τ) ((Q n τ).restrictOpen W) (StandardCap.metric.restrictOpen W) v < e`.
  Conclusion (L4 `hconv` shape): `∀ K compact, ∀ p e, 0 < e → ∀ᶠ n, ∀ σ ∈ J,
  metricDerivNormSupOn K p (g n (σ + (T n - T₀))) ((Q'.val.metric σ).restrictOpen W) (… W) < e`.
  Time continuity of `Q'` from `exists_metric_time_lipschitz_constant_on_compact_regular`
  (`Geometry/Metric/Convergence/Time/CompactBounds.lean:109`) on `Icc (a/2) Θ ⊆ Ioo 0 1`.
  `eventually_forall_metricDerivNorm_lt_of_tendsto` turns the bridge's `(N n, ε n)` closeness
  (`N → ∞`, `ε → 0`) into `hclose`.
  L6 use: `S n := (window flow on W).timeShift (T n - T₀)` (then `timeRestrict`),
  `SolutionOn.timeShift_base_metric` gives `S n σ = g n (σ + (T n - T₀))` by `rfl`; this is the
  `A = 1` shift, simpler than `parabolicSolution … 1` (which carries `scaleMetric 1`).
  L6 must restrict the flows on `standardCapWindow Dₙ` to the fixed `W` (not done here).
- (2) `CheegerGromovCompactness.tendsto_metricScalarAt_of_metricDerivNormSupOn` (general manifold;
  belongs in `Geometry/Metric/Convergence/Scalar.lean` or next to
  `MetricCPConvergenceOn.tendstoUniformlyOn_metricScalarAt`), and
  `SolutionOn.tendsto_scalar_of_metricDerivNormSupOn`: from L4's exact `hconv`, `t ∈ D.carrier`,
  `x' → x`, gives L4's exact `hscalar`.
- (3) `exists_subseq_tendsto_standardCapWindow`: `‖z n‖ < r < D + 1` gives a subsequence and
  `z₀ : standardCapWindow D`, `‖z₀.val‖ ≤ r`, with `⟨z (φ n), _⟩ → z₀` in the window (L4's `hx'`).
- Compile: `LEAN_NUM_THREADS=2 lake env lean <file>` in place, also with
  `-Dweak.linter.mathlibStandardSet=true`: no output. Scratch copy: `#lint` 0 errors (14 linters),
  axioms `propext, Classical.choice, Quot.sound` for all five theorems. Names grep-unique.
