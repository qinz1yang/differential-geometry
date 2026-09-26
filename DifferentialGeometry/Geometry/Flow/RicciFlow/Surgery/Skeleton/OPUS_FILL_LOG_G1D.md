# G1d fill log

2026-09-26. Closed END as base time `T = b`, metric-only. One new file, unwired:
`Perelman/LGeometry/Geodesic/ClosedEndBase.lean` (190 lines, imports G1c).

- Obstruction, now a theorem: `lRegularizedDomain_eq_empty_of_not_mem_regular` (`T ∉ D.regular`
  gives an empty domain). For `S` on `closed a b`, `b ∉ regular`, so the domain at base `b` is
  empty. G6's conclusion at `T = b` is FALSE for that `S`, whatever the proof. It must be stated
  for a re-indexed `S₂ := ⟨S.base⟩ : SolutionOn D₂` with `Ioc a b ⊆ D₂.regular` (for example
  `closed a d`, `d > b`). `SolutionOn` is only a wrapper, so this needs no extension: times
  `b - s² ≤ b`, and the metric past `b` never enters. But `IsSolutionOn S₂` is false in general.
- (1) `lPhaseField_contDiffAt_of_closed_end`: `hmetric` on `Ioc a b`, `s² < b - a`, giving
  `ContDiffAt` of `uncurry (lPhaseField S b x0)` at `(s, z)`. Two-sided in `s`, from G1b's
  lemma with `J = Ioc a b`. No extension is needed.
- (2) Metric-only local existence: `exists_lRegularizedFamily_of_lPhaseField_contDiffAt` (any `S`,
  no `IsSolutionOn`; hypotheses are `T - s² ∈ D.regular` and phase-field `ContDiffAt` for
  `s² < ρ`). `exists_lRegularizedFamily_of_closed_end` and
  `zero_mem_lRegularizedDomain_of_closed_end` apply it at base `b` for `S₂` (`hreg : Ioc a b ⊆
  D.regular`).
- NOT delivered: the `b`-base analogues of `exists_lPhaseAt`, `lRegularizedFamily_extend`,
  `lRegularizedCurve_smooth` and uniqueness. Every tree lemma takes `hS : IsSolutionOn`, used only
  through `lPhaseField_smoothAt` (Basic:479). Cloning the chain is about 2000 lines.
- (3) Independence: G1's `lRegularizedDomain_eq_of_metric_eq_of_le` already covers it (no `hS`).
  `lRegularizedCurve_eq_of_metric_eq_of_le` needs `hS₂`, so it is subject to the same refactor.
- (4) G6 cannot be restated. Its proof uses `IsSolutionOn` through Range
  (`mem_lRegularizedDomain_and_edist_lt_of_local_gradient_ricci_bounds`), parabolic rescaling,
  and the Shi/curvature bounds. Precise glue, pick one:
  (A) Refactor. Replace `hS` in `Geodesic/Basic`, `ExponentialMap` and `Ray/Range` by
      `hF : ∀ x0 s z, T - s² ∈ D.regular → z.1 ∈ interior (extChartAt I x0).target →
      ContDiffAt ℝ ∞ (uncurry (lPhaseField S T x0)) (s, z)`. Keep the Ricci/Shi facts as
      hypotheses on times `≤ T` only, which already hold for `S` on `Icc`. `IsSolutionOn → hF`
      is `lPhaseField_smoothAt`; `hF` at `b` for `S₂` is (1). Then G6 is stated for `S₂`.
  (B) H9 side. Give the common flow on `closed a t'` with `t' > t` whenever the history continues
      past `t` (the active stage or seam window is a Ricci flow past `t`), so `t ∈ regular` and G6
      applies unchanged. `t = horizon` still needs the slab past the horizon (DESIGN_22 F4).
- Compile: scratch concatenation outside the repo (G1b 1, G1b 2, G1c, G1d), then
  `LEAN_NUM_THREADS=2 lake env lean`, no `-D`: clean. `#lint`: passed (22 declarations).
  `linter.mathlibStandardSet`: clean. Axioms (5 new public theorems): propext, choice, Quot.sound.
