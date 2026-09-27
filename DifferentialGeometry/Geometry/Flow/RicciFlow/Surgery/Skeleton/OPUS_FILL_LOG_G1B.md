# G1b fill log

2026-09-26. Closed START of the L-phase flow, no backward Ricci continuation. Two new files, unwired.

- `Solution/ChartCurvatureRegularity.lean` (95 lines). The metric-only Ricci and dR facts, in the
  shape of `chartRicci_joint` / `chartScalarDeriv`, as `ContDiffOn` on `J ×ˢ interior target` from
  `hmetric : ContMDiffOn … (J ×ˢ univ)`. `J` is arbitrary, so the statements are one-sided at a closed
  end. There is no flow equation. Source: Ricci and scalar curvature in the chart are polynomials in
  the spatial jets of the Gram matrix (`WithinSmoothness`, `ChartCurvature/Scalar`).
  `chartGramFamilySmoothWithinOn_of_jointContMDiffOn`, `chartRicci_contDiffOn_of_jointContMDiffOn`,
  `chartScalarDeriv_contDiffOn_of_jointContMDiffOn` (namespace `…RicciFlow.SolutionOn`).
- `Perelman/LGeometry/Geodesic/ClosedStartPhase.lean` (500 lines):
  - `lPhaseField_contDiffOn_of_jointContMDiffOn`: `ContDiffOn` of `uncurry (lPhaseField S T x0)` on
    `{p | T - p.1^2 ∈ J ∧ p.2.1 ∈ interior target}`. `lPhaseField_contDiffAt_of_jointContMDiffOn` is
    the open-`J` corollary. It is the drop-in metric-only replacement for `lPhaseField_smoothAt`.
  - `exists_lPhaseFlow_of_start`: `hmetric` on `Ico a c`, `0 < s0`, `T - s0^2 = a`. It gives a
    phase flow `Ψ (p, s)` with variable base time `p = (s₁, z)` near `(s0, z0)`, `C^∞` on
    `W ×ˢ Ioo (s0-ε) (s0+ε)`. It solves the true L-phase ODE (two-sided `HasDerivAt`) for every
    `s ∈ Ioc (s0-ε) s0`, and `T - s^2 ∈ Ico a c` there. Route: Borel/Seeley extension of the
    reflected field across `s = s0` (`exists_contDiff_extension_Ici_prod_nhdsWithin`), then
    `exists_flow_on`. `exists_lPhaseAt_of_start` is the fixed-base (`exists_lPhaseAt`) shape.
  - Independence at the start: `lPhaseField_congr`; `lRegularizedDomain_subset_of_metric_eq` and
    `lRegularizedCurve_eqOn_of_metric_eq` (only `IsSolutionOn S₁`; `S₂` is any extension, for example
    a non-Ricci one past `a`). The private transfer lemma duplicates G1's public
    `IsLRegularizedCurveOn.of_metric_eq`: merge once both files are built.
- Consumers (DESIGN_22 §7): G3, "Window solution map of the L-geodesic ODE from arbitrary
  `(s₀, x, V)`, smooth in data". H3b, `isOpen_historyLExpDomain_and_contMDiffOn_historyLExp` "requires
  G1 when T − v² or T is a closed end". `exists_lPhaseFlow_of_start` is the G3 window map at a
  closed start.
- Compile: `lake env lean -DmaxSynthPendingDepth=3` (file 1 directly; file 2 on a scratch
  concatenation, since file 1 has no olean). Clean with the standard linter set. `#lint` passed
  (11 declarations). Axioms for all 10 public theorems: propext, Classical.choice, Quot.sound.
- OPEN (not built): curve-level assembly at `v` with `T - v^2 = a`. For `Z` near `Z0` with
  `Ico 0 v ⊆ lRegularizedDomain S T x Z0` and chart state converging in one chart as `s → v⁻`, a family
  `β` that is `C^∞` on `V ×ˢ Ioo (v-δ) (v+δ)` and equals `lRegularizedCurve S T x Z` on `Ioo (v-δ) v`.
  Needs `lRegularizedFamily_extend` at `s₁ < v`, joint smoothness of the chart velocity in `(Z, s)`,
  ODE uniqueness on `(s₁, v)`, and a gluing lemma for `IsLRegularizedCurveOn`. That is about 350
  lines. Alternatively refactor `Geodesic/Basic`/`ExponentialMap` to take `MetricFamilySmoothOn`
  instead of `IsSolutionOn` (hS is used only through `lPhaseField_smoothAt`). Then a non-Ricci
  extension works, but a global time extension of the metric family below `a` is also missing.
- Instances: my files use `[InnerProductSpace ℝ E]` only, because `WithinSmoothness` needs it. The
  tree's `Geodesic` section has a separate `[NormedSpace ℝ E]`, which is defeq only for concrete `E`.
