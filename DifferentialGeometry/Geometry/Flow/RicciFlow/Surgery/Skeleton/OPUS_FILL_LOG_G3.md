# G3 fill log

2026-09-26. Window solution map of the L-phase ODE at an interior data point. One new file, unwired:
`Perelman/LGeometry/Geodesic/WindowSolutionMap.lean` (440 lines, imports G1c `ClosedStartCurve` and
`Congruence`).

- Consumer shapes (DESIGN_22 §7): G3 is "Window solution map of the L-geodesic ODE from arbitrary
  `(s₀, x, V)`, smooth in data (repackage `exists_lPhaseAt`, `lRegularizedFamily_extend`)". H3a
  (`historyLExp`, uniqueness) and H3b ("composition of G3 maps and seam `F`") are not written yet,
  so no Lean signature exists to match. The statements below use the shape of G1b's
  `exists_lPhaseFlow_of_start` (variable base `p = (s₁, z)`, `Ψ (p, p.1) = p.2`).
- `exists_lPhaseFlow_of_regular`: `IsSolutionOn S`, `T - s0^2 ∈ D.regular` (any `s0`, so `s0 = 0`
  is included), chart state `z0` in `interior target`. It gives `W ∋ (s0, z0)` open,
  `W ⊆ Ioo (s0-ε) (s0+ε) ×ˢ univ`, and `Ψ` that is `C^∞` on `W ×ˢ Ioo (s0-ε) (s0+ε)`, solves the ODE
  (two-sided `HasDerivAt`), and stays regular and in the chart. It uses `exists_flow_on` on the
  time-augmented field. No reflection.
- (1) Agreement: `eqOn_lPhaseCurve_of_isLRegularizedGeodesicOn` (any `IsLRegularizedGeodesicOn` curve
  whose chart state is `z s₁`). `isLRegularizedGeodesicOn_lRegularizedCurve` covers the whole domain.
  `eqOn_lRegularizedCurve_lPhaseCurve` gives equality on `lRegularizedDomain ∩ K`, and
  `..._of_initial` is the seed case `z 0 = (ext x, trivToE x (2•Z))`.
- (2) Composition: `lPhaseState_eqOn` (same-chart state uniqueness on `K ∩ K'`) and
  `lPhaseFlow_comp_eqOn` (a window restarted from its own state agrees with the first window).
  `exists_lPhaseFlow_union` glues two windows: `C^∞` on
  `{p ∈ W₁ | (s₁, Ψ₁(p,s₁)) ∈ W₂} ×ˢ (L₁ ∪ L₂)`. That set is open, and the result is again an ODE
  solution.
- (3) Chart independence: `eqOn_lPhaseCurve_of_coordChange` (the manifold curves agree) and
  `lPhaseState_eq_coordChange`: `z₁ = (φ z₀.1, Dφ z₀.1 z₀.2)` on `K₀ ∩ K₁`, with
  `φ = ext x1 ∘ (ext x0).symm`. The conjugator is `C^∞` on the overlap by
  `contDiffOn_extChartAt_coordChange_prod_fderiv`. The proof is the chain rule and needs no
  trivialization identity.
- Compile: G1b/G1c prerequisites (`ChartCurvatureRegularity`, `ClosedStartPhase`,
  `ClosedStartCurve`) have no oleans. They were concatenated outside the repo into one scratch
  module, compiled with `lean -o`, and the test copy imports that module. Command:
  `LEAN_NUM_THREADS=2 lake env lean`, with no `-D` and no overrides. Clean.
  `linter.mathlibStandardSet` is clean, and `#lint` passed (14 declarations). Axioms for all
  11 public theorems: propext, Classical.choice, Quot.sound. Public names are unique library-wide.
