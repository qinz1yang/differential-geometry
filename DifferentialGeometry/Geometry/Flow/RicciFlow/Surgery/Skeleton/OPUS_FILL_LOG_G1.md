# G1 fill log

2026-09-26. File `Perelman/LGeometry/Geodesic/ClosedEndExtension.lean` (232 lines, new, unwired).
- Route: Ricci-flow continuation, not a non-Ricci Seeley extension. Short-time flow from `g(b)`
  (`exists_completeBoundedCurvatureSolutionOn_from_time_of_compact`) glued at `b` by
  `isSolutionOn_ite_of_ricciFlow`. The result is `IsSolutionOn` on `closed a d`, `b` regular, so
  `exists_lPhaseAt` / `lRegularizedFamily_extend` / `lRegularizedCurve_smooth` apply unchanged.
- Independence: `lRegularizedDomain`/`lRegularizedCurve`/`lExp`/`lExpDomain` equal for any two
  flows agreeing (metric and regular set) on times `≤ T`; closed-interval corollaries.
- `lake env lean`: clean. `#lint` on scratch copy: passed. Axioms: propext, choice, Quot.sound.
- OPEN: closed START end (`T - v² = time j`). A backward Ricci continuation does not exist in
  general. A non-Ricci extension breaks `IsSolutionOn`, and `chartRicci_joint` needs the equation.
  So that case needs metric-only regularity of Ric/∇R (or a one-sided ODE lemma). Not built.
- Promotion: `exists_isSolutionOn_extension_past_right_endpoint` belongs in `Solution/`.
