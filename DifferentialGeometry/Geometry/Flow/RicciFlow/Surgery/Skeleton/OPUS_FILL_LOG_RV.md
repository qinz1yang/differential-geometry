# Lane RV log (reducedVolume truncation, queue entry 26)

- 2026-09-26: new `Topology/ReducedVolumeTruncation.lean` (not registered in the root aggregate).
  Truncation shape: not `max R (-B)`; `stageRegularizedExtendedAction` is
  `lowerBoundedIntegral L (fun t => -2 * B * t ^ 2)`, so `B` only enters as the integrand floor and
  the existing `*_congr_scalar_lower_bound` lemmas make everything `B`-independent once `R ≥ -B`.
- Floor: `ObservedHistory.exists_stageMetric_scalar_lower_bound` (from
  `∀ i, GeometricCutoffRecord H i p`; the stage-0 floor comes from compactness, then the
  `-3/(2(t+c))` barrier crosses surgeries; `b = 3/(2c)` on every `stageDomain`). Plain stage
  compactness is not enough: incoming slabs live on `Ico`, the scalar is not continuous up to the
  surgery time. Corollary `RetainedCoreHistory.exists_stageMetric_scalar_lower_bound_of_inCutoffClass`.
- Stability for `b ≤ B, C`: `regularizedCost_eq_of_scalar_lower_bound_le`,
  `regularizedDensity_eq_of_scalar_lower_bound_le`, `regularMinimizerEndpoints_eq_of_scalar_lower_bound_le`.
- `reducedVolume_eq_of_scalar_lower_bound_le` (limsup = integral at any `B₀ ≥ b`),
  `exists_reducedVolume_eq_lintegral_of_inCutoffClass`.
- Bounds: `regularizedDensity_le_exp` (any `B`, no floor needed: truncated action `≥ -(2B/3)v³`),
  `reducedVolume_le_of_scalar_lower_bound` (`≤ (4πv²)^{-3/2} e^{bv²/3} · vol(stage)`),
  `reducedVolume_lt_top_of_scalar_lower_bound`, `reducedVolume_lt_top_of_inCutoffClass`.
- Measurability: density = F(cost) (`regularizedDensity_eq_exp_of_regularizedCost_eq`,
  `regularizedDensity_eq_zero_of_regularizedCost_eq_top`, no scalar hypothesis);
  `measurable_regularizedDensity_of_isClosed_regularizedCost_le` from closed cost sublevel sets
  (lower semicontinuity of the endpoint cost, NOT in the tree). Measurability of
  `regularMinimizerEndpoints` itself: OPEN (needs closedness of the set of endpoints of regular
  minimizers: compactness of minimizing curves plus closedness of `RegularCrossing`).
- Compile: module oleans upstream were being rebuilt by a running wiring build, so compiled a
  scratch concatenation outside the repo (leaves defs + `InCutoffClass` copied verbatim, then the
  file body): 0 errors, 0 warnings; `#lint` with `mathlibStandardSet`: only `docBlame` on the copied
  defs. Axioms: propext, Classical.choice, Quot.sound. Real module compile still to do.
