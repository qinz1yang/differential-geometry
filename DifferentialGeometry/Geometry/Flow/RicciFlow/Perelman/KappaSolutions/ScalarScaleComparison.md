- `cor:ksol-scalar-scale-comparison`, consequence part only. The two differential
  estimates `eq:ksol-scalar-differential-estimates` (`|∇R| ≤ η R^{3/2}`,
  `0 ≤ ∂_t R ≤ η R²`) are NOT produced here; they come from
  `thm:ksol-universal-derivative-estimates` at `(a,b) ∈ {(1,0),(0,1)}` plus the ancient
  trace Harnack inequality at vector zero, which the tree does not have. They enter as
  the single explicit input `ScalarDifferentialBounds`, shaped so the future producer can
  discharge it directly.
- Public declarations: `scalar_spatial_scale_comparison`,
  `scalarDifferential_eq_mfderiv_metricScalarAt`, `scalar_temporal_scale_comparison_of_le`,
  `scalar_temporal_scale_comparison`, `ScalarDifferentialBounds`,
  `ancientKappa_spatial_scale_comparison`, `ancientKappa_temporal_scale_comparison`,
  `ancientKappa_scalar_scale_comparison`, `ancientKappa_scalar_scale_comparison_three`.
- Axiom audit (fresh, saved-source copy): the first eight are standard-only
  (`propext`, `Classical.choice`, `Quot.sound`). `ancientKappa_scalar_scale_comparison_three`
  additionally carries `sorryAx`, inherited from `ancientKappa_scalar_pos` of
  `ScalarPositive.lean`, whose complete bounded-curvature forward-flatness dependency
  (`UpstreamForwardFlatness`) is explicitly delegated. The axiom-clean route keeps
  `0 < R` as an explicit hypothesis (`ancientKappa_scalar_scale_comparison`).
- Route for the spatial half `eq:ksol-spatial-scale-comparison`: put
  `u = (2/η) R^{-1/2}`. Then `du(v) = -(1/(η R √R)) dR(v)`, so `|du(v)| ≤ |v|_g`
  pointwise, and `ofReal_abs_sub_le_riemannianEDistOf`
  (`Geometry/Metric/CompleteMetricExists.lean`) turns that into
  `|u(x) - u(y)| ≤ d_g(x,y)` with no minimizing geodesic, no completeness and no
  dimension hypothesis. With `d_g(x,y) ≤ η⁻¹ R(x)^{-1/2}` this gives
  `½ R(x)^{-1/2} ≤ R(y)^{-1/2} ≤ (3/2) R(x)^{-1/2}`, hence the `4/9` and `4` factors.
  Note: `exists_lt_of_edistOf_lt` / `edistOf_le_metricPathELength` of
  `Geometry/Comparison/DistanceHessianLocal.lean` are NOT needed — the whole
  path-integration step is already packaged in `ofReal_abs_sub_le_riemannianEDistOf`,
  whose hypothesis is exactly `mvfderiv f x v * mvfderiv f x v ≤ g.inner x v v`.
- Route for the temporal half `eq:ksol-temporal-scale-comparison`: `R` is nondecreasing
  (`monotoneOn_of_hasDerivWithinAt_nonneg`, `Analysis/Calculus/Deriv/MeanValue.lean`), and
  the auxiliary `s ↦ R(s)⁻¹ + η s` has derivative `η - R'/R² ≥ 0`, so it is nondecreasing
  too; on a window of length `(2ηR(t))⁻¹` that yields `R(s)⁻¹ ≤ (3/2) R(t)⁻¹`.
- Elaboration traps found (worth avoiding elsewhere):
  * `(mfderiv I 𝓘(ℝ, ℝ) f x v : ℝ)` does NOT elaborate at ℝ inside `binop%`/`|·|`
    (`failed to synthesize HMul ℝ (TangentSpace 𝓘(ℝ, ℝ) (f x)) _`). Use the tree idiom
    `(show ℝ from mfderiv I 𝓘(ℝ, ℝ) f x v)`, as in `Integration/DivergenceTheorem/Gradient.lean`.
  * `simpa using DFunLike.congr_fun h v` fails on `(c • L) v` because the equation lives in
    `TangentSpace 𝓘(ℝ, ℝ) (φ (f x))`; plain `exact` succeeds, since
    `(c • L) v ≡ c * L v` definitionally.
  * `ScalarPositive.lean` is stated over `[InnerProductSpace ℝ E]`, not `[NormedSpace ℝ E]`.
    Calling `ancientKappa_scalar_pos` from a `NormedSpace` section produces a
    `whnf`/`isDefEq` heartbeat timeout, not a clean synthesis error. The dimension-three
    corollary therefore lives in its own `InnerProductSpace` section; the rest of the file
    keeps the weaker `NormedSpace` assumption.
- Chain rule used: private `mfderiv_real_comp` (`HasDerivAt φ c (f x)` composed with
  `MDifferentiableAt f x`), modelled on `hasMFDerivAt_rexp` of
  `Integration/DivergenceTheorem/Gradient.lean`.
- `ScalarDifferentialBounds` takes the time derivative as
  `derivWithin (fun s => F.S.scalar s x) D.carrier t`: an ordinary derivative at interior
  times and the one-sided derivative at the terminal time, matching
  `CanonicalWitness.time_derivative`'s `Set.Iic t` convention on the carrier `(-∞,0]`.
  Differentiability in time is not assumed separately — it is the actual `IsSolutionOn`
  field `scalarTime`, so the derivative on the comparison window `[t-(2ηR)⁻¹, t]` is
  obtained by `DifferentiableWithinAt.hasDerivWithinAt` on `D.carrier` followed by
  `HasDerivWithinAt.mono`. Stating the bound on `Set.Iic s` for each `s` separately would
  NOT work: at the left endpoint of the window the one-sided and two-sided derivatives are
  different derivWithin values.
- Verification: `LEAN_NUM_THREADS=2 lake env lean
  DifferentialGeometry/Geometry/Flow/RicciFlow/Perelman/KappaSolutions/ScalarScaleComparison.lean`,
  23.3 s, empty output (no errors, no warnings). Fresh 9-declaration axiom audit on a
  scratch copy of the saved source, 23.2 s. Not registered in `DifferentialGeometry.lean`,
  not committed; no named artifact refresh performed, so downstream consumers need one
  exclusive-window refresh before importing.
