# B6c — κ-solution properties of the ancient pointed limit (2026-09-26)

- Start. Read AGENTS.md, Skeleton/README, DESIGN_CROSSING (F9, B6), E-review digest (minimal lemma
  set), OPUS_FILL_LOG_B6A/B6B, `Surgery/Topology/AncientPointedFlowLimit.lean`,
  `TerminalScalarAncientLimit.lean`, `ParabolicNoncollapseLimit.lean`, `ParabolicOfSpatialAncient.lean`,
  `ModelWitness.lean` (`IsAncientKappaSolution`), `AncientCanonicalNeighborhood.lean:146`.
- Target structure (`ModelWitness.lean:193`): `IsAncientKappaSolution kappa F` has fields
  `kappa_pos`, `carrier_eq : D.carrier = Iic 0`, `regular_eq : D.regular = Iio 0`, `connected`,
  `complete : ∀ t ∈ D.carrier, MetricComplete (F.atTime t)`,
  `nonnegativeCurvatureOperator : ∀ t ∈ D.carrier, PointedFlowNonnegativeCurvatureOperator F t`,
  `globalScalarBound : ∃ C, PointedFlowScalarBounded F C` (`0 ≤ R ≤ C` at every `t ≤ 0`, every `x`),
  `noncollapsed : PointedFlowNoncollapsedAllScales F kappa`, `notFlat`.
  `kappa_canonical_neighborhood` (`AncientCanonicalNeighborhood.lean:146`) takes, for
  `P : PointedFlowData.{u,0,0} I3 ancientTimeInterval`: `IsAncientKappaSolution kappa P`,
  `PointedFlowScalarAtBase P 1`, `TangentOrientationSection P.M`.
- Finding (F9 routes). (a) the `∂R ≥ 0` route (`TerminalScalarAncientLimit.lean:405`) needs BOTH
  `hsign` (`0 ≤ ∂ₜR` on the approximants wherever `R > q`, with `q` bounded) AND a whole-slice bound
  `R(G 0) ≤ B` at time 0 (`hterminalBound`); the crossing derivative clause is a two-sided
  `|∂ₜR| ≤ Ctime R²` bound at canonical points, not a sign, so it supplies neither. (b) "complete,
  `Rm ≥ 0`, κ-noncollapsed ⇒ bounded curvature" is not a theorem of the tree and is false as a purely
  spatial statement; the tree's time-0 bounds (`exists_uniform_scalar_bound_outside_terminal_ball`,
  `terminal_limit_global_bound`) all run on `NormalizedSequence` whose `higher_good` gives
  `OrientedWitness` necks at every point with `R ≥ 2`. Neither route is complete for B6's limit.
- Finding (κ). `pointedFlowNoncollapsedAllScales_of_parabolic_of_curvatureOperator_nonnegative`
  (`ParabolicOfSpatialAncient.lean:141`) needs `∃ C, PointedFlowScalarBounded F C`, i.e. F9, and
  `ConvergesOn.parabolicallyKappaNoncollapsedBelowScale` (`ParabolicNoncollapseLimit.lean:246`) needs
  `ConvergesOn` of a `FlowSequence` of GLOBAL flows; B6a's approximants are local solutions on
  `W k n`, so the κ transfer must be redone for local approximants.
- 2026-09-26 (+~1.5h) File `Surgery/Topology/AncientPointedFlowLimitCurvature.lean` (239 lines) compiles
  clean in-repo (`LEAN_NUM_THREADS=2 lake env lean <file>`, no output; all imports have oleans; the
  file does NOT import B6a's module, it takes B6a's output shape as hypotheses). Proved:
  1. `curvatureOperator_nonnegative_of_local_pinching_limit` (generic `E`, `InnerProductSpace`):
     B6a's local convergence (`V`, `φ`, `ψ`, `metricDerivNormSupOn` on `V k × [−(k+1), 0]`) +
     approximant pinching `curvatureOperatorLowerBoundAt (h k n t) x … (rescalePinchingFunction
     (Q n) Phi (R))` eventually in `n`, every `t ∈ [−(k+1), 0]`, every `x : W k n`, `Q → ∞`,
     `AdmissiblePinchingFunction Phi` ⇒ `∀ t ≤ 0, ∀ x, metricAlgebraicCurvatureTensorAt (G t) x ∈
     algebraicCurvatureOperatorNonnegativeCone`. Suppliers: `curvatureOperator_nonnegative_of_metricCInf_admissible_pinching`
     (`MetricPinchingLimit.lean:77`), `curvatureOperatorLowerBoundAt_localPullMetric_iff`
     (`Naturality/Pullback/CurvatureOperator.lean:15`), `metricScalarAt_localPull` (`LocalCross.lean:307`),
     `…restrictOpen_mem_curvatureOperatorNonnegativeCone_iff` (`CurvatureOperator/Restriction.lean:19`).
  2. `riemannianMetricComplete_of_ancient_curvatureOperator_nonnegative`: an ancient solution on
     `infiniteClosed 0 0` with `Rm ≥ 0` and `G 0` complete has every `G t`, `t ≤ 0`, complete.
     Supplier: `complete_at_earlier_time_of_ricci_nonnegative` (`Estimates/MetricComparison.lean:470`,
     already the "metric bounded below by a complete one" route, `RiemannianMetricComplete.of_lower`).
  3. `ancient_pointed_flow_limit_curvatureOperator_nonnegative_and_complete`: 1 + 2 on exactly B6a's
     output (`MetricComplete P`, `ConnectedSpace P.M`, `V k = B(y∞, (k+1)/2)`, `G 0 = P.metric`,
     `IsSolutionOn` on `infiniteClosed 0 0`, the convergence clause verbatim).
  4. (package, I3) `FiniteHorn.isAncientKappaSolution_flowOfMetric_of_curvatureOperator_nonnegative`:
     `P : PointedRiemannianManifold.{v,0,0} I3`, `G` ancient solution, `G 0 = P.metric`, connected,
     every slice complete, `Rm ≥ 0`, `R(G t) ≤ C` for all `t ≤ 0`, `0 < κ`, `∀ ρ > 0,
     ParabolicallyKappaNoncollapsedBelowScale {G} κ ρ`, `R(P.metric)(basepoint) = 1` ⇒
     `IsAncientKappaSolution (κ / 30³) (flowOfMetric ancientTimeInterval P G hsol) ∧
     PointedFlowScalarAtBase … 1` — exactly the first two inputs of `kappa_canonical_neighborhood`
     (the orientation section is B8's). All-scales κ via `pointedFlowNoncollapsedAllScales_of_parabolic_of_curvatureOperator_nonnegative`.
- Verification: scratch copy + `#print axioms` + `#lint`: all four `[propext, Classical.choice,
  Quot.sound]`; 14 linters, 0 errors on 4 declarations. Lines ≤ 100; names unique library-wide.
- NOT delivered (no sorry, no named hypothesis; stated here as the remaining bricks):
  B6c-κ (parabolic κ of the limit from LOCAL approximants). Exact target, for B6a's data at `I3`
  and a history-side input `hnc : ∀ k, ∀ᶠ n, ∀ t ∈ [−(k+1), 0], ∀ z : W k n, ∀ ρ, 0 < ρ → ρ ≤ radii n →
  Icc (t − ρ²) t ⊆ Icc (−(k+2)) 0 → IsCompact (riemannianClosedBallOf (h k n t) z ρ) →
  (∀ s ∈ Icc (t − ρ²) t, ∀ y ∈ riemannianBallOf (h k n t) z ρ, ρ⁴ |Rm(h k n s)|²(y) ≤ 1) →
  ofReal (κ ρ³) ≤ vol_{h k n t}(riemannianBallOf (h k n t) z ρ)` with `radii → ∞`: conclude
  `∀ ρ > 0, ParabolicallyKappaNoncollapsedBelowScale {G} (κ / c) ρ`. The compactness clause makes
  `hnc` suppliable by B6b (a W-intrinsic ball with compact closure equals the ambient history ball).
  Obstacle found: the curvature transfer to the approximants must hold uniformly for
  `s ∈ [t − r², t]` at a fixed index; B6a's convergence is uniform in `s` but with reference
  `G 0`, while the only quantitative curvature-continuity lemma
  (`metricRmNorm_le_of_relative_two_jets`, `KappaSolutions/PointedNoncollapse.lean:123`) uses the
  limit slice `G s` as reference, and the reference-change constant
  (`exists_metric_deriv_norm_reference_bound`, `…/Norm/ReferenceChange.lean:134`) depends on `s`.
  Needed extra lemma: uniform-in-`s` reference equivalence and `iterCov` bounds of `G s` relative
  to `G 0` on compact `K × [a, 0]` (joint spacetime regularity of the limit), OR a uniform
  time-Lipschitz bound for `|Rm(h k n s)|²` from `hjets` (the frame-based `NormEvolution` API is
  the only supplier). `MetricComparisonOn`/`ConvergesOn` do not apply: they need global target flows
  and a global smooth pullback field on the limit. Estimated 1.5–3k lines.
  B6d (F9, whole-slice bound): `∃ C, ∀ t ≤ 0, ∀ x, metricScalarAt (G t) x ≤ C` for the crossing
  limit. Route (a) needs `hsign` + a time-0 bound, neither supplied; route (b) is not a spatial
  theorem. With B6c-κ and B6d, item 4 above closes `IsAncientKappaSolution` for B8 immediately
  (`notFlat` and `scalar = 1` come from the base normalization).
