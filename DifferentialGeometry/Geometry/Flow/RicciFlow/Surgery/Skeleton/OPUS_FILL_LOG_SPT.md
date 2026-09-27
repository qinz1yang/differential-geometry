# OPUS fill log SPT: spatial canonical-witness transport API (2026-09-26)

Worker lane SPT. Scope: SW-S / SW-P / SW-R / SW-T of `DESIGN_C4.md` §4. New files only under
`Perelman/CanonicalNeighborhood/` (at most two). Read-only compiles with
`LEAN_NUM_THREADS=2 lake env lean <file>`. No git writes, no lake build.

## Shapes consumed by DESIGN_C4 case (B) (quoted)

- step 3: "**Restrict** `W_Q` to `standardCapWindow D` (SW-R). This works because `‖z‖ < Dw+1` and
  the `Q(T)`-ball of radius `4·C_std/√R_Q ≤ 4C_std` stays inside `window(D−1)`".
- step 4: "**Metric-close transport** from `(Q T)|_D` to `S.base.metric T` on the same window, with
  the identity map (SW-T). Output: accuracy `2α = ε`, constants `2C_std`."
- step 5: "Apply SW-P along `Φ := fun v => (Ξ v)` (after L7a turns it into a `PartialDiffeomorph`
  with open image), then SW-S with factor `q`."
- step 6: "`gflow t = ... (Gk.flow.base.metric t).restrictOpen _` ... Then apply SW-P along the
  inclusion." Capture: "`B_{g(t)}(y, 3·radius) ⊆ image`".

## Progress

- 00:00 read AGENTS/NAMING/DESIGN_C4 and suppliers; started.
- +0:40 SW-S done and compiling: `SpatialCanonicalWitness.scaleMetric` (all fields, all four
  alternatives), `capTubeHasNeckChart.scaleMetric`, helpers for chain/neck/cap/round/secLower/deep
  in `SpatialCanonicalWitnessTransport.lean`. Starting SW-P (isometric pushforward).
- +1:40 isometry invariance lemmas compile (`metricScalarAt_eq_of_isometryOn`,
  `rmNormSq_eq_of_isometryOn`, `metricRm04At_eq_of_isometryOn`,
  `mfderiv_metricScalarAt_eq_of_isometryOn`, `secLower_image_of_isometryOn`) for a
  `PartialDiffeomorph` isometric on its source. Kernel deterministic timeout met once in the
  gradient lemma (Eq.trans across `TangentSpace 𝓘(ℝ,ℝ) (R x)` codomains); fixed by stating the
  chain in `ℝ` via `show ℝ from`. Next: neck/chain/cap/round/witness `map`.
- +2:30 pushforward layer compiles: `MetricComparisonOn.mapIsometry`, `SpatialNeck.pushforward`,
  `SpatialOrderedNeckChain.pushforward`, `SpatialLocalNeck.pushforward`,
  `SpatialLocalCap.pushforward`, `SpatialRoundComponent.pushforward`,
  `SpatialCanonicalAlternative.pushforward` (all four alternatives; whole-component clause by a
  clopen argument, no extra hypothesis). Name `map` clashes with the structure field `map`, so the
  operation is called `pushforward`. Next: witness-level pushforward (balls, depth, volume).
- +3:20 `SpatialCanonicalWitness.pushforward` (all fields) and
  `capTubeHasNeckChart.pushforward` compile. Hypotheses: `e : PartialDiffeomorph I3 I3 N M ∞`
  isometric on `e.source` (bilinear), a compact source ball `riemannianClosedBallOf h x R ⊆ e.source`
  with `2 * W.radius < R`, and the neck windows (neck alternative / chain necks / tube-chart neck)
  inside `e.source`. Next: restriction to an open set and the global injective local-isometry form.
- +4:10 SW-R and the global form compile: `SpatialCanonicalWitness.restrictOpen` (to an open `O`,
  via `pushforward` along `(subtypeVal O).symm`; needs `[SigmaCompactSpace O]`),
  `SpatialCanonicalWitness.pushforwardOfInjective` (injective local diffeomorphism `f`, witness for
  `localPullMetric g f hf`), each with its `capTubeHasNeckChart` lemma. File A ≈ 1140 lines.
  Starting SW-T in a second file (budget ≈ 350 lines left).
- +5:10 SW-T (alternative level) compiles in `SpatialCanonicalWitnessComparisonTransport.lean`
  (checked by scratch concatenation with file A, since A has no olean): neck, deep cap, and the
  neck/cap alternative under `MetricComparisonOn (fun _ => g) (fun _ => g') F U {0}`.
  A `whnf` heartbeat timeout in the cap theorem came from elaborating `exact hdepth ... rfl ...`
  with all implicits open; fixed by naming the implicits and `mem_singleton 0`.
- +5:40 final state. Both files compile with the project options
  (`-DmaxSynthPendingDepth=3 -Dweak.linter.mathlibStandardSet=true`): file A directly
  (`LEAN_NUM_THREADS=2 lake env lean`), file B via scratch concatenation with A (A has no olean).
  0 errors, 0 warnings. Axioms of all 11 headline declarations: `propext, Classical.choice,
  Quot.sound`. The local `secLower_scaleMetric` clone was removed in favour of the existing
  `FiniteHorn.secLower_scaleMetric` (ParabolicRescalingReduction.lean:208). Files are NOT in the
  root aggregate (lane rule: edit nothing else).

## Result (failures first)

1. SW-T is only proved at the alternative level (neck, deep cap). The witness-level transport
   (scalar/rm/volume/gradient/radius fields at accuracy 2α, constants 2C) is NOT proved:
   - gradient: no supplier; `ScalarGradientComparison` (WitnessTransport.lean:626) is an
     unproved hypothesis family, so the `gradient` field cannot be transported;
   - rm bound with constant 2C: the available comparison bounds are
     `rmNormSq_image_le_of_rmNormSq_le` (factor 324) or `riemannOp_norm_le` (needs a complete
     reference metric and a closed-ball comparison domain);
   - `radius_lower : (√R)⁻¹ ≤ radius` is tight: under a (1±δ) comparison the radius cannot be
     kept without a strict radius margin in the source (same phenomenon as failure 4 for depth).
   Round/positive components are not covered by SW-T (hshape: neck or cap, as in E3).
2. Universe: all operations require source and target in the same universe `u`
   (`SpatialRoundComponent.Z`, `CapCore.projective Z` live in the manifold's universe). DESIGN §2
   step 5 pushes from `standardCapWindow D` (Type 0) into a `Type u` carrier; this needs a
   ULift step that is not provided.
3. Reference-metric mismatch: the bridge output is `metricDerivNorm i (S T) ((Q T)|_D)
   (StandardCap.metric|_D)` (reference `StandardCap.metric`), while SW-T consumes a
   `MetricComparisonOn` (jets w.r.t. the source metric). Converting needs
   `MapMetricApproximationOn.ofMetricDerivNorm` with reference = source, i.e. a change of
   reference metric that is not in this lane.
