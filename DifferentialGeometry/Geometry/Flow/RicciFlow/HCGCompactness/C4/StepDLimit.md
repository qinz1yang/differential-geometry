# StepDLimit.lean — notes (MSM135 Ch4 Step D, D3e)

The D3e assembly: `PointedRiemannianManifold` for the direct-limit manifold.

## State (2026-07-07): DONE, sorry-free, axiom-clean, full `lake build` green

- `limitPointed S O₀ ginf` — metric-generic form: carrier `S.Lim`, basepoint `incl 0 O₀`, metric
  supplied; all structure fields (`charted`/`smooth`/`sigmaCompact`/`t2`/`t2TangentBundle`)
  auto-synthesize from the D3a–D3c instances of `Geometry/Topology/DirectLimitManifold.lean`.
- `limitPointedCoc S O₀ g hg` — **the full D3 endpoint**: per-factor metrics + the isometry
  cocycle (`SmoothSeqSystem.MetricCocycle`, = D2c's conclusion shape) in, pointed bundle out, with
  metric `g∞ = S.limitMetric g hg` (D3d) satisfying `(incl k)^* g∞ = g k`
  (`SmoothSeqSystem.limitMetric_pullback`).

`#print axioms limitPointedCoc = [propext, Classical.choice, Quot.sound]`.

## D4a DONE (2026-07-07, later session) — the comparison-map package
`limitCGMaps S O₀ g hg : PointedRiemannianCGMaps (factorSeq S O₀ g) (limitPointedCoc S O₀ g hg) id`
— sorry-free, axiom-clean, `lake build` green (3790 jobs).  Components: `factorPointed`/`factorSeq`
(stage members as pointed manifolds, basepoints `F_{0≤k} O₀`), `rangeExhausts` (`ExhaustsByOpen`
of the stage ranges = `lbl379` packaged: open + monotone + `isCompact_exists`), the per-`k`
`SmoothSeqSystem.inclPartialDiffeo` (in `DirectLimitManifold.lean`: `(incl k)⁻¹` as a
`PartialDiffeomorph Lim (A k)` with source the stage range) and `invIncl_incl_le` (basepoint
transport `(incl k)⁻¹ (incl j a) = F_{j≤k} a`).  Also landed upstream:
`SeqSystem.instPreconnectedLim`/`instConnectedSpaceLim` (monotone-union of preconnected ranges —
the endpoint's `hconn` and D5's connectedness input).

**ELABORATION LESSONS (cost ~5 iterations):** `PointedRiemannianCGMaps`'s file context is
`[NormedAddCommGroup E] [InnerProductSpace ℝ E]` with **NO explicit `[NormedSpace ℝ E]`** — its
baked `PointedRiemannianManifold`-argument spine uses `InnerProductSpace.toNormedSpace`.  A caller
section declaring BOTH `[NormedSpace ℝ E]` and `[InnerProductSpace ℝ E]` produces a NON-DEFEQ
NormedSpace slot ⟹ the structure's `I`-metavariable freezes and the error surfaces as a bogus
`Application type mismatch … PointedRiemannianManifold ?m` at an unrelated argument.  FIX: mirror
the consumer file's instance set exactly (drop `NormedSpace`, keep `InnerProductSpace`).  Diagnose
with `#check @Struct` probes (the probe shows the real baked spine).

## D4b/c source-domain bridge checked (2026-07-09)

`limitCGMapsOf` separates the sequence-stage metrics from the cocycle family used to glue the
limit metric. `limitCGConverges` takes uniform compact-open seminorm convergence on every stage and
constructs `PointedRiemannianCGConverges` for the direct-limit comparison maps. The proof identifies
the restricted limit metric with the pullback of the stage-limit metric using
`limitMetric_of_mem`, transports all three metric slots by
`metricDerivNormSupOn_pullback_image`, and removes the target open subtype with
`metricDerivNormSupOn_restrictOpen`.

Focused verification passed without new `sorry`. The remaining D4 endpoint packaging is the
ambient-target lift: current chain instantiation has codomain carrier `U k`, while the final
compactness conclusion needs codomain carrier `M k` with target set `U k`. The next API should lift
`inclPartialDiffeo` through the open-subtype embedding, not reprove the convergence estimate.

## D5 distance cornerstones DONE (2026-07-07, same session, §StepD5) — green + axiom-clean
1. `enorm_mfd_incl` — **pointwise isometry** `‖mfderiv (incl k) a v‖ₑ = ‖v‖ₑ` under the two
   `RiemannianBundle` letI's.  Proof = the `TangentNormDiamond` idiom verbatim:
   `attribute [-instance] Tensor0SBundle.tangentSpace_normed*` (WITHOUT this,
   `norm_eq_sqrt_real_inner` fails to synthesize the fiber `InnerProductSpace` — the Tensor0S
   norm instance shadows the RiemannianBundle one), then `← ofReal_norm_eq_enorm,
   norm_eq_sqrt_real_inner` and `inner ℝ v v = metric.inner x v v` is `rfl`; finish with
   `limitMetric_pullback`.
2. `pathELength_incl` — `pathELength I (incl k ∘ γ) t₀ t₁ = pathELength I γ t₀ t₁` for `γ`
   `C¹` on `Icc`.  Via `pathELength_eq_lintegral_mfderiv_Ioo` + `setLIntegral_congr_fun` +
   `mfderiv_comp` (interior points; `Icc_mem_nhds`); the composed-enorm step is (1) BY DEFEQ
   (`exact enorm_mfd_incl …` — do NOT `simp [comp_apply]`, it makes no progress).
   `ContMDiffOn.mdifferentiableOn` takes `n ≠ 0` (`one_ne_zero`), not `1 ≤ n`.
3. `edist_incl_le` — `riemannianEDist_Lim (incl a) (incl b) ≤ riemannianEDist_k a b` via
   `le_of_forall_gt_imp_ge_of_dense` + Mathlib's `exists_lt_of_riemannianEDist_lt` (ℝ-line
   form, no unitInterval boundary manifold) + `riemannianEDist_le_pathELength` + (2).

4. `pathELength_invIncl` — the REVERSE comparison on range-contained paths: a `C¹` limit path
   staying in `range (incl k)` pulls back to a stage path of equal length (= (2) applied to the
   pullback + `pathELength_congr` on `incl ∘ (incl)⁻¹ = id`; `comp_contMDiffWithinAt` takes the
   POINT as first explicit arg).  This is the book's ball-level reverse-distance mechanism.

5. `edist_invIncl_le` — **the reverse comparison, assembled** (same session): if the closed
   `riemannianEDist`-`r`-ball at `x` lies in `range (incl k)` (quantifier form `hsub`) and
   `edist x y < r`, then `edist_k ((incl k)⁻¹x) ((incl k)⁻¹y) ≤ r`.  Proof: take a limit path of
   length `< r` (`exists_lt_of_riemannianEDist_lt`); its partial lengths dominate the distances
   (`riemannianEDist_le_pathELength` on `[0,t]` + `pathELength_mono`) so the path stays in the
   ball ⟹ in the range; pull back at equal length (`pathELength_invIncl`) and bound.
   Gotchas: `ℝ≥0∞` notation needs `open scoped ENNReal` but that makes `∞` AMBIGUOUS with the
   ContDiff `∞` — write `ENNReal` literally instead; `¹` (superscript) is not a valid identifier
   character.

6. `isCompact_cball_lim` — **the D5a compactness core, assembled** (same session): metric
   exhaustion (`hexh`, quantifier form — the honest input, D6-discharged from `2^k` balls +
   `lbl367`) + stage-ball compactness (`hcpt`, from members' properness) ⟹ closed limit
   `riemannianEDist`-balls of finite radius are compact.  Proof: exhaust at radius `r+1`, the
   ball is CLOSED (under `EMetricSpace.ofRiemannianMetric` the edist IS `riemannianEDist` by
   `rfl` — `ofEDistOfTopology` construction; letI chain copied from `MetricComplete`:
   `IsManifold 1` + `Manifold.metrizableSpace` + `T3` + `IsContinuousRiemannianBundle` +
   `ofRiemannianMetric`) and contained in `incl k '' (stage ball of radius r+1)`
   (`edist_invIncl_le` + `ENNReal.lt_add_right hr`), which is compact
   (`IsCompact.image`/`continuous_incl`); finish by `IsCompact.of_isClosed_subset`.

7. **`limitComplete` — D5a ENDPOINT DONE** (same session): `MetricComplete (limitPointedCoc S O₀
   g hg)` from the metric exhaustion (`hexh`) + stage-ball compactness (`hcpt`), with
   `[∀ k, PreconnectedSpace (A k)]` (→ `instConnectedSpaceLim` → `riemannianEDist_ne_top`, which
   also needs `[NeZero (finrank ℝ E)]` + `[I.Boundaryless]`).  Assembly: `unfold MetricComplete`;
   rebuild the letI chain on `S.Lim` (defeq to the baked bundle fields); `EMetricSpace.toMetricSpace
   (fun x y => Geometry.Riemannian.Exponential.riemannianEDist_ne_top …)` (edist = riemannianEDist
   by `rfl`, uniformity defeq by Mathlib's design); `ProperSpace.of_isCompact_closedBall_of_le 0`
   with `Metric.closedBall = closedEBall (ofReal r)` (`Metric.closedEBall_ofReal` +
   `mem_closedEBall'`, the `edist x y`-orientation) fed by `isCompact_cball_lim`; close with the
   ASCRIBED `exact (complete_of_proper : CompleteSpace S.toSeqSystem.Lim)` (the ascription pins
   `α` so the metric-vs-emetric uniformity defeq check fires).

### Historical D5 status: conditional consumer complete; concrete producer not complete.
The 2026-07-09 audit below retracts the claim that `hcpt` follows from members'
`ProperMetricOn`: the stages are open balls. Concrete D5 still needs metric exhaustion and an
honest compact-cover producer.

## 2026-07-09 review fill — hidden Hamilton assumptions live here, not in D3

The direct-limit review's hidden Hamilton assumptions are already separated at this layer.
`limitPointed`/`limitPointedCoc` consume finite-dimensionality, `CompleteSpace E`,
`SigmaCompactSpace`, `T2Space`, basepoint data, the smooth metric family, and the tangent-level
metric cocycle.  `limitCGMaps` consumes the open range exhaustion and basepoint transport.
`limitComplete` consumes the genuinely metric inputs: metric exhaustion (`hexh`), stage-ball
compactness (`hcpt`), preconnected stages, `[NeZero (finrank ℝ E)]`, and `[I.Boundaryless]`.

Completeness, connectedness, and Hamilton properness/exhaustion are therefore not consequences of
the bare direct-limit manifold. They remain consumer assumptions/proved endpoints in D4–D6 and
should not be hidden inside `SeqSystem` or `SmoothSeqSystem`.

## Consumers (future Step D lanes)
- D4a: comparison maps `Φ k := (incl k)⁻¹` — use `SmoothSeqSystem.contMDiffAt_invIncl` +
  `contMDiff_incl`; the reference-metric pullback identity is `limitMetric_pullback`.
- D5: completeness of `limitPointedCoc` (`MetricComplete`) via metric exhaustion plus compact
  stage covers; open-stage properness is unavailable.
- D6: instantiate `S`/`g`/`hg` from the D1/D2 outputs (subsequence re-index folds into the
  `SmoothSeqSystem`).

## 2026-07-09: D5 correction after concrete-stage audit

The earlier claim that `hcpt` follows from the members' properness is false for the actual open
ball stages. A restricted metric on an open ball need not be proper, even when the ambient member
is proper. Consequently the old conditional `limitComplete` is not a completed concrete D5
producer.

The corrected abstract API is checked:

- `HasCompactBallCover` asks directly for a compact stage cover of every finite limit ball.
- `compactCover_of_step` combines metric exhaustion with compact containment of each successor
  image.
- `compact_cball_cover` and `limitComplete_cover` derive compact limit balls and completeness.

This API removes the false open-stage properness assumption, but it does not manufacture metric
exhaustion. The attempted shortcut from relatively compact successor images to completeness is
also false: relative compact nesting alone does not prevent Cauchy sequences from approaching a
boundary missing from the union. This is route error 3/3 in the restarted audit.

Concrete D5 remains 0% as a theorem from the Step-D geometric data. Its dedicated abstract
consumer machinery is about 80%; the missing mathematical producer is a quantitative statement
that the distance from the limit basepoint to the complement of the `n`th stage tends to infinity.
The checked `tailSystem_compact` brick supplies compact containment once that metric-exhaustion
statement is proved.
