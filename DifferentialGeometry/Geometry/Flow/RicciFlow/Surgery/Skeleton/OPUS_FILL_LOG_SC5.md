# OPUS fill log SC5: T4′ consumer wave 5 = finite-window splitting + ℝ×N capture (2026-09-26)

Worker lane SC5. Scope: the two mathematical bricks T4′ still lacks after SC1–SC4: (1) finite-window
splitting of a `Rm ≥ 0` flow whose terminal slice contains a line; (2) ℝ×N whole-neighbourhood capture
(depth analogue of SC1-b): a class witness whose domain is captured by a chart close to a product
`N × ℝ` is a NECK, hence a `HistoryStrongNeck`. New files only; read-only compiles
(`LEAN_NUM_THREADS=2 lake env lean -DmaxSynthPendingDepth=3 -Dweak.linter.mathlibStandardSet=true`),
uncommitted imports through scratch modules `SC5.*` under the session scratchpad `sc5/`. No git writes,
no lake build, no root-aggregate edit, no committed file modified.

## Progress
- read AGENTS.md, SC1/SC2/SC3/SC4 logs, H13/H17/H18 digests.
- scratch chain `SC5.*` (SP1 + SC1 + SC3 files as on disk) building in background.

## Supplier survey (failures and existing mathematics first)

1. **Finite-window splitting is already in the tree except the line ⇒ rank-one step.** The strong
   maximum principle / Hamilton splitting on a closed window is committed:
   - `curvatureOperatorImageAt_finrank_trichotomy_at_right_endpoint` (`DimensionThree/ClosedRankTrichotomy.lean:173`):
     on `[a,b]` with `Rm ≥ 0` the terminal rank is spatially constant and `∈ {0,1,3}`;
   - `curvatureOperatorImageAt_finrank_eq_one_of_terminal_rank_one` (`DimensionThree/TerminalRankOne.lean:43`):
     terminal rank one ⇒ rank one on `(a,b]` (bounded curvature, completeness propagated);
   - `exists_surface_product_on_closed_interval_of_terminal_rank_one`
     (`DimensionThree/TerminalProductSplitting.lean:22`, `[SimplyConnectedSpace M]`): terminal rank one ⇒
     `M ≅ N × ℝ` with `g(t) = h(t) ⊕ dz²` for ALL `t ∈ [a,b]`, `N` simply connected, `h(t)` complete,
     `R_h > 0` on `(a,b]`.
   - time-0 Cheeger–Gromoll: `cheeger_gromoll_splitting` (`Geometry/Comparison/Splitting/IntrinsicLine.lean:22`);
     line ⇒ null plane at every point under `sec ≥ 0`:
     `exists_null_plane_of_nonnegative_sectional_intrinsic_line`
     (`Perelman/KappaSolutions/IntrinsicLineNullPlane.lean:70`).
   - the ancient analogue is `ancient_fixed_universal_cover_product_of_null_plane`
     (`Perelman/KappaSolutions/AncientSplitting.lean:162`, universal cover, all `t ≤ 0`).
   So brick 1 = line at `b` ⇒ null plane ⇒ terminal rank `≠ 3`; nonflat ⇒ rank `≠ 0`; ⇒ rank one ⇒ the
   committed window product. No new PDE.
2. **ℝ×N capture is already in the tree at the level of one neck sphere.**
   `SpatialNeck.interior_eq_empty_of_frontier_in_product_chart` (`Geometry/Neck/ProductCapExclusion.lean:58`):
   a compact `K` inside a chart `Φ : O ⊆ N × ℝ ≃ V` whose pulled-back metric is `C²`-`η`-close to
   `h ⊕ dz²` on `frontier K`, with `frontier K` the level sphere of an `ε`-neck (`ε ≤ 1/1000`,
   `720η < R/16`), has EMPTY interior (the neck sphere is a graph over `N`, so it bounds no compact
   region with interior). `N` only needs to be a connected 2-manifold (no compactness, no roundness).
   This is exactly H13's "cap frontier sphere ≅ `{pt} × N` bounds no compact region", in the metric form
   the approximants provide. The spacetime-witness version exists
   (`CanonicalWitness.exists_localNeck_of_product_chart`, `Perelman/CanonicalNeighborhood/ProductNeck.lean:26`,
   compact alternatives killed by a low-scalar point `C2·R(y) < R(x)`). What is missing is the
   SPATIAL-witness version (the currency of `StronglyCanonicalAt`), its pointed-limit transport and the
   strong-neck trigger. DEVIATION (recorded before proving): the purely topological lemma "an embedded
   sphere isotopic to `{pt} × N` bounds no compact region of `N × ℝ`" is NOT proved separately; the
   committed metric form above is what the approximant data give (a neck sphere is only known to be
   `C²`-close to a graph, not isotopic by construction) and it already contains the contradiction.
3. **Compact alternatives in the product.** For the positive/round alternatives the domain is the whole
   component; captured in `V ≅ O ⊆ N × ℝ` it would be a nonempty compact open subset of the connected
   noncompact `N × ℝ` — a purely topological exclusion, no low-scalar point needed (unlike
   `ProductNeck.lean`).
4. **Transport from the pointed limit.** `pointedMaps_eventually_fixedDomain_metric_close`
   (`Geometry/Compactness/CheegerGromov/Pointed/Convergence/DomainMetric.lean:160`),
   `pointed_metric_eventually_inverse_ball_capture` (`…/InverseCapture.lean:50`) and
   `exists_diffeomorph_onto_range_pullback_eq_immersionInducedMetric` turn canonical `MetricConvergenceData`
   of a pointed limit `L` with a product structure `e : N × ℝ ≃ L.M` into product charts of the approximants
   capturing a fixed-radius ball (template: `NeckProductFactor.lean:30`, which does it for one neck).

## Statements (recorded BEFORE proving; elaborated with `sorry` first)

**SC5-1a** (`Geometry/Flow/RicciFlow/DimensionThree/LineProductSplitting.lean`, ns `DifferentialGeometry.PDE.RicciFlow`):
```lean
theorem curvatureOperatorImageAt_finrank_eq_one_of_line [ConnectedSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 3) {a b : ℝ} (hab : a < b)
    (hcar : Icc a b ⊆ D.carrier) (hreg : Ioo a b ⊆ D.regular)
    (hR : ∀ t ∈ Icc a b, ∀ x, metricAlgebraicCurvatureTensorAt (S.family.metric t) x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (hcomplete : RiemannianMetricComplete (S.base.metric b))
    (hnonflat : ∃ x, metricRm04At (S.base.metric b) x ≠ 0)
    {gamma : ℝ → M} (hline : ∀ s t : ℝ, riemannianEDistOf (S.base.metric b) (gamma s) (gamma t) =
      ENNReal.ofReal |s - t|) (x : M) :
    Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric b) x
      (metricAlgebraicCurvatureTensorAt (S.family.metric b) x)) = 1
```
**SC5-1b** (same file): `[SimplyConnectedSpace M]`, SC5-1a's hypotheses + `hbound : ∃ K, 0 ≤ K ∧ ∀ t ∈ Icc a b,
∀ x, normSq0S (S.base.metric t) x 4 (S.base.rm04 t x) ≤ K` ⇒ the conclusion of
`exists_surface_product_on_closed_interval_of_terminal_rank_one` (`N` 2-manifold, connected, simply
connected; `Phi : N × ℝ ≃ M`; `pullbackMetricCross (S.base.metric t) Phi = (h t).prod dz²` for all
`t ∈ Icc a b`; `h t` complete; `R_{h t} > 0` on `Ioc a b`). Name `exists_surface_product_on_closed_interval_of_line`.
**SC5-1c** (same file, if the cover API cooperates): the universal-cover form for connected `M`
(`S.universalCover`), name `exists_universalCover_surface_product_on_closed_interval_of_line`.

**SC5-2a** (`Perelman/CanonicalNeighborhood/SpatialCanonicalWitnessProductChart.lean`, ns `…FiniteHorn`):
```lean
theorem SpatialCanonicalWitness.exists_localNeck_of_product_chart
    (W : SpatialCanonicalWitness g epsc C1 C2 y) (hchart : W.capTubeHasNeckChart eps)
    (heps : eps ≤ 1 / 1000) (h : SmoothRiemannianMetric J N) (hdim : Module.finrank ℝ F = 2)
    (O : Opens (N × ℝ)) (V : Opens M) (Φ : O ≃ₘ⟮J.prod 𝓘(ℝ), I3⟯ V)
    (hcapture : W.domain.carrier ⊆ V) {eta : ℝ} (heta : eta ≤ 1 / 4)
    (hsmall : 720 * eta < C2⁻¹ * metricScalarAt g y / 16)
    (hclose : ∀ z : V, z.val ∈ W.domain.carrier → ∀ m : ℕ, m ≤ 2 →
      metricDerivNorm m (Diffeomorph.pullbackMetricCross (g.restrictOpen V) Φ)
        ((h.prod (euclideanMetric (E := ℝ))).restrictOpen O)
        ((h.prod (euclideanMetric (E := ℝ))).restrictOpen O) (Φ.symm z) ≤ eta) :
    ∃ neck : SpatialLocalNeck g epsc y W.domain.carrier,
      W.alternative = SpatialCanonicalAlternative.neck neck
```
(`N` connected 2-manifold, no compactness/roundness.) Ball form `…_of_ball_product_chart`: capture and
closeness on `riemannianBallOf g y (2 * (C1 / √R(y)))` (the witness-independent region).

**SC5-2b** (`Perelman/CanonicalNeighborhood/PointedProductLimitNeck.lean`, ns `…FiniteHorn`): canonical
pointed convergence `Phi : PointedRiemannianConvergenceMaps X L subseq` to a complete `L` with a product
structure `e : N × ℝ ≃ L.M`, `pullbackMetricCross L.metric e = h.prod dz²` ⇒ for `q > 0`, `A`:
```lean
    ∀ᶠ k in atTop, ∀ x : (X.obj (subseq k)).M,
      riemannianEDistOf (X.obj (subseq k)).metric (X.obj (subseq k)).basepoint x ≤ ENNReal.ofReal A →
      q ≤ metricScalarAt (X.obj (subseq k)).metric x →
      ∀ {epsc eps : ℝ} (W : SpatialCanonicalWitness (X.obj (subseq k)).metric epsc C1 C2 x),
        W.capTubeHasNeckChart eps → eps ≤ 1 / 1000 →
        ∃ neck, W.alternative = SpatialCanonicalAlternative.neck neck
```
(uniform over all points of a bounded ball with a scalar floor and over all witnesses: "every class
witness at depth is a neck").

**SC5-2c** (`Surgery/Topology/HistoryStrongNeckProductChart.lean`, ns `…RetainedCoreHistory`): the SC1-d /
SC3-e triggers with the product-chart capture in place of the fine spatial neck:
`historyStrongNeck_of_product_chart` (`StronglyCanonicalAt` + ball product chart ⇒ `HistoryStrongNeck`),
`hasStrongNeckAt_of_product_chart` (class clause + terminal slab + `qcan < R` + ball product chart ⇒
`HasStrongNeckAt ε₁ v p`), `isTracedRegion_of_product_charts` (SC3-d with product-chart supply at the
trace points).

## Proof status (incremental)
- scratch chain `SC5.*` built (SP1/SC1/SC3 files as on disk, all exit 0). NOTE: the shared `.lake` build
  currently LACKS the committed `DimensionThree/TerminalProductSplitting.olean` and
  `Surgery/Topology/TracedRegionBackwardStep.olean` (committed at d81403768 / fb8709ed7, sources present);
  both were compiled here as scratch modules `SC5.TerminalProductSplitting`, `SC5.TracedRegionBackwardStep`
  (clean; the committed TerminalProductSplitting has pre-existing long-line warnings at :111 and others).
  An acceptance build must build them first.
- SC5-1a/1b/1c `DimensionThree/LineProductSplitting.lean` — PROVED, clean compile (zero output).
  1c proved as `exists_universalCover_surface_product_on_closed_interval_of_line` (instance args
  `[ConnectedSpace M] [LocallyPathConnectedSpace M] [SemilocallySimplyConnectedSpace M] [Inhabited M]`,
  as the committed `SolutionOn.universalCover` API requires them to state `UniversalCover M`).
  Private copy `rm04_eq_zero_of_image_finrank_eq_zero` of the private lemma in
  `DimensionThree/AncientCurvatureRank.lean:91` — deferred merge: make one public
  (e.g. `metricRm04At_eq_zero_of_curvatureOperatorImageAt_finrank_eq_zero` in
  `Geometry/Curvature/DimensionThree/CurvatureOperatorVanishing.lean`); a third copy lives in
  `KappaSolutions/NullPlaneSplittingReduction.lean:205`.
- SC5-2a `SpatialCanonicalWitnessProductChart.lean` — PROVED, clean. Private topological helper
  `false_of_isOpen_isCompact_subset_product_chart` (nonempty compact open set of `M` inside a chart onto an
  open subset of the connected noncompact `N × ℝ` is impossible).
- SC5-2b `PointedProductLimitNeck.lean` — PROVED as stated (`eventually_exists_localNeck_of_pointed_product_limit`),
  clean.
- SC5-2b addendum (recorded before proving, proved): `SpatialCanonicalWitness.exists_neck_of_scaleMetric`
  (neck alternative of `W.scaleMetric c` ⇒ neck alternative of `W`) and
  `eventually_exists_localNeck_of_scaled_pointed_product_limit` (2b for witnesses of the UNSCALED metrics
  `g k` when `(X.obj k).metric = scaleMetric (c k) (g k)` — the B13/SC4 shape `X n = Rₙ·g(tₙ)`; distance and
  scalar floor stay in rescaled units).
- SC5-2c `HistoryStrongNeckProductChart.lean` — `historyStrongNeck_of_product_chart`,
  `hasStrongNeckAt_of_product_chart` PROVED, clean. The third planned brick
  (`isTracedRegion_of_product_charts`) is NOT written: it would only restate SC3-d
  (`RetainedCoreHistory.isTracedRegion_of_hasStrongNeckAt`, whose supply hypothesis is exactly
  `HasStrongNeckAt` at the trace points) with `hasStrongNeckAt_of_product_chart` substituted pointwise; the
  consumer composes the two directly.
- `#print axioms` for all 11 public declarations: `[propext, Classical.choice, Quot.sound]` (no `sorryAx`);
  `#lint` (scratch copies): 0 errors in every file. `#print`/`#lint` lived only in scratch copies (deleted).
- New public names grep-unique; no `open private`; no committed file modified.

## Deliverables (all new, uncommitted, not in the root aggregate)
| File | Lines | Declarations | Uncommitted deps |
|---|---|---|---|
| `Geometry/Flow/RicciFlow/DimensionThree/LineProductSplitting.lean` | 185 | `curvatureOperatorImageAt_finrank_eq_one_of_line`, `exists_surface_product_on_closed_interval_of_line`, `exists_universalCover_surface_product_on_closed_interval_of_line` (+ private copy) | — |
| `Perelman/CanonicalNeighborhood/SpatialCanonicalWitnessProductChart.lean` | 140 | `SpatialCanonicalWitness.exists_localNeck_of_product_chart`, `…exists_localNeck_of_ball_product_chart` (+ private topological helper) | — |
| `Perelman/CanonicalNeighborhood/PointedProductLimitNeck.lean` | 209 | `eventually_exists_localNeck_of_pointed_product_limit`, `SpatialCanonicalWitness.exists_neck_of_scaleMetric`, `eventually_exists_localNeck_of_scaled_pointed_product_limit` | ProductChart |
| `Surgery/Topology/HistoryStrongNeckProductChart.lean` | 85 | `RetainedCoreHistory.historyStrongNeck_of_product_chart`, `RetainedCoreHistory.hasStrongNeckAt_of_product_chart` | ProductChart; SP1 `HistoryStrongNeck`; SC3 `HistoryStrongNeckClassSupply` chain |

Acceptance order: `LineProductSplitting` (after the committed-but-unbuilt `TerminalProductSplitting`),
`SpatialCanonicalWitnessProductChart`, `PointedProductLimitNeck` (committed deps only besides ProductChart);
`HistoryStrongNeckProductChart` after SP1/SC1/SC3's chain (and the committed-but-unbuilt
`TracedRegionBackwardStep`).

## Deviations (with reasons)
1. No standalone topological "sphere isotopic to `{pt} × N` bounds no compact region" lemma: the committed
   metric form `SpatialNeck.interior_eq_empty_of_frontier_in_product_chart` already is that statement for neck
   spheres `C²`-close to the product (the only spheres the witnesses produce); a bare isotopy hypothesis is
   not what the approximants supply.
2. Compact alternatives are excluded topologically (captured component ⇒ compact open subset of connected
   noncompact `N × ℝ`), not by a low-scalar point as in the committed spacetime `ProductNeck.lean`; so no
   scalar hypothesis beyond `720η < C2⁻¹R/16`.
3. Brick 1 needs `hnonflat` (terminal `Rm ≢ 0`; T4′'s limits have `R(base) = 1`) and states the product on
   `M` only for simply connected `M`; for general connected `M` the product is on the universal cover (1c).
   The line is used only through its null plane: the conclusion does not identify the `ℝ`-factor with the
   line (not needed by 2a–2c).

## What T4′ still lacks (consumer side, after SC1–SC5)
- **Finite-window limit at depth `T`** in the `PointedRiemannianConvergenceMaps` + canonical
  `MetricConvergenceData` currency at EACH slice `τ ∈ [−T, 0]` (2b consumes one slice), with: `Rm ≥ 0` on the
  window (Hamilton–Ivey limit), completeness at time 0, bounded curvature on `[−T, 0]`, `IsSolutionOn` on the
  window (brick 1's inputs). B13 (`TracedRegionAncientLimitScalarBound.lean:42`) only produces the limit after
  `htraced` holds at EVERY depth; the depth induction needs its finite-window analogue from `htraced` at depth
  `T` (candidate: `Compactness/Limits/LocalPointedFlowLimit.lean`, uncommitted — not audited here).
- **Line at time 0 of the window limit**: SC4's separation route (`exists_pointed_metric_line_of_eventual_separated_points_in_compact_balls`)
  applies to the time-0 slice verbatim; must be run on the window limit, not only on B13's ancient one.
- **Simple connectivity of the window limit** (to use 1b on `L` itself; 1c only splits `L̃`): e.g. orientation
  (`PointedLimitOrientation.lean`) + the time-0 Cheeger–Gromoll factor `N₀` being `S²` (compact, orientable,
  `K > 0`), or a deck-group descent of 1c's product (`Geometry/Metric/UniversalCover/DeckProduct*.lean`).
  Not in the tree for the window setting.
- **History → pointed sequence converter at depth**: the traced stage points `B.point` at slice `v` with the
  rescaled stage metric `R_n·g(v)` as a `PointedRiemannianSeq` whose base points are the traces, plus the
  identification of the class witness's metric with `g k` in `…_scaled_pointed_product_limit` (the
  `hX : (X.obj k).metric = scaleMetric (c k) (g k)` equation), and the scalar floor `qcan < R` ⇔
  `q ≤ R_X` in rescaled units. With it, `hasStrongNeckAt_of_product_chart` (or 2b + SC1-d's trigger) feeds
  SC3-d's supply at every trace point of the ball.
- As before (SC3/SC4): uniform top-ball bounds at depth 0, the sequence-level depth induction, the
  `extendHorizon` transfer lemma, T3A-3 and the T4′ constants.
- Deferred merges: `rm04_eq_zero_of_image_finrank_eq_zero` (three private copies now).
