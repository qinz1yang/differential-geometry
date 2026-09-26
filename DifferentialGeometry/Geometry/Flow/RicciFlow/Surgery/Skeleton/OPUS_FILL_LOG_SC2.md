# OPUS fill log SC2: T4′ consumer wave 2 (2026-09-26)

Worker lane SC2. Scope: (1) depth-0 uniformity of SC1-b/SC1-d over compact sets of horn points;
(2) T3A-3 (line ⇒ cylinder ⇒ neck, and the neck datum `P.FineCutNecks εc Qc` needs on `L`).
New files only; read-only compiles (`LEAN_NUM_THREADS=2 lake env lean -DmaxSynthPendingDepth=3
-Dweak.linter.mathlibStandardSet=true`); scratch modules `SC2.*` under the session scratchpad `sc2/`.
No git writes, no lake build, no root-aggregate edit.

## Progress
- read AGENTS.md, OPUS_FILL_LOG_SC1.md, DESIGN_S_SUPPLY.md §0–§3.
- supplier survey:
  - fixed-centre cap barrier chain, all in `Surgery/Topology/TerminalSpatialCanonicalAlternatives.lean`:
    `eventually_spatial_cap_neck_compact_capture` (:672), `eventually_normalizedNeck_of_spatial_caps`
    (:768), `eventually_scalar_bounds_on_spatial_domains` (:854),
    `exists_cap_midpoint_region_of_normalizedNeck_of_spatialCap` (:912, already centre-generic),
    `eventually_spatial_cap_midpoint_region` (:1022), `eventually_spatial_cap_spherical_barrier` (:1149).
    The centre `x` enters only through (i) `G(τ)`-scalar at `x` → `R_L(x)` and (ii) `x ∈ interior K`;
    the neck centres `v n` are already moving (`eventually_normalizedNeck_of_moving_spatialNecks`, :366).
  - `L`-side neck transfer needing only SPATIAL necks of `G(τₙ)` at a fixed `x` along one sequence:
    `TerminalLimitMetric.eventually_normalizedNeck_of_spatialNecks` (:473) — no derivative/pinching
    hypotheses (it builds them from `G.exists_all_point_canonical_neighborhoods`).
  - strong-neck variant with scalar control: `TerminalNeckNormalization.lean:434`, and its
    FineCutNecks-shaped corollary `exists_normalizedNeck_of_eventually_strongNeck`
    (`Contract/HornFineCutNecksLongSlab.lean:83`, needs `∀ᶠ τ` and `G.flow` strong necks).
  - splitting/cylinder: `exists_trivial_shrinkingCylinderCover_of_rays_comparisonAngle_lower`
    (`Perelman/KappaSolutions/SeparatedRayCylinderBranch.lean:29`: ancient κ-solution, two rays from the
    base point with comparison angle ≥ θ > 0 ⇒ trivial shrinking-cylinder cover),
    `exists_strongNeck_of_shrinkingCylinderCover_trivialModel` (`ShrinkingCylinderNecks.lean:88`),
    limit → approximant: `StrongNeck.eventually_transport_of_comparisons` (`NeckLimitTransport.lean:23`),
    `comparisonAngle_add` (`Geometry/Comparison/Toponogov/ComparisonAngle.lean:85`, angle π).
  - `StrongNeck.toSpatialNeck` (`SpatialNeckLocalTransport.lean:30`), `SpatialNeck.pushforward`
    (`SpatialCanonicalWitnessTransport.lean:481`), `openSubtypePartialDiffeomorph`
    (`Topology/Manifold/OpenSubtypeDiffeomorph.lean:17`).

## Choice for (1)
The "L-necks ⇒ G(τ)-necks uniformly on compacts" route is circular for T4′: the ball around a
non-`εc`-neck point `xₙ` need not consist of fine necks of `L`, and SC1-c's tolerance `eta(C1,C2)` comes
after `eta` in T4′. The moving-centre cap barrier is supported verbatim by the tree's suppliers (only
scalar convergence at the centre changes), so (1) is the moving-centre route.

## Brick statements (recorded BEFORE proving)

**SC2-a = moving-centre cap barrier** (`Surgery/Topology/TerminalSpatialCapMovingBarrier.lean`, namespace
`…Surgery.Topology.OrientedThreeStage.IncomingSlab`): the fixed-centre chain of
`TerminalSpatialCanonicalAlternatives.lean` (:672, :747, :768, :854, :1022, :1149) with centres
`x : ℕ → G.terminalRegularOpen` in a compact `B` (positive `R_L` on `B`), headline
```lean
theorem TerminalLimitMetric.eventually_moving_spatial_cap_spherical_barrier
    (L : G.TerminalLimitMetric) {τ : ℕ → ℝ} (hτ : Tendsto τ atTop (𝓝[<] s))
    {B : Set G.terminalRegularOpen} (hB : IsCompact B)
    (hBpos : ∀ y ∈ B, 0 < metricScalarAt L.metric y)
    (x : ℕ → G.terminalRegularOpen) (hxB : ∀ n, x n ∈ B)
    {epsCanonical eps δ C1 C2 : ℝ} (hδ : 0 < δ) (hδsmall : δ < 1 / 20000)
    (hepsδ : eps < δ) (hfit : δ⁻¹ + 1 ≤ eps⁻¹)
    (W : ∀ n, SpatialCanonicalWitness (G.flow.base.metric (τ n)) epsCanonical C1 C2 (x n).val)
    (hW : ∀ n, (W n).capTubeHasNeckChart eps) (cap …) (depth …) (hcap …) :
    ∀ᶠ n in atTop, ∃ (v) (nk : SpatialNeck L.metric δ v) (K : CompactDomain G.terminalRegularOpen),
      … x n ∈ interior K.carrier … -- body of :1149 with x ↦ x n
```
(intermediates: `eventually_moving_scalar_range_on_spatial_domains` (uniform over `B`, in `t`),
`eventually_moving_spatial_cap_neck_compact_capture`, `eventually_normalizedNeck_of_moving_spatial_caps`,
`eventually_moving_scalar_bounds_on_spatial_domains`, `eventually_moving_spatial_cap_midpoint_region`).
The fixed-centre versions are the constant-sequence case (`B = {x}`); deferred merge (not done: no edits
in the import chain).
- PROVED (443 lines), clean compile (zero output).

**SC2-b = uniform SC1-b** (`Surgery/Topology/TerminalHornCanonicalNeckUniform.lean`, namespace
`…Surgery.Topology.TerminalCorePresentation`):
```lean
theorem eventually_forall_neck_alternative_of_subset_hornHalfRange :
    ∃ eta : ℝ, 0 < eta ∧
    ∀ {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ), ε ≤ eta →
    ∀ (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c)
      {B : Set D.slab.terminalRegularOpen}, IsCompact B → B ⊆ P.hornHalfRange c e →
    ∀ {epsCan eps C1 C2 : ℝ}, 0 < eps → eps ≤ eta →
      (∀ x ∈ B, 4 * C2 * (Λ * (P.coreRadius ^ 2)⁻¹) < metricScalarAt D.terminal.metric x) →
      ∀ᶠ t in 𝓝[<] D.endTime, ∀ x ∈ B,
        ∀ W : SpatialCanonicalWitness (D.slab.flow.base.metric t) epsCan C1 C2 x.val,
          W.capTubeHasNeckChart eps →
            ∃ neck : SpatialLocalNeck (D.slab.flow.base.metric t) epsCan x.val W.domain.carrier,
              W.alternative = SpatialCanonicalAlternative.neck neck
```
- The single `t`-filter is uniform over the compact `B` (one `τ` for all points), which is what the
  blow-up at depth 0 needs: the consumer takes `B` = a closed `L`-ball around `xₙ` inside the horn
  (compact, since `L` is locally compact and the ball is small relative to the horn).
- Route: contradiction ⇒ `τ n → s⁻`, `x n ∈ B` with a non-neck witness; one base point
  `b = horn(y₀,0)` (`R_L(b) ≤ ℓ`) and uniform scalar closeness on `B ∪ {b}` with tolerance `ℓ/2`
  give `C2·R_G(b) < R_G(x n)` for all large `n` ⇒ cap alternative (`alternative_eq_neck_or_cap_of_mul_scalar_lt`);
  SC2-a with centres `x n`; then SC1-b's horn-topology contradiction at one `n` (T1 on
  `P.monoEpsilon`, interior connected by SC1-a).
- SC2-b PROVED: `Surgery/Topology/TerminalHornCanonicalNeckUniform.lean`, clean compile (scratch modules
  `SC2.TerminalSpatialCapMovingBarrier`, `SC2.InteriorCollar`), axioms of SC2-a/SC2-b headlines
  `[propext, Classical.choice, Quot.sound]`. SC1-b is the case `B = {x}` (deferred merge, not done).

**SC2-c = uniform depth-0 strong-neck trigger** (`Surgery/Topology/HistoryStrongNeckUniform.lean`,
depends on SP1's uncommitted `HistoryStrongNeck`/`TruncatedNeck`, θ₀ = 1/5 version of 12:27):
```lean
theorem RetainedCoreHistory.eventually_forall_historyStrongNeck_of_subset_hornHalfRange :
    ∃ eta : ℝ, 0 < eta ∧
    ∀ {P₀} (H : RetainedCoreHistory P₀) (k) {s} (G) (L : G.TerminalLimitMetric) (hsing) (parameters)
      {εP Λ : ℝ} (P : TerminalCorePresentation {…as SC1-d…} εP Λ), εP ≤ eta →
    ∀ (c) (e : P.hornIndex c) {B : Set G.terminalRegularOpen}, IsCompact B → B ⊆ P.hornHalfRange c e →
    ∀ {ε ε₁ C1 C2 qcan : ℝ}, 0 < ε → ε ≤ eta →
      (∀ x ∈ B, 4 * C2 * (Λ * (P.coreRadius ^ 2)⁻¹) < metricScalarAt L.metric x) →
      (∀ x ∈ B, qcan < metricScalarAt L.metric x) →
      H.StronglyCanonicalBefore k G ε ε₁ C1 C2 qcan s →
      ∀ᶠ t in 𝓝[<] s, ∀ x ∈ B, H.toHistory.HistoryStrongNeck k G ε₁ x.val t
```
plus the T3A-3 history bridge (same file):
```lean
def TruncatedNeck.toSpatialNeck (nk : TruncatedNeck S eps depth x t) : SpatialNeck (S.base.metric t) eps x
theorem ObservedHistory.nonempty_spatialNeck_of_historyStrongNeck … (h : H.HistoryStrongNeck k G eps y t)
    (ht : H.time k ≤ t) : Nonempty (SpatialNeck (G.flow.base.metric t) eps y)
theorem RetainedCoreHistory.exists_normalizedNeck_of_frequently_historyStrongNeck … (L) (x) (hx : 0 < R_L x)
    {εc eps} (hεc : 0 < εc) (hεc1 : εc < 1) (hfit : εc⁻¹ + 1 ≤ eps⁻¹)
    (h : ∃ᶠ t in 𝓝[<] s, H.toHistory.HistoryStrongNeck k G eps x.val t) :
    ∃ N : NormalizedNeck L.metric εc (⌊εc⁻¹⌋₊ + 1), N.center = x
```

**SC2-d = neck on an open subset is a neck of the ambient metric**
(`Perelman/CanonicalNeighborhood/SpatialNeckOpenSubset.lean`, namespace `…FiniteHorn`):
```lean
def SpatialNeck.ofRestrictOpen {U : TopologicalSpace.Opens M} {z : U}
    (nk : SpatialNeck (g.restrictOpen U) eps z) : SpatialNeck g eps z.val
```

**SC2-e = T3A-3, terminal side: the exact FineCutNecks datum** (`Surgery/Topology/TerminalFineNeckOfSpatialNecks.lean`):
```lean
theorem TerminalLimitMetric.exists_normalizedNeck_of_frequently_spatialNeck (L : G.TerminalLimitMetric)
    (x : G.terminalRegularOpen) (hx : 0 < metricScalarAt L.metric x) {εc eps : ℝ} (hεc : 0 < εc)
    (hεc1 : εc < 1) (hfit : εc⁻¹ + 1 ≤ eps⁻¹)
    (h : ∃ᶠ t in 𝓝[<] s, Nonempty (SpatialNeck (G.flow.base.metric t) eps x.val)) :
    ∃ N : NormalizedNeck L.metric εc (⌊εc⁻¹⌋₊ + 1), N.center = x
theorem TerminalCorePresentation.fineCutNecks_of_frequently_spatialNeck (P : TerminalCorePresentation D ε Λ)
    {εc eps Qc : ℝ} (hεc : 0 < εc) (hεc1 : εc < 1) (hfit : εc⁻¹ + 1 ≤ eps⁻¹)
    (h : ∀ c (e : P.hornIndex c) x, x ∈ interior (range fun p : HalfNeckCylinder => P.horn c e p.1) →
      Qc ≤ metricScalarAt D.terminal.metric x →
      ∃ᶠ t in 𝓝[<] D.endTime, Nonempty (SpatialNeck (D.slab.flow.base.metric t) eps x.val)) :
    P.FineCutNecks εc Qc
```
Only spatial necks of `G(t)` along one sequence `t → s⁻` are needed (`:473` builds the derivative and
pinching control itself) — weaker input than `exists_normalizedNeck_of_eventually_strongNeck`.

**SC2-f = T3A-3, limit side: line ⇒ cylinder ⇒ necks** (`Perelman/KappaSolutions/LineCylinderNeck.lean`):
```lean
theorem exists_trivial_shrinkingCylinderCover_of_line (P : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
    {kappa : ℝ} (hP : IsAncientKappaSolution kappa P) (hbase : PointedFlowScalarAtBase P 1)
    (o : TangentOrientationSection P.M) (γ : ℝ → P.M)
    (hγ : ∀ a b, metricDistance (P.S.base.metric 0) (γ a) (γ b) = |a - b|) (hγ0 : γ 0 = P.basepoint) :
    ∃ C : ShrinkingCylinderCover P, C.TrivialModel
theorem exists_strongNeck_of_line … : ∀ eps : ℝ, 0 < eps → eps < 1 / 11 →
    Nonempty (StrongNeck P.S eps P.basepoint 0)
theorem eventually_strongNeck_of_line_of_comparisons … (approximants `S i` on `M i`, maps `F i`,
    comparisons on every compact set and every window `[-A, 0]`) :
    ∀ alpha, 0 < alpha → 2 * alpha < 1 / 11 → ∀ᶠ i in atTop, Nonempty (StrongNeck (S i) (2 * alpha) (F i P.basepoint) 0)
```
- SC2-c/d/e/f PROVED as stated (SC2-f's approximant corollary is the windowed-model form
  `FiniteHorn.eventually_strongNeck_of_windowed_models_of_line`, file
  `Perelman/CanonicalNeighborhood/WindowedLineNeckTransport.lean`, built on
  `StrongNeck.eventually_transport_of_windowed_models` (`WindowedNeckLimit.lean:28`)).
- SC2-c's history bridge uses only `nk.depth_pos` of the `TruncatedNeck` (no θ₀ literal), so it is
  θ₀-agnostic; it was compiled against SP1's 12:27 files (θ₀ = 1/5, `TruncatedNeck` form).

## Deliverables (all new, uncommitted, not in the root aggregate)
| File | Lines | Headlines | Uncommitted deps |
|---|---|---|---|
| `Surgery/Topology/TerminalSpatialCapMovingBarrier.lean` | 443 | `IncomingSlab.TerminalLimitMetric.eventually_moving_spatial_cap_spherical_barrier` (+5 moving intermediates) | — |
| `Surgery/Topology/TerminalHornCanonicalNeckUniform.lean` | 279 | `TerminalCorePresentation.eventually_forall_neck_alternative_of_subset_hornHalfRange` | MovingBarrier, SC1's `InteriorCollar` |
| `Perelman/CanonicalNeighborhood/SpatialNeckOpenSubset.lean` | 37 | `FiniteHorn.SpatialNeck.ofRestrictOpen` (+`_map`, `_center`) | — |
| `Surgery/Topology/TerminalFineNeckOfSpatialNecks.lean` | 70 | `IncomingSlab.TerminalLimitMetric.exists_normalizedNeck_of_frequently_spatialNeck`, `TerminalCorePresentation.fineCutNecks_of_frequently_spatialNeck` | — |
| `Perelman/KappaSolutions/LineCylinderNeck.lean` | 53 | `KappaSolutions.exists_trivial_shrinkingCylinderCover_of_line`, `KappaSolutions.exists_strongNeck_of_line` | — |
| `Perelman/CanonicalNeighborhood/WindowedLineNeckTransport.lean` | 64 | `FiniteHorn.eventually_strongNeck_of_windowed_models_of_line` | LineCylinderNeck |
| `Surgery/Topology/HistoryStrongNeckUniform.lean` | 156 | `FiniteHorn.TruncatedNeck.toSpatialNeck`, `ObservedHistory.nonempty_spatialNeck_of_historyStrongNeck`, `ObservedHistory.exists_normalizedNeck_of_frequently_historyStrongNeck`, `RetainedCoreHistory.eventually_forall_historyStrongNeck_of_subset_hornHalfRange` | SP1 (`StrongNeckRestriction` → `TruncatedNeck` → `HistoryStrongNeck`), HornCanonicalNeckUniform, FineNeckOfSpatialNecks, SpatialNeckOpenSubset |

- Compile: every file with `LEAN_NUM_THREADS=2 lake env lean -DmaxSynthPendingDepth=3
  -Dweak.linter.mathlibStandardSet=true`, uncommitted imports through scratch modules `SC2.*`
  (`--root` = `scratchpad/sc2`): zero output. `#lint in SC2`: docBlame only (inapplicable).
- `#print axioms` for all 13 headlines: `[propext, Classical.choice, Quot.sound]` (scratch files only).
- New names grep-unique library-wide. No `open private`, no copies of private lemmas.
- Acceptance order: MovingBarrier, SpatialNeckOpenSubset, FineNeckOfSpatialNecks, LineCylinderNeck
  (committed deps only); then SC1's InteriorCollar → HornCanonicalNeckUniform; WindowedLineNeckTransport;
  then SP1's three files → HistoryStrongNeckUniform.
- Deferred merges (not done, import chain untouched): the fixed-centre chain of
  `TerminalSpatialCanonicalAlternatives.lean` (:672–:1149) is the constant-sequence case of SC2-a;
  SC1-b is the case `B = {x}` of SC2-b (the SC2-b proof tail repeats SC1-b's horn-topology argument);
  `TruncatedNeck.toSpatialNeck` belongs in `TruncatedNeck.lean`.
- Deviation: SC2-a was recorded in this log after its first clean compile (mechanical generalization);
  SC2-b…f were recorded before proving.

## What T4′ still lacks after this wave
1. T3A-2 (not this lane; waits on the θ₀ revision): the repeated backward extension. Its depth-0 input
   is now SC2-c: for any compact `B ⊆ hornHalfRange c e` with `R_L > max(4·C2·ℓ, qcan)` on `B`, ONE
   `t`-filter on which every point of `B` carries a `HistoryStrongNeck`. The consumer still has to put the
   rescaled `G(τ)`-ball `B(xₙ, A/√R)` inside such a `B` (closed `L`-ball in the horn; compact since `L`
   is locally complete there — needs the `L`-ball/`G(τ)`-ball comparison as `τ → s⁻`, cf.
   `TerminalVaryingChartConvergence`).
2. The line in the limit: two horn arms of normalized length → ∞ with comparison angle ≥ θ > 0
   (DESIGN_S_SUPPLY F7) must be produced inside the T3A-2 limit, then SC2-f applies (either through
   rays + angle directly, `exists_trivial_shrinkingCylinderCover_of_rays_comparisonAngle_lower`, or an
   isometric line through the base point, `exists_trivial_shrinkingCylinderCover_of_line`). The limit must
   be packaged as `PointedFlowData` with `IsAncientKappaSolution`, `PointedFlowScalarAtBase 1` and an
   orientation (`WindowedOrientation`'s `orientable_limit_of_orientable_sources` exists for windowed models).
3. Format gap: SC2-f's approximant transport exists for windowed-model limits
   (`WindowedModelWitness`) and for `MetricComparisonOn` families (`NeckLimitTransport.lean:23`). The
   T3A-2 limit supplier `TerminalScalarAncientLimit.lean:475` outputs `metricDerivNormSupOn` closeness on
   `U n`; a converter to `MetricComparisonOn` (or a StrongNeck transport in that format) is missing.
4. Closing the contradiction: SC2-e contrapositive — if `xₙ` is not an `εc`-neck of `Lₙ`, then
   `∀ᶠ τ in 𝓝[<] sₙ, IsEmpty (SpatialNeck (Gₙ(τ)) eps xₙ)` with `εc⁻¹ + 1 ≤ eps⁻¹` (one line from
   `exists_normalizedNeck_of_frequently_spatialNeck` + `not_frequently`); so `τₙ` may be chosen as close
   to `sₙ` as the blow-up needs with no spatial `eps`-neck at `xₙ`, and the approximant neck at `(xₙ, τₙ)`
   (after undoing the parabolic rescaling — `WindowedModelWitness.embedding`/`base_map` already does this
   in the windowed format) contradicts it. `ObservedHistory.exists_normalizedNeck_of_frequently_historyStrongNeck`
   covers the survivor-flow form.
5. T4′ constants: `eta := min` of SC2-b/SC2-c's `eta` and T1's; `eps ≤ εc/(1+εc)` for SC2-e;
   `εcone ≤ 1/1000`.
