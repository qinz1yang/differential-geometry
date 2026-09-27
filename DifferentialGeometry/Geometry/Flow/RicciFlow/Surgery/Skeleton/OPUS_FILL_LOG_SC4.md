# OPUS fill log SC4: T4′ consumer wave 4 = SC2's gaps 2, 3, 5 (2026-09-26)

Worker lane SC4. Scope: (1) the line in the T3A-2 blow-up limit; (2) packaging of that limit as an
ancient κ-solution + the transport back to the approximants (format gap); (3) the T4′ constants lemma.
New files only; read-only compiles (`LEAN_NUM_THREADS=2 lake env lean -DmaxSynthPendingDepth=3
-Dweak.linter.mathlibStandardSet=true`); uncommitted imports through scratch modules `SC4.*` under the
session scratchpad `sc4/`. No git writes, no lake build, no root-aggregate edit.

## Progress
- read AGENTS.md, SC1/SC2/SC3/XA3 logs, DESIGN_S_SUPPLY §0–§3, H12/H13/H17 digests,
  `TerminalScalarAncientLimit.lean:475`, B13 (`TracedRegionAncientLimitScalarBound.lean:42`),
  X5 (`CrossingAncientLimit.lean`), B8 (`AncientLimitCanonicalWitness.lean`), the horn-arms files.

## Findings before the statements (failures first)

1. **T3A-2's limit is B13's, not `:475`'s.** SC3 (finding 1) produces the window supply in the
   `isTracedRegion` currency, i.e. exactly `htraced` of
   `exists_bounded_ancient_pointed_flow_limit_of_spatially_canonical_before` (B13). The "T3A-2 limit"
   is therefore B13's output: `F : PointedRiemannianConvergenceMaps X P f` from the rescaled stage
   metrics `X n = (stage(tₙ), yₙ, Rₙ·g(tₙ))`, canonical `MetricConvergenceData`, and `G` on `P`.
   DEVIATION (recorded before proving): the converter of piece 2 is written for B13's format. A
   `:475 → MetricComparisonOn` converter is not written: `:475` no longer feeds T3A-2, and the
   transport back used below (`pointedAncientKappaLimit_eventually_spatialNeckWitness_of_intrinsic_line`,
   `Perelman/KappaSolutions/PointedLineNeck.lean:83`) consumes B13's `MetricConvergenceData` directly;
   the windowed-model route (`eventually_strongNeck_of_windowed_models_of_line`) is not needed either
   (and would need survivor-flow approximants, since `closedPrefixAt` has no window at young points).
2. **The line needs neither arms nor "through the base point".** The tree already has the
   Cheeger–Gromov line lemma
   `CheegerGromovCompactness.exists_pointed_metric_line_of_eventual_separated_points_in_compact_balls`
   (`Geometry/Compactness/CheegerGromov/Pointed/Convergence/SeparatingSegments.lean:302`): a two-sided
   separating set `S k` at bounded distance from the approximant base points, and for every `A`
   eventually points on both sides at distance exactly `A` (with compact `3A+1` balls and the `3A` ball in
   the open set carrying the separation) give a line in the limit. And
   `pointedAncientKappaLimit_eventually_spatialNeckWitness_of_intrinsic_line` turns ANY line of the
   limit κ-solution into `ε`-necks at the APPROXIMANT base points for every `ε`. So SC2's gap 2 is closed
   by a separation hypothesis on the approximants, not by arms with comparison angles (comparison-angle
   monotonicity is unavailable on the approximants; the windowed arm machinery needs windowed models).
3. **F7 / H12's presentation-dependent `Q` is already gone in the tree.** `exists_minimizingArms_of_horn_point`
   and `exists_deep_horn_centralSphere_sides` (`HornCentralSphereSeparation.lean:384,488`) take `Q` from
   `exists_scale_threshold_neck_coordinates_beyond_depth` (`Q = 2·(max_core R + 1)`, unbounded in `Λ/r²`),
   but the committed `HornSeparationFrontierScalar.lean` (9126abc30) has the `Q`-free versions:
   `exists_neck_coordinates_in_horn_of_frontier_scalar_lt` (:116, needs only the core FRONTIER scalar,
   `≤ Λ/r²` by `frontier_scalar_le`), `exists_horn_centralSphere_side_points_of_frontier_scalar_lt` (:164,
   sides + side points at distance `r` in `L`) and the slice transfer
   `exists_strongNeck_threshold_of_horn_point_at_slice_of_frontier_scalar_lt` (:232, via
   `HornSeparationSliceTransfer.lean`: `L`-balls ↔ `G(τ)`-balls and `G(τ)`-necks at `x` as `τ → s⁻`). So the
   horn geometry feeds a uniform `Kfine` (the hypothesis is `2·R(w) < N.scale` on the core frontier, implied
   by `2·Λ/r² < R(x)`). No new `Q`-free arms lemma is needed.

## Statements (recorded BEFORE proving; elaborated with `sorry` first — only `declaration uses sorry`)

**SC4-a = packaging of the T3A-2 limit** (`Surgery/Topology/TracedRegionAncientKappaLimit.lean`, ns
`…Surgery.Topology.ObservedHistory`): B13's hypotheses verbatim plus `hscal` (scalar `R n` at `(tₙ, yₙ)`) give
```lean
theorem exists_ancientKappa_pointed_limit_of_isTracedRegion :
    ∃ epsW : ℝ, 0 < epsW ∧ ∀ H t y R hR, (hscal) → Tendsto R atTop atTop → (htraced) → … (B13's list) →
    let X := (rescaled stage metrics, as B13)
    ∃ f, StrictMono f ∧ ∃ (P) (F : PointedRiemannianConvergenceMaps X P f),
      (∃ C : MetricConvergenceData F, ∀ n, C.domain n = canonicalSourceData F n) ∧
      MetricComplete P ∧ ConnectedSpace P.M ∧ Nonempty (TangentOrientationSection P.M) ∧
      ∃ G (hG : IsSolutionOn {G} on ancientTimeInterval), G 0 = P.metric ∧
        IsAncientKappaSolution (κ / 250 / 30 ^ 3) (flowOfMetric ancientTimeInterval P G hG) ∧
        PointedFlowScalarAtBase (flowOfMetric ancientTimeInterval P G hG) 1
```
(X5's inline steps as one reusable lemma: pinching of the survivor windows, curvature cone + completeness,
base scalar via X5d, orientation via X5c, κ-solution via `AncientPointedFlowLimitCurvature:185`.)

**SC4-b = the line in the T3A-2 limit ⇒ necks at the approximant base points**
(`Surgery/Topology/TracedRegionLineNeck.lean`, same ns): B13's hypotheses + `hscal` + a two-sided separation
of the approximants:
```lean
theorem exists_eventually_spatialNeck_of_isTracedRegion_of_twoSidedSeparation :
    ∃ epsW : ℝ, 0 < epsW ∧ ∀ H t y R, (∀ n, 0 < R n) → (hscal) → … (B13's list) →
    ∀ (U : ∀ n, Opens ((H n).stageAt (t n)).Carrier) (S : ∀ n, Set (U n))
      (sep : ∀ n, TwoSidedSeparation (S n)) {B : ℝ}, 0 ≤ B →
    (∀ n (z : U n), z ∈ S n → d_{g(tₙ)}(yₙ, z) ≤ B / √(R n)) →
    (∀ A, B < A → ∀ᶠ n, closedBall_{g(tₙ)}(yₙ, 3A/√(R n)) ⊆ U n ∧
      ∃ p q : U n, p ∈ (sep n).negativeSide ∧ q ∈ (sep n).positiveSide ∧
        d_{g(tₙ)}(yₙ, p) = A/√(R n) ∧ d_{g(tₙ)}(yₙ, q) = A/√(R n)) →
    ∃ ψ, StrictMono ψ ∧ ∀ ε, 0 < ε → ε < 1/11 → ∀ᶠ i in atTop,
      Nonempty (SpatialNeck (g_{H (ψ i)}(t (ψ i))) ε (y (ψ i)))
```
(distances are `riemannianEDistOf … = ENNReal.ofReal (A / Real.sqrt (R n))`, `g(tₙ)` the stage metric of the
active stage.) Route: SC4-a; `exists_pointed_metric_line_of_eventual_separated_points_in_compact_balls` on the
rescaled approximants (`edistOf_scale`) gives a line in `P`; `pointedAncientKappaLimit_eventually_spatialNeckWitness_of_intrinsic_line`
(after transporting `F` along `flowOfMetric_atTime`) gives `SpatialNeckWitness`es at the rescaled base points;
`SpatialNeckWitness.exists_spatialNeck` + `SpatialNeck.scaleMetric` by `R⁻¹` undo the rescaling.
This is exactly the input of SC2-e's contrapositive (SC2 gap 4).

- SC4-a PROVED (`TracedRegionAncientKappaLimit.lean`), clean compile, first try after the `open` fix.
- SC4-b first elaborated and PROVED with a `TwoSidedSeparation` hypothesis and exact-distance points
  (clean). REVISION before acceptance (weaker, more natural hypothesis; DEVIATION: this revision and SC4-a′ were logged right after their first clean compile, not before):
  the separation data are now three plain sets `S V W : ∀ n, Set carrier`, `V n`, `W n` open and disjoint,
  `S n` within `B/√(R n)` of `yₙ`, and for every `A > B` eventually
  `closedBall(yₙ, 3A/√(R n)) \ S n ⊆ V n ∪ W n` with points `p ∈ V n`, `q ∈ W n` at distance in
  `[A/√(R n), 3A/√(R n))` from `yₙ`. (A `TwoSidedSeparation` needs `frontier = S` on both sides, which the horn
  sides of `HornSeparationFrontierScalar` do not provide; exact distances are not what the horn gives.)
  The line now comes from `exists_pointed_metric_line_of_eventual_minimizing_segments_intersecting_bounded_sets`
  (`SeparatingSegments.lean:376`) with segments from `exists_distance_parametrized_minimizer_in_closedBall`;
  the exact-distance points come from the new generic lemma SC4-a′ below. Name:
  `exists_eventually_spatialNeck_of_isTracedRegion_of_separating_set`. RE-PROVED, clean compile.

**SC4-a′ = exact-distance point on a side** (`Geometry/Metric/Distance/SeparatedSidePoint.lean`, ns
`DifferentialGeometry.Geometry.Metric`):
```lean
theorem exists_mem_riemannianEDistOf_eq_of_ball_diff_subset (g : SmoothRiemannianMetric I M)
    {S V W : Set M} (hV : IsOpen V) (hW : IsOpen W) (hVW : Disjoint V W) {x : M} {a b c : ℝ}
    (hb : 0 ≤ b) (hba : b < a) (hS : ∀ z ∈ S, riemannianEDistOf g x z ≤ ENNReal.ofReal b)
    (hcover : riemannianBallOf g x c \ S ⊆ V ∪ W) {q : M} (hq : q ∈ V)
    (ha : ENNReal.ofReal a ≤ riemannianEDistOf g x q)
    (hc : riemannianEDistOf g x q < ENNReal.ofReal c) :
    ∃ q' ∈ V, riemannianEDistOf g x q' = ENNReal.ofReal a
```
(last crossing of the level `a` along an almost-minimizing path from `x` to `q`; the tail beyond it stays
in the ball, misses `S`, is preconnected, hence lies in `V`). PROVED, clean (logged after proving, see the deviation above).
- Axioms (`#print axioms`, scratch file only, removed): SC4-a, SC4-b, SC4-a′ all
  `[propext, Classical.choice, Quot.sound]`.

**SC4-c = the horn produces SC4-b's separation data on the slices** (`Surgery/Topology/HornSliceSeparatedSides.lean`,
ns `…Surgery.Topology.TerminalCorePresentation`), recorded BEFORE proving (elaborated with `sorry`):
```lean
theorem exists_eventually_separated_sides_of_frontier_scalar_lt :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ), ε ≤ eta →
        ∀ c, c ∈ P.component → ∀ (e : P.hornIndex c) {δ k} (N : NormalizedNeck D.terminal.metric δ k),
          δ ≤ ε → ⌊ε⁻¹⌋₊ + 1 ≤ k → N.center ∈ hornHalfRange P c e →
          (∀ w ∈ frontier (P.core c), 2 * R_L(w) < N.scale) →
          ∃ S V W : Set D.stage.Carrier, IsOpen V ∧ IsOpen W ∧ Disjoint V W ∧
            (∀ᶠ τ in 𝓝[<] D.endTime, ∀ z ∈ S, d_τ(x, z) ≤ 7 / √R_τ(x)) ∧
            ∀ {A}, 0 < A → IsCompact (closedBall_L(x, 4A/√R_L(x))) →
              (∀ w ∈ frontier (P.core c), 2A/√R_L(x) < d_L(x, w)) →
              ∀ᶠ τ in 𝓝[<] D.endTime,
                closedBall_τ(x, 3A/√R_τ(x)) \ S ⊆ V ∪ W ∧
                ∃ p ∈ V, ∃ q ∈ W, A/√R_τ ≤ d_τ(x, p) < 3A/√R_τ ∧ A/√R_τ ≤ d_τ(x, q) < 3A/√R_τ
```
(`x = N.center`, `d_τ` the distance of `G(τ) = D.slab.flow.base.metric τ`, `R_τ = D.slab.flow.scalar τ`.) `S` is
the central sphere of the `L`-neck `N` (the same set in the stage manifold for every `τ`), `V`/`W` the images of
the core side and the end side of the horn's complement pair (`HornSeparationFrontierScalar:164`'s
construction, split at the radius quantifier so that the sides do not depend on `A`). With `B = 7 < A` this is
exactly SC4-b's separation hypothesis at `(D, x, τ)`; the `L`-inputs per `A` (compact `L`-ball of radius
`4A/√R_L(x)`, core frontier farther than `2A/√R_L(x)`) are the T4′ bounded-curvature-at-distance inputs.
- SC4-c PROVED, clean compile (first try; 213 lines), axioms `[propext, Classical.choice, Quot.sound]`.

**SC4-d = T4′ constants bookkeeping** (`Surgery/Contract/FineCutNeckSupplyTolerances.lean`, ns
`…Surgery.Topology`), recorded before its first compile:
```lean
theorem inv_add_one_le_inv_of_le_div_one_add {εc eps : ℝ} (hεc : 0 < εc) (heps : 0 < eps)
    (h : eps ≤ εc / (1 + εc)) : εc⁻¹ + 1 ≤ eps⁻¹       -- SC2-e's `hfit`
theorem exists_fineCutNeckSupplyStrong_tolerances :
    ∃ eta εcone : ℝ, 0 < eta ∧ 0 < εcone ∧ εcone ≤ eta ∧ εcone ≤ 1 / 1000 ∧
      (SC2-c's body at eta) ∧ (T1 `false_of_terminal_capSide`'s body at eta) ∧ (SC4-c's body at eta)
```
(`eta := min` of the three tolerances, `εcone := min eta (1/1000)`; `εcone ≤ 1/1000` is SC1-d's
`capTubeHasNeckChart` accuracy, `εcone ≤ eta` makes the class accuracy admissible for SC2-c.)
- SC4-d PROVED, clean compile (first try), axioms `[propext, Classical.choice, Quot.sound]`.

## Deliverables (all new, uncommitted, not in the root aggregate)
| File | Lines | Headlines | Uncommitted deps |
|---|---|---|---|
| `Geometry/Metric/Distance/SeparatedSidePoint.lean` | 82 | `Geometry.Metric.exists_mem_riemannianEDistOf_eq_of_ball_diff_subset` | — |
| `Surgery/Topology/TracedRegionAncientKappaLimit.lean` | 144 | `ObservedHistory.exists_ancientKappa_pointed_limit_of_isTracedRegion` | X5c `Compactness/Limits/PointedLimitOrientation`, X5d `Surgery/Topology/AncientPointedFlowLimitBaseScalar` |
| `Surgery/Topology/TracedRegionLineNeck.lean` | 209 | `ObservedHistory.exists_eventually_spatialNeck_of_isTracedRegion_of_separating_set` | TracedRegionAncientKappaLimit, SeparatedSidePoint |
| `Surgery/Topology/HornSliceSeparatedSides.lean` | 211 | `TerminalCorePresentation.exists_eventually_separated_sides_of_frontier_scalar_lt` | — |
| `Surgery/Contract/FineCutNeckSupplyTolerances.lean` | 103 | `inv_add_one_le_inv_of_le_div_one_add`, `exists_fineCutNeckSupplyStrong_tolerances` | HornSliceSeparatedSides; SC2's `HistoryStrongNeckUniform` (→ SP1 `StrongNeckRestriction` → `TruncatedNeck` → `HistoryStrongNeck`, SC1 `InteriorCollar`, SC2 `TerminalSpatialCapMovingBarrier`, `TerminalHornCanonicalNeckUniform`, `TerminalFineNeckOfSpatialNecks`, `SpatialNeckOpenSubset`) |
(paths under `Geometry/Flow/RicciFlow/` except the first.)

- Compile: every file with `LEAN_NUM_THREADS=2 lake env lean -DmaxSynthPendingDepth=3
  -Dweak.linter.mathlibStandardSet=true`; uncommitted imports through scratch modules `SC4.*`
  (`--root` = `scratchpad/sc4`, the SC2-c chain rebuilt from the files on disk): zero output.
  `#lint in SC4`: only `docBlame`, and only on the other lanes' definitions (inapplicable).
- `#print axioms` for all 7 headlines: `[propext, Classical.choice, Quot.sound]` (scratch files, removed).
- New public names grep-unique library-wide. One `open private` (`horn_sides_of_complementPair`, as in
  `HornSeparationFrontierScalar.lean`); one private helper `exists_canonical_convergence_of_eq` (transport of
  the convergence maps along `flowOfMetric_atTime`). No copies of private lemmas; no committed file touched.
- Acceptance order: SeparatedSidePoint, HornSliceSeparatedSides (committed deps only); X5c, X5d →
  TracedRegionAncientKappaLimit → TracedRegionLineNeck; SC2-c's chain → FineCutNeckSupplyTolerances.
- Deferred merge (not done, import chain untouched): X5's inline packaging in `CrossingAncientLimit.lean`
  (pinching of the windows, cone, base scalar, orientation, κ-solution) is SC4-a; X5 could call it.

## Deviations
1. Piece 2's converter is for B13's format, not `:475`'s (Finding 1): `:475` does not feed T3A-2 any more
   (SC3 finding 1), and the transport back goes through `pointedAncientKappaLimit_eventually_spatialNeckWitness_of_intrinsic_line`,
   which consumes B13's canonical `MetricConvergenceData` directly. No windowed-model witnesses are built.
2. Piece 1 produces the line from a SEPARATING SET on the approximants (Cheeger–Gromov line lemma), not from
   two arms with a comparison-angle lower bound: comparison-angle monotonicity is not available on the
   approximants, and the arms lemmas are about `L`, not about `G(τ)`. The horn → approximant transfer is SC4-c
   (`L`'s neck sphere and horn sides, carried to `G(τ)` by `HornSeparationSliceTransfer`). The line need not
   pass through the base point: `PointedLineNeck.lean:83` accepts any line (`exists_strongNeck_of_line` is not
   used).
3. SC4-b's hypothesis was weakened once after its first clean compile (plain open sides instead of a
   `TwoSidedSeparation`, distances in `[A, 3A)` instead of exact), with the new lemma SC4-a′; both were logged
   right after proving (see above). SC4-d was logged before its first compile but after its proof was written.

## What T4′ still lacks after this wave
The contradiction skeleton is now: bad deep horn point `xₙ` (not an `εc`-neck of `Lₙ`) ⇒ (SC2-e contrapositive,
`eps ≤ εc/(1+εc)` via SC4-d) no spatial `eps`-neck of `Gₙ(τ)` at `xₙ` for `τ` near `sₙ` ⇒ choose `τₙ` ⇒ T3A-2
(SC3) `htraced` ⇒ SC4-c separation at `τₙ` ⇒ SC4-b: `eps`-necks of `Gₙ(τₙ)` at `xₙ` along a subsequence ⇒ ⊥.
Missing:
1. **GAP-L1 (bounded curvature at bounded normalized distance in `L`)**: SC4-c needs, for `A ≤ Aₙ` with
   `Aₙ → ∞`, (a) `closedBall_{Lₙ}(xₙ, 4A/√R_L(xₙ))` compact (equivalently: bounded scalar on it — the ball stays
   off the singular end), and (b) the core frontier farther than `2A/√R_L(xₙ)`. (b) follows from a scalar
   lower bound on the ball, e.g. `|∇ R^{-1/2}| ≤ η` on `Lₙ` (the class gradient bound `GradientBoundBefore Cgrad
   qcan` in the limit) together with `R_L(xₙ)/(Λ/r²) → ∞`; (a) is §4.2's cone exclusion at the terminal time
   (the `BoundedCurvatureAtDistance*` family is stated with cap parameters; a `p₀`-free terminal version is
   needed). The frontier-scalar hypothesis of SC4-c (`2·R(w) < N.scale`) is automatic once `Kfine ≥ 3`
   (`frontier_scalar_le`); the neck `N` at `xₙ` is `P.horn_spatial_neck`.
2. **T3A-2 (SC3)**: `htraced` at `(Hₙ, τₙ, xₙ, Rₙ)` for the chosen `τₙ`, plus B13's side inputs (`hsliver`/`t₀`,
   `hnc`, `hpinch`, `hwit`, `hderiv`) from the class.
3. **Assembly glue**: the diagonal choice of `τₙ` (finitely many `∀ᶠ τ` filters per `n`: SC2-e's
   contrapositive, SC4-c's `S`-bound and its clauses for `A = 1, …, mₙ`, T3A-2's), the identification
   `(Hₙ).stageMetric ((Hₙ).activeStage τₙ) τₙ = Gₙ.flow.base.metric τₙ` with `activeStage τₙ = last` and
   `time last < τₙ`, the scalar normalization `Rₙ = scalar at (τₙ, xₙ)` (SC4-b's `hscal`), and T4′'s statement
   (`FineCutNeckSupplyStrong`) wrapper with SC4-d's `eta εcone`.
