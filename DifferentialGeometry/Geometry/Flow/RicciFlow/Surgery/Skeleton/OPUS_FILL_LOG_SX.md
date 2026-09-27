# OPUS fill log SX — the SX leaf `spatialCrossingContinuation_holds` and the strong SX leaf

Worker: Fable 5.1, worktree D:\differential-geometry-pc3 (codex/pc-target-c-psf, HEAD e68bf6466 + lane files),
started 2026-09-26 ~16:30 PDT.
Scratch: C:\Users\liao9\AppData\Local\Temp\claude\D--differential-geometry-moise-int\08693914-694c-4a5b-8767-edd7f4799e4d\scratchpad\sx
(copied x7's `XP2B.*` scratch src/olean tree and `deps.sh`/`cc.sh` with the same module prefix; own `mko.sh` builds a
module's scratch olean; `gen2.py` assembles `CrossingAncientLimitSpatial.lean` from X5's and B13's statement text).
Compile: `lean -DmaxSynthPendingDepth=3 -Dweak.linter.mathlibStandardSet=true`, 4 threads, read-only, one module per call.
Nothing under `.lake`, no git writes, no lake build, root aggregate and `PoincareEndgame.lean` untouched.

## Targets (both `def`s consumed by C4A's assembly and SL1's leaf; NOT changed)
- SX = `SpatialCrossingContinuation P₀ g₀` (`Surgery/Topology/SpatialCrossingContinuation.lean`, 86 lines, lane C4A;
  H16 deltas already applied there: `0 < ε`, `εbar ≤ coneAccuracy`, `∃ Cx` before `∀ B`, C3's output as the
  `∀ η₃, 0 < η₃ → …On t₀ η₃ →` input, `η ≤ η₃ ∧ t₀ + η ≤ slab end`).
  Deliverable `Surgery/Topology/SpatialCrossingContinuationLeaf.lean`, theorem `spatialCrossingContinuation_holds`.
- strong SX = `StrongSpatialCrossingContinuation P₀ g₀` (`Surgery/Topology/StrongSpatialCrossingContinuation.lean`,
  lane SL1: SX prefixed by `∀ ε₁, 0 < ε₁ → ε₁ < 1/11 →`, `εbar ≤ ε₁`, conclusion `∃ W, W.capTubeHasNeckChart ε ∧
  ((∃ n, W.alternative = .neck n) → H.toHistory.HistoryStrongNeck k G ε₁ y t)`).
  Deliverable `Surgery/Topology/StrongSpatialCrossingContinuationLeaf.lean`, theorem
  `strongSpatialCrossingContinuation_holds`.

## Order decision (recorded): SX first, then strong SX
The two routes share everything up to the spatial finish; strong SX additionally needs the neck-branch splicing
(H20 (c): the survivor-flow strong neck of B8's `K` cut to depth 1/5 and identified with `HistoryStrongNeck`'s
`gflow` on the backward-survivor domain), which is new mathematics not in the tree (the SC lanes' `HistoryStrongNeck`
producers all consume the `StronglyCanonicalAt` implication; none builds `gflow` from a survivor-flow neck).
So SX is proved first; the B8-young variant already EXPORTS `K` and the survivor block so strong SX reuses it.

## Route (DESIGN_C4_ASSEMBLY §2: X5s, X6s, X7s), files and status
1. `Surgery/Topology/AncientLimitSurvivorCanonicalWitness.lean` (new, ~420 lines) — DONE, compiles clean
   (0 errors, 0 warnings, 54 s):
   - `FiniteHorn.eventually_exists_canonicalWitness_survivor_of_ancient_pointed_flow_limit`: the B8-young
     variant (H20 (a)). Same binders as B8's `eventually_scalar_derivative_bounds_of_ancient_pointed_flow_limit`;
     conclusion `∃ k, 2 * C + 1 < (k + 3 : ℕ) ∧ ∀ᶠ i, ∃ hy : basepoint ∈ W k (f (ψ i)),
     ∃ K : CanonicalWitness {h k (f (ψ i))} ε C C ⟨_, hy⟩ 0, K.capTubeHasNeckChart ε` — the `K` on the survivor
     flow `h k n` (B13's local Ricci flow on `W k n × [−(k+2), 0]` across surgeries) is exported with the cap-tube
     condition (B8's proof did `obtain ⟨K, -⟩`). Proof = B8's young-point proof with `k` enlarged by `2C`
     (`exists_nat_gt (2(rad+1) + T + 1 + 2C)`) and the transfer's output returned instead of the derivative
     projection. B8's private helpers used via `open private opensInclusion opensInclusion_symm_apply
     windowedModelWitnessOfLimitComparison mfderiv_restrict_open_apply scaleMetric_restrictOpen_eq from
     …AncientLimitCanonicalWitness` (no copy). A private local instance `SigmaCompactSpace U` for
     `U : Opens M` (B13's text) is needed to STATE `CanonicalWitness` on `W k n`.
   - `FiniteHorn.exists_spatialCanonicalWitness_of_canonicalWitness_restrictOpen` (X6s core, generic):
     `[CompactSpace M]`, `g`, `0 < R`, `U : Opens M`, `x : U`, `metricScalarAt g x = R`,
     `h 0 = scaleMetric R (g.restrictOpen U)`, `K : CanonicalWitness {h} ε C C x 0` with cap-tube,
     `closedBall_{scaleMetric R g}(x, 2C+1) ⊆ U` ⊢ `∃ W : SpatialCanonicalWitness g ε C C x.val,
     W.capTubeHasNeckChart ε ∧ ((∃ n, W.alternative = .neck n) → ∃ n, K.alternative = .neck n)`.
     Route: `K.toSpatial` (radius ≤ C since the scaled scalar at x is 1) → cast to the local-pull metric
     (`scaleMetric_restrictOpen_eq`, `localPullMetric_subtype_val`) → `SpatialCanonicalWitness.pushforwardOfInjective`
     along `Subtype.val : U → M` (compactness of the subtype closed ball of radius 2C+1 from the ambient
     compact closed ball: `IsInducing.subtypeVal.isCompact_preimage'`, `riemannianEDistOf_le_restrictOpen`,
     `isClosed_riemannianClosedBallOf`) → `.scaleMetric R⁻¹` and `scaleMetric R⁻¹ (scaleMetric R g) = g`
     (`ext_inner` + `scaleMetric_inner`). The neck-label implication (for strong SX) is tracked through every step
     by private `cases` lemmas (`exists_neck_of_cast_metric/point`, `…_of_alternative_pushforward_eq_neck`,
     `…_of_witness_pushforward_eq_neck`, `…_of_alternative_scaleMetric_eq_neck`, `…_of_toSpatial_eq_neck`).
   - Private COPIES (deferred merge): `domain_subset_of_ball_subset` and `metricDistance_le_image` from
     `SpatialCanonicalWitnessTransport.lean:895–928` (private there; needed by name in a `change`, because
     proof-irrelevance leaves the `hdist` argument of the alternative pushforward unassignable by unification).
2. `Surgery/Topology/CrossingAncientLimitSpatial.lean` (new, 300 lines) — X5s, compiles (0 errors; one
   `hlt`-unused warning in the corollary being removed):
   - `ObservedHistory.exists_eventually_canonicalWitness_survivor_of_isTracedRegion`: X5's binders WITHOUT the
     age split (`hmode` dropped — H16 "no split by age"; `hlt` binder kept, anonymous), `∃ epsW, ∀ ε ≤ epsW, ∃ C ≥ 1,
     …`, conclusion = B13's survivor block `∃ W h, (∀ k, ∀ᶠ n, hblock k n)` verbatim ∧ `∃ ψ StrictMono, ∃ k,
     2C+1 < k+3 ∧ ∀ᶠ i, ∃ hy K, K.capTubeHasNeckChart ε` (the data strong SX needs). Proof = X5's proof
     (B13 → κ-solution limit via `ancient_pointed_flow_limit_curvatureOperator_nonnegative_and_complete`,
     `metricScalarAt_basepoint_eq_of_local_flow_limit`, `nonempty_tangentOrientationSection_of_pointedConvergence`,
     `isAncientKappaSolution_flowOfMetric_of_curvatureOperator_nonnegative`) with the B8 call replaced.
     Copy of ~100 proof lines of X5 (`CrossingAncientLimit.lean`, uncommitted, lane XA1): deferred refactor —
     factor the "B13 → κ-solution data" prefix into a shared lemma when X5 is next touched.
   - `ObservedHistory.exists_eventually_spatialCanonicalWitness_of_isTracedRegion` (corollary, the SX input):
     same binders, conclusion `∃ ψ StrictMono, ∀ᶠ i, ∃ Wt : SpatialCanonicalWitness (stageMetric (activeStage t) t)
     ε C C (y (ψ i)), Wt.capTubeHasNeckChart ε`, by the conversion lemma at `n = ψ i` (`hh0` from the block's
     current-slab clause at `s = 0`, `hball` from `W k n = ball(k+3)` and `2C+1 < k+3`, `CompactSpace` from
     `OrientedThreeStage.compact`).
3. `Surgery/Topology/SpatialCrossingContinuationLeaf.lean` (new, 428 lines) — X7s, DONE 2026-09-26 ~17:00 PDT:
   `spatialCrossingContinuation_holds (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) : SpatialCrossingContinuation P₀ g₀`,
   fully proved, unconditional. Compile (scratch chain, standard linter set, 4 threads): EXIT 0, zero output, 59 s.
   Axioms (scratch probe importing the leaf's scratch olean, `#print axioms`, probe deleted):
   `spatialCrossingContinuation_holds`, `ObservedHistory.exists_eventually_spatialCanonicalWitness_of_isTracedRegion`,
   `ObservedHistory.exists_eventually_canonicalWitness_survivor_of_isTracedRegion`,
   `FiniteHorn.eventually_exists_canonicalWitness_survivor_of_ancient_pointed_flow_limit`,
   `FiniteHorn.exists_spatialCanonicalWitness_of_canonicalWitness_restrictOpen`: all
   `[propext, Classical.choice, Quot.sound]`, no `sorryAx`. No `sorry`, no comments, no docstrings, no options, all
   non-import lines ≤ 100 characters, no trailing whitespace. The three modules recompile clean after the File-1 tidy
   (single `omit`, wrapped line). Route as planned below (the X1 copy is `exists_spatial_crossing_bad_point`, generic in
   the per-point clause `Φ`, so the event/terminal branches pass `Φ y t := R(t−a) < θ ∧ ¬CWP ∧ ∀ W, ¬capTube`); the
   age split of X7 (`σ₀`) is dropped (X2 called with `σ₀ := id`). Private copies in the leaf (deferred merges):
   `derivativeBoundBefore_double` (= `CrossingTracedRegion.lean:29`), `le_static_scale_of_neckRadius_le` and
   `metricScalarAt_extendAt_eq` (= X7's private adapters, `CrossingContinuationLeaf.lean`), the X1 body (=
   `CrossingBadPoint.lean`, generalized over the clause — deferred merge: generalize X1 and make X7 consume it).
   Original design of the leaf:
   - `εbar := min coneAccuracy (min epsW (min crossingNeckAccuracy crossingWindowNeckAccuracy))`, `Cx := C` (X5s's).
   - No floors: per-`n` constants `Dₙ = n+1`, `θcapₙ = 1 − 1/(n+2)`, `q₀ₙ = n+1`, `mcapₙ = n+2`,
     `δmaxₙ = 1/(n+1)`, `ρmaxₙ = √(1/(2(n+1)qcanₙ))`, `εcapₙ = 1/(n+1)` (no slab-start `Rs qsS ms δs ρs εs`).
   - X1 copy with the spatial failure clause (`exists_spatial_crossing_bad_point_terminal`, private in the leaf):
     X1's `hfail` is hard-wired to `CanonicalBoundsOn`; the copy takes the `push Not` form of SX's clause
     (`∀ η, 0 < η → η ≤ η₃ → t₀ + η ≤ s → ∃ y t, … ∧ ∀ W, ¬ W.capTubeHasNeckChart ε`), adds `η₃` to the `min`,
     returns `η ≤ η₃`, `t₀ + η ≤ s` and the bad point with `¬ ∃ W`. Deferred merge: generalize X1 over the clause.
   - Sliver derivative supply from the C3 output instead of F9: P0 `derivativeBoundBefore_of_derivativeBoundOn`
     at `t₀ + η₀`, `η₀ := min η₃ ((s − t₀)/2)`, then the private `derivativeBoundBefore_double`
     (`CrossingTracedRegion.lean:29`, copied or `open private`) to `(2Ctime, 2qcan)`. No `0 < Ctime` needed.
   - Σ context identical to X7's (X3, X4, X4ext consumed as delivered); in the infinite-depth branch X5s's
     corollary replaces X5, and a private adapter (X6s) carries `SpatialCanonicalWitness (stageMetric (activeStage τ) τ) … ŷ`
     of `Kₙ = extendAt` to `SpatialCanonicalWitness (G.flow.base.metric t) … y` by
     `activeStage_extendHorizon_eq_last` + `stageMetric_extendHorizon_last_of_mem_Icc` (pattern of X7's
     `metricScalarAt_extendAt_eq`), contradicting the bad clause.
## Skeleton edit text for C4 (acceptance lane; `PoincareEndgame.lean` and `DifferentialGeometry.lean` untouched by me)
With C4A's I29 applied (`OPUS_FILL_LOG_C4A.md`: `∃ εbar` at `SpatialCanonicalContinuation.lean:145`, the 8-line `min εbar εs`
change in `CanonicalNeighborhoodsThroughSurgeryStrong.lean:278–284`, Cases file's L renamed
`spatialCanonicalContinuation_of_spatialCrossing`), in `Surgery/Skeleton/PoincareEndgame.lean` add
```lean
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SpatialCanonicalContinuationCases
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SpatialCrossingContinuationLeaf
```
and replace the C4 leaf by
```lean
theorem spatialCanonicalContinuation (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    SpatialCanonicalContinuation P₀ g₀ :=
  spatialCanonicalContinuation_of_spatialCrossing P₀ g₀ (spatialCrossingContinuation_holds P₀ g₀)
```
(no separate `spatialCrossingContinuation` sorry leaf is needed). Root aggregate: register, after X7's 36 suppliers
(`OPUS_FILL_LOG_X7.md`, a valid build order) and `SpatialCrossingContinuation`, `SpatialCanonicalContinuationCases`,
`CapWindowSpatialCanonicalWitness` (C4A/M5):
    import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.AncientLimitSurvivorCanonicalWitness
    import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingAncientLimitSpatial
    import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SpatialCrossingContinuationLeaf
Uncommitted suppliers of the SX leaf beyond X7's list: none (its imports are X7's suppliers, the committed
`AncientLimitCanonicalWitness`/`TracedRegionAncientLimitScalarBound`/X1's three committed imports, C4A's
`SpatialCrossingContinuation` and `SpatialCanonicalContinuationCases`).

4. `Surgery/Topology/StrongSpatialCrossingContinuationLeaf.lean` — IN PROGRESS from 2026-09-26 ~17:05 PDT, on the
   watcher's route (`WATCH_SX.md` cycle 1, adopted; recorded here): do NOT identify B13's `h k n` with `gflow` on the
   window (the `MetricComparisonOn` fields `pullback_eq`/`jet_zero` quantify over ALL times, so every exact neck
   transport needs equality for every τ); instead feed B8-young with `h' k n σ := scaleMetric R ((gflow k n (t+σ/R))`
   pulled back to `W k n`)`, where `gflow k n` is the SPLICED survivor-domain flow on
   `U k n := H.backwardSurvivorDomain (activeStage (a k n)) k`, so K's neck is exact for `gflow` at every τ.
   Bricks (statements to be recorded before proving):
   (A) `ObservedHistory.exists_backwardSurvivor_incomingSlab_flow`: for `first ≤ k`, an incoming slab `G` of stage `k`
       with `G.metric (time k) = initialMetric k`: `∃ gflow` on `backwardSurvivorDomain first k` with the event-slab
       identities, `gflow τ = (G.metric τ).restrictOpen U` on `Ico (time k) s`, and `IsSolutionOn` on
       `closedOpen (time first) s` (`first = k`: `isSolutionOn_restrictOpen`; `first < k`: `ite` at `time k` of
       `exists_backwardSurvivor_isSolutionOn` and `G.restrictOpen U`, `Solution/Seam.lean` + `G.smoothUpTo` joint
       smoothness on `Ico`, assembled on `closedOpen` from the closed pieces `[time first, b']` by
       `isSolutionOn_of_joint_metric`).
   (P) `historyStrongNeck_of_prefixAt : (H.prefixAt k).toHistory.HistoryStrongNeck (Fin.last _) G eps y t →
       H.toHistory.HistoryStrongNeck k G eps y t` (needed: the event branch of the X-core works on `H.prefixAt`;
       `Fin.castLE` reindexing + `backwardPointTraceOfPrefix` + `backwardSurvivorMap_eq_point`).
   (B) block traces: the block's `f j`, `RegularCrossing`, `f top = val` give `BackwardPointTrace` of every `x ∈ W k n`
       (field copy across `extendHorizon`), hence `W k n ⊆ U k n` and `backwardSurvivorMap j = f j` on `W k n`.
   (D) neck transports: `StrongNeck.ofParabolic` (exists), a `StrongNeck` pushforward along the open inclusion
       `W k n ↪ U k n` (converse of `StrongNeck.restrictOpen`, pattern `SpatialNeck.ofRestrictOpen`),
       `TruncatedNeck.ofStrongNeck` at depth 1/5 with jets from `IsSolutionOn gflow` (exists), `TruncatedNeck.mono` to ε₁.
   (X5s′) `CrossingAncientLimitStrong.lean`: X5s with per-`n` slab data `Gn` of the active stage (metric = stage metric
       on `[time k, t]`, `t < s`), `ε ≤ ε₁`, concluding the spatial witness with
       `(∃ n, W.alternative = .neck n) → (H n).HistoryStrongNeck (activeStage t) Gn ε₁ y t`.
   (L′) the strong leaf: SX's leaf with `εbar` also `≤ ε₁`, the X5s′ output, `historyStrongNeck_extendHorizon_iff`
       (terminal branch) and (P) (event branch).
   Progress 2026-09-26 ~17:40 PDT: (A) DONE — `Surgery/Topology/HistoryStrongNeckSurvivorSlab.lean` (128 lines),
   `ObservedHistory.exists_backwardSurvivor_incomingSlab_flow` exactly as stated in (A), compiles clean (37 s;
   `first = k` by `isSolutionOn_restrictOpen`, `first < k` by the `ite` of `exists_backwardSurvivor_isSolutionOn` and
   `G.restrictOpen`, `Seam.lean`'s two lemmas on every `[time first, b']`, `b' < s`, assembled on `closedOpen` by
   `isSolutionOn_of_joint_metric` with `ContMDiffWithinAt.mono_of_mem_nhdsWithin`). (D) DONE —
   `Perelman/CanonicalNeighborhood/StrongNeckPullbackTransport.lean` (108 lines): `StrongNeck.castTime`,
   `StrongNeck.ofMetricEq` (equal metric families across domains, window inside the new carrier),
   `StrongNeck.ofLocalPullback` (along an injective local diffeomorphism, via `MetricComparisonOn.mapIsometry` and
   `IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_injOn`), compiles clean (45 s); private copy of B8's
   `rescaledMetric_congr_scale` (deferred merge: promote it in `AncientLimitCanonicalWitness.lean`). NEXT: the
   per-index brick (B)+(C) `SurvivorBlockStrongNeck.lean` (block traces ⇒ `W ⊆ U`, `backwardSurvivorMap = f`,
   the identity `h σ = scaleMetric R (localPullMetric (gflow (t+σ/R)) ι)` on `[−(k+2), 0]`, and the packaging
   `StrongNeck {h'} → HistoryStrongNeck`), then X5s′, then (P), then the leaf.
   Progress ~18:30 PDT: (B)+(C)+packaging DONE — `Surgery/Topology/SurvivorBlockStrongNeck.lean` (~250 lines):
   `ObservedHistory.exists_survivor_flow_of_block` (block data ⇒ `first := activeStage a`, `W ⊆ U`, the spliced
   `gflow` of (A) with `time first ≤ t − 2(k+2)/R`, and the window identity
   `h σ = scaleMetric R (localPullMetric (gflow (t+σ/R)) ι)` on `[−(k+2), 0]`, by cases on the active stage of
   `t + σ/R`: top stage via `hcur`/`hG`/`htop`, earlier stage via `hslabs`, `extendedMetric_before`,
   `backwardSurvivorTerminalMap_val`, `stageMetric_castSucc_apply`, `localPullMetric_comp` and trace uniqueness
   `backwardSurvivorMap_eq_point`) and `ObservedHistory.historyStrongNeck_of_survivor_strongNeck` (a `StrongNeck`
   of `{hfam}` on `W`, `hfam σ = scaleMetric R (localPullMetric (gflow (t+σ/R)) ι)`, gives
   `H.HistoryStrongNeck (activeStage t) G ε₁ y t` by `ofMetricEq` → `ofParabolic` → `castTime` →
   `ofLocalPullback` → `TruncatedNeck.ofStrongNeck` at depth 1/5 → `.mono`); compiles clean.
   (X5s′) DONE — `Surgery/Topology/CrossingAncientLimitStrong.lean` (~300 lines):
   `ObservedHistory.exists_eventually_strong_spatialCanonicalWitness_of_isTracedRegion`: X5s's binders plus
   `∀ {ε₁}, ε ≤ ε₁ → ε₁ < 1/11 → ∀ (s) (Gs : ∀ n, slab of the active stage), (∀ n, t n < s n) →
   (∀ n, Gs n = stage metric on [time k, t n]) → ∃ ψ StrictMono, ∀ᶠ i, ∃ Wt, Wt.capTube ε ∧ ((∃ n, Wt.alt = .neck n)
   → (H (ψ i)).HistoryStrongNeck (activeStage (t (ψ i))) (Gs (ψ i)) ε₁ (y (ψ i)) (t (ψ i)))`. Proof: X5s's
   proof; block thresholds `Nb` by `choose` on `hblock`; per `(k, n ≥ Nb k)` the survivor flow of the brick,
   `choose`d; `h' k n := if Nb k ≤ n then the pulled-back rescaled gflow else h k n`; B8-young's three `h`-hypotheses
   for `h'` from `h' = h` on `[−(k+2), 0]` (`IsSolutionOn.congr_metric`, the current-slab identity, `hconv` with the
   index eventually ≥ `Nb k`); then the conversion lemma (spatial witness with the neck-label implication) and
   the packaging brick on `data.strong`. Compiles clean (41 s). NEXT: brick (P) `HistoryStrongNeckPrefix.lean`
   (written, compiling), then the strong leaf.
   Progress ~19:15 PDT: (P) DONE — `Surgery/Topology/HistoryStrongNeckPrefix.lean` (~120 lines):
   `RetainedCoreHistory.historyStrongNeck_of_prefixAt : (H.prefixAt k).toHistory.HistoryStrongNeck (Fin.last _) G eps
   y t → H.toHistory.HistoryStrongNeck k G eps y t` (private copy of SC's `strongNeckBody` as `neckBody`; the prefix
   body transfers to `H` at `Fin.castLE first` by `subst` of the survivor-domain equality — traces both ways via
   `backwardPointTraceOfPrefix` and a private converse — and the reindexed terminal maps agree by
   `backwardSurvivorMap_eq_point`). Compiles clean. (L′) `Surgery/Topology/StrongSpatialCrossingContinuationLeaf.lean`
   (497 lines) generated from the SX leaf: `εbar` also `≤ ε₁`; Φ carries `∀ W, capTube → (∃ n, neck) ∧ ¬HSN` (shape
   confirmed by a `push Not` probe); event branch: `¬HSN_H` ⇒ `¬HSN_prefix` by (P); infinite branch: X5s′ on the
   extended histories with the slabs cast along `activeStage τ = Fin.last` (adapters `slab_metric_of_extendAt`,
   `strong_clause_of_extendAt` by generalize/subst and `historyStrongNeck_extendHorizon_iff`).
   STRONG SX DONE ~19:40 PDT: `strongSpatialCrossingContinuation_holds (P₀ : OrientedThreeStage.{u})
   (g₀ : P₀.Metric) : StrongSpatialCrossingContinuation P₀ g₀` compiles clean (42 s, zero output, linter set on),
   fully proved, unconditional; both `def`s (SX, strong SX) untouched. Final verification sweep and axioms: see
   "Final verification" at the end of this log.
   Original plan text kept below for reference. Plan (H20 (b)–(d)): same leaf
   with `α := ε` from B8 (no second transport), `εbar ≤ ε₁` added to the `min`; witness `W` = the conversion
   lemma's output from `K` (label implication kept); neck branch: `K.alternative = .neck data` gives
   `data.strong : StrongNeck {h k n} ε ⟨y,hy⟩ 0`, `TruncatedNeck.ofStrongNeck` at depth 1/5 (jet differentiability
   from `IsSolutionOn {h k n}` and `Ioo (−1) 0 ⊆ regular`), then the parabolic unscaling and the identification of
   `h k n` on `[−1/5, 0]` with `gflow` on `backwardSurvivorDomain first k` (survivor maps `f j` of the block vs
   `backwardSurvivorMap`, `RegularCrossing` ⇒ unique backward traces) — open; if it does not close, the exact
   remaining statement will be recorded here.

## Deviations so far
- Conversion lemma states `hh0 : h 0 = scaleMetric R (g.restrictOpen U)` (B13's form) rather than
  `(scaleMetric R g).restrictOpen U`.
- Two private lemmas copied from `SpatialCanonicalWitnessTransport.lean` (see 1.).
- X5's κ-solution prefix duplicated in X5s (see 2.).

## Deliverables (all new, uncommitted, not in the root aggregate; no committed file touched)
| File | Lines | Headline |
|---|---|---|
| `Surgery/Topology/AncientLimitSurvivorCanonicalWitness.lean` | 462 | B8-young variant exporting `K` on the survivor flow; `K ↦` ambient spatial witness with the neck-label implication |
| `Surgery/Topology/CrossingAncientLimitSpatial.lean` | 300 | X5s `exists_eventually_canonicalWitness_survivor_of_isTracedRegion`, corollary `exists_eventually_spatialCanonicalWitness_of_isTracedRegion` |
| `Surgery/Topology/SpatialCrossingContinuationLeaf.lean` | 429 | `spatialCrossingContinuation_holds` (SX) |
| `Surgery/Topology/HistoryStrongNeckSurvivorSlab.lean` | 126 | (A) `ObservedHistory.exists_backwardSurvivor_incomingSlab_flow` |
| `Perelman/CanonicalNeighborhood/StrongNeckPullbackTransport.lean` | 109 | (D) `StrongNeck.castTime`, `StrongNeck.ofMetricEq`, `StrongNeck.ofLocalPullback` |
| `Surgery/Topology/SurvivorBlockStrongNeck.lean` | 266 | (B)+(C) `ObservedHistory.exists_survivor_flow_of_block`, `ObservedHistory.historyStrongNeck_of_survivor_strongNeck` |
| `Surgery/Topology/CrossingAncientLimitStrong.lean` | 304 | X5s′ `ObservedHistory.exists_eventually_strong_spatialCanonicalWitness_of_isTracedRegion` |
| `Surgery/Topology/HistoryStrongNeckPrefix.lean` | 123 | (P) `RetainedCoreHistory.historyStrongNeck_of_prefixAt` |
| `Surgery/Topology/StrongSpatialCrossingContinuationLeaf.lean` | 500 | `strongSpatialCrossingContinuation_holds` (strong SX) |

Order decision recorded: SX was proved first (its leaf is the C4 input and the strong route needed five extra
bricks); strong SX reuses the same B8-young export and the same leaf skeleton.

## Deviations (from the task text / designs), with reasons
1. The conversion `K ↦ W` takes `hh0 : h 0 = scaleMetric R (g.restrictOpen U)` (B13's form) and `[CompactSpace M]`
   (the stage carrier is compact; H16's compact closed ball of radius `ρ` is not needed separately).
2. No window congruence for `MetricComparisonOn` (impossible without off-window pull-backs, `WATCH_SX.md`): B8-young
   is fed `h'` built from the SPLICED survivor-domain flow, so the neck comparison is exact for every time.
3. The event branch lands on the ORIGINAL history through the new transport (P) along `prefixAt` (the X-core's
   event branch necessarily works on `H.prefixAt j.castSucc`); no `HasStrongNeckAt`/SC1-d trigger is used (it
   needs the strong class clause, which strong SX supplies, so it would be circular).
4. Accuracy: `α := ε` from B8 in both leaves; the truncated neck is `.mono`'d to `ε₁` (`ε ≤ ε₁ < 1/11`); no second
   approximate transport (H20 (d)).
5. The strong leaf's `εbar = min ε₁ (min coneAccuracy (min epsW (min crossingNeckAccuracy crossingWindowNeckAccuracy)))`.
6. `hlt` (time of the active stage `< t`) is kept as an anonymous hypothesis of X5s/X5s′ (it supplies B8-young's
   left-window hypothesis); X5's age split `hmode` is dropped.

## Deferred merges (private copies; no committed file edited)
- `derivativeBoundBefore_double` (= `CrossingTracedRegion.lean:29`), `le_static_scale_of_neckRadius_le`,
  `metricScalarAt_extendAt_eq` (= X7's private adapters, `CrossingContinuationLeaf.lean`) — copied into BOTH leaves;
  the X1 body (`exists_spatial_crossing_bad_point`, generic in the per-point clause `Φ`) copied into both leaves —
  merge: generalize `CrossingBadPoint.exists_crossing_bad_point_terminal` over the clause, make X7 consume it, and
  move the three adapters into a shared module consumed by X7, SX and strong SX.
- `domain_subset_of_ball_subset`, `metricDistance_le_image` (= `SpatialCanonicalWitnessTransport.lean:895–928`) in
  `AncientLimitSurvivorCanonicalWitness.lean` — merge: make them public in Transport.
- `rescaledMetric_congr_scale` (= B8's private) in `StrongNeckPullbackTransport.lean` — merge: promote it in
  `AncientLimitCanonicalWitness.lean`.
- `localPullMetric_congr_fun` (private) in `SurvivorBlockStrongNeck.lean` — a generic `localPullMetric` congruence;
  home `Geometry/Metric/Pullback/Local.lean`.
- `neckBody` (= SC's private `strongNeckBody`, `HistoryStrongNeckExtendHorizon.lean:19`) in
  `HistoryStrongNeckPrefix.lean` — merge: make SC's public and reuse.
- X5's κ-solution prefix (B13 → `ancient_pointed_flow_limit_curvatureOperator_nonnegative_and_complete` → orientation
  → `isAncientKappaSolution_flowOfMetric_of_curvatureOperator_nonnegative`) duplicated in X5s and X5s′ — merge:
  factor it into one lemma in `CrossingAncientLimit.lean`.
- The two leaves share ~250 lines (private adapters + Σ package); the SX leaf could be derived from the strong one
  through SL1's `spatialCrossingContinuation_of_strongSpatialCrossingContinuation`, which would retire
  `SpatialCrossingContinuationLeaf.lean` and the corollary of `CrossingAncientLimitSpatial.lean` (kept so that the
  C4 chain does not depend on the strong chain).

## Skeleton edit text for S (acceptance lane; SL1's `StrongNecksOfCutoffClass` route, `OPUS_FILL_LOG_SL2.md`)
In `Surgery/Skeleton/PoincareEndgame.lean` add
```lean
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StrongSpatialCrossingContinuationLeaf
```
and use
```lean
theorem strongNecksOfCutoffClass (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    StrongNecksOfCutoffClass P₀ g₀ :=
  strongNecksOfCutoffClass_of_strongSpatialCrossing P₀ g₀ (strongSpatialCrossingContinuation_holds P₀ g₀)
```
(no `strongSpatialCrossingContinuation` sorry leaf). The C4 edit text is above ("Skeleton edit text for C4");
alternatively C4 may consume `spatialCrossingContinuation_of_strongSpatialCrossingContinuation P₀ g₀
(strongSpatialCrossingContinuation_holds P₀ g₀)` in place of `spatialCrossingContinuation_holds P₀ g₀`.

## Supplier import order (root aggregate; from deps.sh on the strong leaf after ACC14 committed X7's chain, the
SX/strong-SX defs and the SP1/SC files — a valid build order; every other import is committed)
    import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.AncientLimitSurvivorCanonicalWitness
    import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingAncientLimitSpatial
    import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SpatialCrossingContinuationLeaf
    import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryStrongNeckPrefix
    import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryStrongNeckSurvivorSlab
    import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.StrongNeckPullbackTransport
    import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SurvivorBlockStrongNeck
    import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingAncientLimitStrong
    import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StrongSpatialCrossingContinuationLeaf
