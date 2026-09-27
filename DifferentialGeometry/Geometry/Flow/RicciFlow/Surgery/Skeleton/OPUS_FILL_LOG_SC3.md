# OPUS fill log SC3: T4′ consumer wave 3 = T3A-2 backward extension on θ₀-windows (2026-09-26)

Worker lane SC3. Scope: H13/H17 T3A-2 — one backward extension step on `HistoryStrongNeck` windows,
the event-endpoint step, the iterated window supply. New files only; read-only compiles
(`LEAN_NUM_THREADS=2 lake env lean -DmaxSynthPendingDepth=3 -Dweak.linter.mathlibStandardSet=true`),
uncommitted imports via scratch modules `SC3.*` under the session scratchpad `sc3/`. No git writes,
no lake build, no root-aggregate edit.

## Progress

- read AGENTS.md (pc3: no header, no module docstring, zero comments), H13/H17 digests,
  DESIGN_S_SUPPLY §0–§3, SP1 log (Round 2; `HistoryStrongNeck.lean` on disk is already θ₀ = 1/5:
  window `H.time first ≤ t - 1/5 * R⁻¹`, `TruncatedNeck … eps (1/5) z t`), SC1 log,
  `TerminalScalarAncientLimit.lean:475`, `HistorySurvivorFlow.lean`, `TracedRegion*.lean`.
- scratch chain built: `SC3.StrongNeckRestriction` → `SC3.TruncatedNeck` → `SC3.HistoryStrongNeck`
  (SP1 files as on disk, θ₀ = 1/5), all compile clean.

## Findings before the statements (failures first)

1. **`TerminalScalarAncientLimit.lean:475` is not the tree's window currency for histories.** Its
   windows are `S n j` on `U n ⊆ P.limit` pulled back from a `FlowSequence` whose terms are single
   smooth flows with a precomputed time-0 limit `P`. A surgery history is not one flow; the tree
   already converts history windows into ancient limits through `ObservedHistory.isTracedRegion`
   (`TracedRegion.lean:76`) and the composed headline
   `exists_bounded_ancient_pointed_flow_limit_of_spatially_canonical_before`
   (`TracedRegionAncientLimitScalarBound.lean:42`, hypothesis `htraced : ∀ A T, ∃ K, ∀ᶠ n,
   isTracedRegion (t n) (y n) (A/√R n) (T/R n) (K R n)`), which outputs a bounded ancient limit and
   needs neither `hneck` nor `∂R ≥ 0`. DEVIATION (recorded before proving): the window supply is
   produced in the `isTracedRegion` currency (the exact `htraced` shape at each depth), not as
   `S n j`/`hslab`/`hneckRegular`. `hneckRegular` only feeds `∂R ≥ 0` for the `:475` route, which the
   `htraced` route does not need.
2. **What the strong neck is needed for.** Curvature on a new layer does NOT need the neck when the
   layer is short: `TracedRegionBackwardStep.lean:299` already gives `R ≤ 2QR₀` on depth
   `1/(8·Ctime·QR₀)` from the class derivative bound — but ONLY for traces that already exist
   (`htrace` input). The neck supplies (i) EXISTENCE of the backward traces across events
   (`backwardSurvivorDomain`, H17 S2e point) and (ii) curvature control on the whole θ₀-window,
   whose normalized depth `1/5` exceeds the derivative-bound reach `1/(4·Ctime)` when `Ctime > 5/4`.
3. **Uniform depth increment.** Per-window loss `(1+Cε)` would make the depths summable. The cylinder
   comparison at the neck CENTRE gives `R(v)/Q ∈ [(1−r)⁻¹ − δ, (1−r)⁻¹ + δ]`, `r = Q(v−t) ∈ [−1/5,0]`,
   `δ = scalarComparisonC 3 eps (1/2) ≤ 364.5·eps`. Choosing the next slice in the lower half
   `r ∈ [−1/5, −1/10]` gives `R ≤ (10/11 + δ)Q ≤ Q` (for `δ ≤ 1/11`): the slice maximum never
   increases, so every step gains at least `1/(10·Q_top)` = θ₀/(2R_max) and the depth is unbounded.
   Lower bound per step `R ≥ (5/6 − δ)Q ≥ (3/4)Q`, so after `N ≤ ⌈10·Q·T⌉` steps `R ≥ Q(3/4)^N`:
   the neck hypothesis is only needed above a floor `L ≤ Q_low·(3/4)^(N+1)`, which the consumer meets
   with `L = qcan` because `R_n → ∞` at fixed normalized depth.
4. **Event endpoints.** The next slice is chosen off the finitely many event times (the class clause
   is on open slabs `Ioo (time k) t₀`); a window may still START at an event time — handled by the
   survivor-flow/stage identification at stage times (`backwardSurvivorInitialMetric`), no buffer.

## Lead message (cap-window points carry CAP witnesses) — delta
- Received mid-lane: at `CapWindowPoint`s SP2 produces a cap witness, so no backward window exists
  there; the extension step must not assume `HistoryStrongNeck` everywhere on the slice.
- Delta: the ENGINE (SC3-c) keeps an abstract, trace-local supply hypothesis (`HasStrongNeckAt` only
  at points of the traces of the ball points, only on non-event slices, only above a floor `L`);
  the PUBLIC extension step (SC3-e) takes the lead's shape instead: the class clause
  (`EventSlabsStronglyCanonical` + the terminal `StronglyCanonicalBefore`) plus `eps`-fine spatial
  necks (`eps ≤ eta(C1,C2)` of SC1-d) at those trace points, and derives `HasStrongNeckAt` there
  through SC1-c/SC1-d (`exists_tolerance_historyStrongNeck_of_spatialNeck`). The fine necks are what
  the consumer gets from closeness to the ℝ×N limit on balls of radius `Aₙ → ∞`.

## Statements (recorded BEFORE proving; elaborated with `sorry` first)

**SC3-a** (generic, `Perelman/CanonicalNeighborhood/TruncatedNeckScalar.lean`, ns `…FiniteHorn`):
```lean
theorem CylinderReference.metric_eq_cylinderReferenceMetric (C : CylinderReference) {s : ℝ}
    (hs : s ≤ 0) : C.metric s = cylinderReferenceMetric s
theorem ricciSharp_cylinderReferenceMetric {s : ℝ} (hs : s ≤ 0) (y : Cylinder)
    (v : TangentSpace IC y) :
    ricciSharp (cylinderReferenceMetric s) y v = ((2 * (1 - s))⁻¹ • v.1, (0 : ℝ))
theorem sqrt_inner_ricciSharp_cylinderReferenceMetric_le … ≤ (1 / 2) * Real.sqrt (g.inner y v v)
theorem TruncatedNeck.abs_scalar_center_sub_le (nk : TruncatedNeck S eps depth x t) {r : ℝ}
    (hr : r ∈ Icc (-depth) 0) :
    |(S.scalar t x)⁻¹ * S.scalar (t + r / S.scalar t x) x - (1 - r)⁻¹| ≤ 2400 * eps
```
The scalar of the cylinder comparison at the neck CENTRE along the whole truncated window (the
cylinder `2(1−r)g_{S²}+dz²` has `R = (1−r)⁻¹`). Route: Ricci♯ trace on the cylinder model (`IC` has no
inner-product model space, so `MetricComparisonOn.scalar_sub_le_of_ricci_bound` does not apply):
`ricciSharp_difference_bound_of_small_metric_derivatives` + trace bound. PROVED, clean.

**SC3-b** (`Surgery/Topology/HistoryStrongNeckTrace.lean`, ns `…Surgery.Topology.ObservedHistory`):
```lean
def HasStrongNeckAt (H : ObservedHistory.{u}) (eps : ℝ) (v : Icc (0 : ℝ) H.horizon)
    (p : (H.stageAt v).Carrier) : Prop :=
  ∃ (s : ℝ) (G : (H.stage (H.activeStage v)).IncomingSlab (H.time (H.activeStage v)) s),
    (v : ℝ) < s ∧
    (∀ τ ∈ Icc (H.time (H.activeStage v)) (v : ℝ),
      G.flow.base.metric τ = H.stageMetric (H.activeStage v) τ) ∧
    H.HistoryStrongNeck (H.activeStage v) G eps p v
theorem scalar_backwardSurvivor_eq_stageMetric   -- the event-endpoint identification
  (gflow on backwardSurvivorDomain first k with the slab/terminal equalities of HistoryStrongNeck,
   G = stage metric on [time k, t]) : for v ∈ stageDomain m, first ≤ m ≤ k, v ≤ t, v < s,
   metricScalarAt (gflow v) z = metricScalarAt (H.stageMetric m v) (backwardSurvivorMap … m … z)
   (covers v = an event time: stageDomain m ∋ time m, initial metric)
theorem exists_backwardPointTrace_scalar_bounds_of_hasStrongNeckAt
    {eps : ℝ} {t : Icc (0 : ℝ) H.horizon} {y : (H.stageAt t).Carrier}
    (h : H.HasStrongNeckAt eps t y) :
    0 < metricScalarAt (H.stageMetric (H.activeStage t) t) y ∧
    ∃ (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t),
      (a : ℝ) = t - (5 * metricScalarAt (H.stageMetric (H.activeStage t) t) y)⁻¹ ∧
      ∃ A : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) y,
        ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
          |(Q)⁻¹ * metricScalarAt (H.stageMetric (H.activeStage v) v)
              (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) -
            (1 - Q * (v - t))⁻¹| ≤ 2400 * eps      -- Q := metricScalarAt (stageMetric … t) y
```
= STEP 1 at one point (one backward extension across any number of events, one error estimate on
the single survivor flow, H17 (4)); EVENT-ENDPOINT STEP = the identification lemma (windows starting
or ending exactly at an event time are covered through `stageDomain` / initial metrics).

**SC3-c** (engine, `Surgery/Topology/HistoryStrongNeckExtension.lean`): iterate SC3-b with slices
chosen in the lower half `[u − 1/(5R_u), u − 1/(10R_u)]` off event times:
```lean
theorem exists_backwardPointTrace_scalar_le_of_hasStrongNeckAt (H : ObservedHistory.{u})
    {eps L : ℝ} (heps : eps ≤ 1 / 30000) {t a : Icc (0 : ℝ) H.horizon} (hat : a ≤ t)
    {y : (H.stageAt t).Carrier} (htop : H.time (H.activeStage t) < t)
    (hL : L ≤ Q * (3 / 4) ^ ⌈10 * Q * ((t : ℝ) - a)⌉₊)     -- Q := scalar of y at t
    (hsupply : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
      H.time (H.activeStage v) < v →
      ∀ B : BackwardPointTrace H (H.activeStage v) (H.activeStage t) (H.activeStage_mono hvt) y,
        L ≤ metricScalarAt (H.stageMetric (H.activeStage v) v) (B.point (H.activeStage v) le_rfl _) →
        H.HasStrongNeckAt eps v (B.point (H.activeStage v) le_rfl _)) :
    ∃ (b : Icc (0 : ℝ) H.horizon) (hbt : b ≤ t), (b : ℝ) = a - (10 * Q)⁻¹ ∧
      ∃ A : BackwardPointTrace H (H.activeStage b) (H.activeStage t) (H.activeStage_mono hbt) y,
        ∀ (v : Icc (0 : ℝ) H.horizon) (hbv : b ≤ v) (hvt : v ≤ t),
          metricScalarAt (H.stageMetric (H.activeStage v) v) (A.point …) ≤ 2 * Q
```
Depth gain `1/(10Q)` per call is `θ₀/(2R_max)`; the slice maximum never increases (Finding 3); the
number of internal steps is not bounded a priori (only by `10Q(t−a)+1`).

**SC3-d** (window supply in the `isTracedRegion` currency, `RetainedCoreHistory`, pinching as in
`TracedRegionBackwardStep`): for a ball `riemannianBallOf (stageMetric (activeStage t) t) p ρ` with
`Qlow ≤ R ≤ Qup` on it, `L ≤ Qlow·(3/4)^⌈10·Qup·T⌉₊`, the supply at the traces of all ball points,
`a = t − T`:
`H.toHistory.isTracedRegion t p ρ (T + (10 * Qup)⁻¹) (8 * √3 * (1 + phi 1 + phi 0) * max Qup 1)`.
Iterating SC3-d in `T` (each call adds `1/(10·Qup)`, `Qup` the slice bound which SC3-c shows does not
grow) gives every depth; this is exactly `htraced` of
`exists_bounded_ancient_pointed_flow_limit_of_spatially_canonical_before` at each `(A, T)`.

**SC3-e** (class-shaped supply, lead's hypothesis shape): `∃ eta > 0` (SC1-d's) such that the class
clause at the slice's slab + an `eps`-fine spatial neck (`eps ≤ eta`) at `p` + `qcan < R(p)` give
`HasStrongNeckAt ε₁ v p`; and SC3-d restated with this supply.

## Lead message (review H18 binds T3A-2) — deltas, recorded before proving SC3-d/SC3-e
- (a) effective step `θ₀/(2R_max)` with a fixed inner margin: SC3-c's gain per call is exactly
  `1/(10Q) = θ₀/(2Q)`; internally every next slice lies in `[u − θ₀/R_u, u − θ₀/(2R_u)]`, so the lower
  half `[θ₀/(2R), θ₀/R]` of each window is the margin (traced, bounded, not used as a slice).
- (b) UNIFORM curvature control on each finite target window, not step positivity: SC3-c proves
  `R ≤ 2·Q_top` along the whole trace down to ANY depth reached, and the slice maximum along a trace
  never increases (`R_{u'} ≤ (10/11 + 2400ε)R_u ≤ R_u`), so the gain `1/(10·Q_top)` is uniform and the
  target depth is reached after at most `⌈10·Q_top·T⌉ + 1` steps. This is the X4a conclusion obtained
  WITHOUT the far/`hRP` bootstrap: every slice point of every trace carries its own neck (the supply),
  and the neck-centre comparison is monotone backwards (cylinder `R = (1−r)⁻¹`). No `hRP` hypothesis is
  needed for the step statement; the X4a template (`WindowScalarBound.lean:260`) is not consumed.
  The price is the supply hypothesis at ALL slice points of the traces (see (c) and the caveat).
- (c) completeness, `Rm ≥ 0`, κ: transported by the existing ancient-limit headline
  (`exists_bounded_ancient_pointed_flow_limit_of_spatially_canonical_before`) from the class inputs once
  `htraced` holds; canonical-type (cap/compact) exclusion at each extended layer is the SUPPLY — it is a
  hypothesis of SC3-c/SC3-d, discharged per layer by the consumer (SC3-e is one supplier).
- (d) nothing about cylinders/lines is concluded in these files.
- CAVEAT on the lead's supply shape (fine necks from limit closeness): at depth the blow-up limit is
  close to `ℝ × N(t)` with `N(t)` a 2-dimensional Ricci flow on `S²` that is NOT known to be near-round
  before the ancient limit and T3A-3 (that is the conclusion of T4′'s contradiction argument; at time 0
  the deep horn points are, by the contradiction hypothesis, not `εc`-necks). So an `eps`-fine spatial
  neck with `eps ≤ eta(C1,C2)` (SC1-c's capture hypothesis) is NOT available at depth from ℝ×N closeness
  alone. The correct per-layer exclusion is H13's whole-neighbourhood TOPOLOGICAL capture in ℝ×N (the
  witness's cap frontier sphere would be a neck sphere isotopic to `{pt}×N`, which bounds no compact
  region of ℝ×N) — the depth analogue of SC1-b, not of SC1-c. SC3-e is delivered in the lead's shape
  as instructed, but T4′ needs an ℝ×N-capture variant of SC1-c; the engine SC3-c/SC3-d is agnostic.

## Proof status (all PROVED, no sorry)
- SC3-a `TruncatedNeckScalar.lean` — proved as stated.
- SC3-b `HistoryStrongNeckTrace.lean` — `HasStrongNeckAt`, the identification lemma (event-endpoint
  step) and the one-step lemma, proved as stated.
- SC3-c `HistoryStrongNeckExtension.lean` — engine proved as stated, plus `0 < L` (`hL0`): needed to
  get `0 < Q` at the top from the floor (with `Q ≤ 0` the floor inequality does not give `L ≤ Q`).
  The supply binder is `∀ v, a ≤ v → ∀ hvt : v ≤ t, …` (unused-name lint).
- SC3-d (same file) `RetainedCoreHistory.isTracedRegion_of_hasStrongNeckAt` — proved; `a` is built
  inside from `hTt : T ≤ t` (instead of an `a` argument); the supply is on `[t − T, t]`.
- SC3-e `HistoryStrongNeckClassSupply.lean` — `exists_currentSlab_stronglyCanonicalBefore` (the
  class clause at the slab of the ACTIVE stage: event slabs from `EventSlabsStronglyCanonical`, the
  last stage from a hypothesis `hterm` indexed by `activeStage v`, which is how the terminal slab `G`
  of T4′ enters after `extendHorizon`), `exists_tolerance_hasStrongNeckAt_of_spatialNeck` (SC1-d
  trigger ⇒ `HasStrongNeckAt`), `exists_tolerance_isTracedRegion_of_spatialNecks` (SC3-d with the
  lead's supply shape; `qcan < L`, `ε₁ ≤ 1/30000`, `eps ≤ eta(C1,C2)`).

## Deliverables (all new, uncommitted, not in the root aggregate)
| File | Lines | Declarations |
|---|---|---|
| `Perelman/CanonicalNeighborhood/TruncatedNeckScalar.lean` | 246 | `CylinderReference.metric_eq_cylinderReferenceMetric`, `ricciSharp_cylinderReferenceMetric`, `sqrt_inner_ricciSharp_cylinderReferenceMetric_le`, `TruncatedNeck.abs_scalar_center_sub_le` (+ private trace bound) |
| `Surgery/Topology/BackwardTraceConcat.lean` | 61 | `BackwardPointTrace.concat`, `concat_point_of_le`, `concat_point_of_ge` |
| `Surgery/Topology/HistoryStrongNeckTrace.lean` | 134 | `ObservedHistory.HasStrongNeckAt`, `metricScalarAt_backwardSurvivor_eq_stageMetric`, `exists_backwardPointTrace_scalar_bounds_of_hasStrongNeckAt` |
| `Surgery/Topology/HistoryStrongNeckExtension.lean` | 348 | `ObservedHistory.exists_backwardPointTrace_scalar_le_of_hasStrongNeckAt`, `RetainedCoreHistory.isTracedRegion_of_hasStrongNeckAt` (+ 5 private arithmetic lemmas) |
| `Surgery/Topology/HistoryStrongNeckClassSupply.lean` | 126 | `RetainedCoreHistory.exists_currentSlab_stronglyCanonicalBefore`, `exists_tolerance_hasStrongNeckAt_of_spatialNeck`, `exists_tolerance_isTracedRegion_of_spatialNecks` |
- Compile: each file with `LEAN_NUM_THREADS=2 lake env lean -DmaxSynthPendingDepth=3
  -Dweak.linter.mathlibStandardSet=true`, uncommitted imports through scratch modules `SC3.*`:
  zero output (no errors, warnings; long lines only in imports). `#lint` (scratch copies): only
  `docBlame` on the two defs (excluded). `#print axioms` for all 14 public declarations:
  `[propext, Classical.choice, Quot.sound]`; the `#print`/`#lint` lines lived only in scratch copies.
- New public names grep-unique (`BackwardPointTrace.concat`: a PRIVATE def of the same name and
  construction exists in `ProspectiveNeckSurvival.lean:1706` — deferred merge: replace it by the public
  one when that committed file is next touched; its public `concat_point_before/after` then become
  aliases of `concat_point_of_le/ge`). `abs_trace_le_of_sqrt_inner_bound` (private) is a copy of the
  private `abs_trace_le_of_metric_bound` of `Geometry/Neck/ScaleComparison.lean:17` — deferred merge:
  make one public (e.g. `LinearMap.abs_trace_le_of_metric_bound` in a Curvature/Metric home).
- Acceptance order: SP1 `StrongNeckRestriction → TruncatedNeck → HistoryStrongNeck`; then
  `TruncatedNeckScalar`, `BackwardTraceConcat` (committed deps only), `HistoryStrongNeckTrace`,
  `HistoryStrongNeckExtension`; SC1 `InteriorCollar → SpatialCanonicalWitnessNeckExclusion →
  TerminalHornCanonicalNeck → HistoryStrongNeckTrigger`; then `HistoryStrongNeckClassSupply`.
- No `open private`; no committed file modified.

## Deviations (with reasons)
1. Window currency: `isTracedRegion` (= `htraced` of the composed ancient-limit headline), not the
   `S n j`/`hslab`/`hneckRegular` of `TerminalScalarAncientLimit.lean:475` (Finding 1: `:475` needs a
   single-flow `FlowSequence` with a precomputed time-0 limit; histories enter the tree's limit
   machinery through traced regions; `hneckRegular` serves only `∂R ≥ 0`, unused on that route).
2. Accuracy `ε₁ ≤ 1/30000` (the cylinder-comparison scalar error at the neck centre is
   `2400·ε₁`; monotonicity backwards needs it `≤ 1/11 − …`). T4′ chooses `ε₁` (∃), so this is free.
3. Supply hypothesis instead of "strong necks everywhere" (lead message; SP2's cap-window points).
4. `hL0 : 0 < L`, `hTt : T ≤ t` as above.

## What the T4′ assembly still lacks (consumer side)
- **Per-layer supply at depth** (the only analytic input SC3-c/SC3-d take): at every slice point of
  the traces (non-event slices, `R ≥ L = qcan`), the class witness must be a NECK. SC3-e derives it from
  `eps`-fine spatial necks (SC1-c), but those are NOT available at depth before the ancient limit is
  known to be round (CAVEAT above). Missing brick: an ℝ×N whole-neighbourhood TOPOLOGICAL capture
  (depth analogue of SC1-b): approximants close on balls of radius `Aₙ → ∞` to a product `ℝ × N` with
  `N ≅ S²` ⇒ the class witness at each point is a neck (cap frontier sphere ≅ `{pt} × N` bounds no
  compact region; compact alternatives excluded by non-compactness).
- **The product structure at depth**: splitting of the limit on `[−T, 0]` (line at time 0 from the
  horn, SC1-b/T3A-1 + strong maximum principle / Hamilton splitting on the traced limit), which is what
  makes the capture above applicable layer by layer; cylinder rigidity only after the ancient limit
  (H18 (d)).
- **Uniform-in-`n` top-ball bounds** `Qlow ≤ R ≤ Qup` on normalized balls at the base time (depth 0),
  from SC2's depth-0 uniformity + closeness to `L`.
- **Sequence-level induction on depth**: iterate SC3-d (gain `1/(10·K_A)` normalized per call, `K`
  independent of the depth) to get `htraced` for all `(A, T)`, then
  `exists_bounded_ancient_pointed_flow_limit_of_spatially_canonical_before` (needs also the class's
  `qs`-witnesses, derivative bound, noncollapsing, pinching on `v < t₀ n` — class inputs).
- **Transfer lemma** `(H.extendHorizon T …).StronglyCanonicalBefore (Fin.last) G … ↔
  H.StronglyCanonicalBefore (Fin.last) G …` (same events/stages; needed to feed SC3-e's `hterm` in T4′).
- T3A-3 (line ⇒ cylinder ⇒ `εc`-neck on `L`) and the T4′ constants bookkeeping.
