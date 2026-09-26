# OPUS fill log SC1: T4′ consumer wave 1 (2026-09-26)

Worker lane SC1. Scope: the first consumer bricks of `DESIGN_STRONG_INTERFACE.md` §2 / `DESIGN_S_SUPPLY.md`
§3 (T3A) whose suppliers are committed. New files only; read-only compiles
(`LEAN_NUM_THREADS=2 lake env lean -DmaxSynthPendingDepth=3 -Dweak.linter.mathlibStandardSet=true`);
scratch under the session scratchpad `sc1/`. No git writes, no lake build, no root-aggregate edit.

## Progress

- read AGENTS.md (pc3: no header, no module docstring, zero comments), DESIGN_STRONG_INTERFACE §0–§4,
  DESIGN_S_SUPPLY §0–§3, H13 digest, DESIGN_B13 §0–§3, T1 file + log.
- SP1's predicate file has not landed (log at 00:00 only). The strong-clause corollaries (neck
  alternative ⇒ `HistoryStrongNeck`) wait for it; wave 1 takes the bricks that do not mention the
  strong predicates.
- Supplier survey (all committed):
  - T1 `TerminalCorePresentation.false_of_terminal_capSide` (`Topology/TerminalCapSideExclusion.lean`).
  - T1a already exists: `TerminalCorePresentation.monoEpsilon` (`Contract/EndNeckFields.lean:65`).
  - depth-0 cap capture in `L`: `TerminalLimitMetric.eventually_spatial_cap_spherical_barrier`
    (`Topology/TerminalSpatialCanonicalAlternatives.lean:1149`): cap witnesses along `τₙ → s⁻` give a
    `CompactDomain K` of `L` (connected, regular closed) containing `x`, frontier = central sphere of a
    `δ`-neck of `L`, scalar in `(R(x)/2C2, 2C2·R(x))`, with an inner collar.
  - compact-alternative exclusion in `L`: `TerminalLimitMetric.eventually_spatial_neck_or_cap` (`:582`).
  - recentering `SpatialNeck.exists_at_coordinate` (`Geometry/Neck/SpatialFixedRecentering.lean:58`),
    normalization `SpatialNeck.exists_normalizedNeck_of_two_mul_le` (`SpatialNormalization.lean:146`).
  - horn membership: `exists_hornHalfRange_superset_of_isPreconnected`, `hornHalfRange_unique`
    (`Topology/ChartTailHornBridge.lean:270,277`).

## Brick statements (recorded BEFORE proving; elaborated with `sorry`, only `declaration uses sorry`)

**SC1-a** (topology, `Topology/Connected/InteriorCollar.lean`, namespace `DifferentialGeometry.Topology`):
```lean
theorem isPreconnected_interior_of_frontier_nhds {X : Type*} [TopologicalSpace X] {K C : Set X}
    (hK : IsPreconnected K) (hKc : IsClosed K) (hreg : closure (interior K) = K)
    (hC : IsPreconnected C) (hCK : C ⊆ interior K)
    (hloc : ∀ p ∈ frontier K, ∃ U : Set X, IsOpen U ∧ p ∈ U ∧ U ∩ interior K ⊆ C) :
    IsPreconnected (interior K)
```
Needed because T1 takes `IsConnected W` and the cap capture gives a connected regular-closed `K`;
`C` is the inner half of the frontier collar. PROVED (48 lines, clean compile).

**SC1-b = T3A-1 at depth 0** (`Surgery/Topology/TerminalHornCanonicalNeck.lean`, namespace
`…Surgery.Topology.TerminalCorePresentation`): at a horn point `x` of `L` with
`R_L(x) > 4·C2·Λ/r²`, eventually as `t → s⁻` every spatial canonical witness at `(x, t)` whose cap
tube carries `eps`-neck charts is a NECK (the cap alternative by the horn topology T1, the compact
alternatives by the core base point of the same component):
```lean
theorem eventually_neck_alternative_of_mem_hornHalfRange :
    ∃ eta : ℝ, 0 < eta ∧
    ∀ {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ), ε ≤ eta →
    ∀ (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c)
      (x : D.slab.terminalRegularOpen), x ∈ P.hornHalfRange c e →
    ∀ {epsCan eps C1 C2 : ℝ}, 0 < eps → eps ≤ eta →
      4 * C2 * (Λ * (P.coreRadius ^ 2)⁻¹) < metricScalarAt D.terminal.metric x →
      ∀ᶠ t in 𝓝[<] D.endTime,
        ∀ W : SpatialCanonicalWitness (D.slab.flow.base.metric t) epsCan C1 C2 x.val,
          W.capTubeHasNeckChart eps →
            ∃ neck : SpatialLocalNeck (D.slab.flow.base.metric t) epsCan x.val W.domain.carrier,
              W.alternative = SpatialCanonicalAlternative.neck neck
```
- `eta` is absolute (from T1's tolerance and the recentering loss `13000·δ`).
- No `c ∈ P.component` binder: it follows from `e : P.hornIndex c` (`hornIndex_empty`).
- Hypotheses are only presentation data + the witness's own cap-tube chart clause; no class, no `p₀`.
- Route: by contradiction; `eventually_spatial_neck_or_cap` with the horn base point
  (`R ≤ Λ/r²`, same component) kills positive/round; a frequently-cap sequence feeds
  `eventually_spatial_cap_spherical_barrier` (`δ := α/13000`); the frontier neck is recentred to level
  `1/2` (`exists_at_coordinate`) and normalized (`exists_normalizedNeck_of_two_mul_le` at `ε := eta_T1`);
  `K ⊆ hornHalfRange c e` via connectedness + `R > 2Λ/r²` on `K` (misses `frontier core`); then T1 on
  `P.monoEpsilon` with `W := interior K`, connected by SC1-a with the inner collar.
- SC1-b PROVED: `Surgery/Topology/TerminalHornCanonicalNeck.lean` (268 lines), clean compile
  (scratch-module import of SC1-a), axioms `[propext, Classical.choice, Quot.sound]`.

**SC1-c = whole-neighbourhood capture at depth ≥ 1** (`Perelman/CanonicalNeighborhood/
SpatialCanonicalWitnessNeckExclusion.lean`, namespace `…CanonicalNeighborhood.FiniteHorn`), recorded
before proving, elaborated with `sorry` first:
```lean
theorem exists_tolerance_alternative_eq_neck_of_spatialNeck (C1 C2 : ℝ) :
    ∃ eta : ℝ, 0 < eta ∧
    ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
      [T2Space M] [SigmaCompactSpace M] (g : SmoothRiemannianMetric I3 M)
      (epsc epsb eps : ℝ) (y : M) (W : SpatialCanonicalWitness g epsc C1 C2 y),
      W.capTubeHasNeckChart epsb → epsb ≤ 1 / 1000 → eps ≤ eta →
      Nonempty (SpatialNeck g eps y) →
      ∃ neck : SpatialLocalNeck g epsc y W.domain.carrier,
        W.alternative = SpatialCanonicalAlternative.neck neck
```
- H13 conformity: `eta` depends on `(C1, C2)`, i.e. the neck at `y` must be long compared with the
  witness diameter `4·C1/√R(y)` — this is the whole-neighbourhood capture, not "a finite ε₁-neck
  excludes caps". In the ℝ×N limit the approximants carry `eps`-necks with `eps → 0` at every point of
  a large ball, so the hypothesis is met at every fixed depth.
- cap alternative: the cap core is compact with nonempty interior, its frontier is the `epsb`-neck
  sphere of `capTubeHasNeckChart`, the domain has scaled diameter `≤ 4·C1` and `R ≤ C2·R(y)`, the tube
  centre has `R ≥ R(y)/C2`; `exists_neck_cap_separation_tolerance_of_subset`
  (`Geometry/Neck/CapSeparation.lean:157`) makes the domain miss the unit slab of the neck at `y`,
  but `y` lies in it.
- positive/round: the domain would be the whole component, which contains the neck point at level
  `4·C1 + 1`, outside `ball(y, 2·radius)` by `SpatialNeck.ball_subset_image_slab` + injectivity.
- PROVED (146 lines), clean compile, axioms `[propext, Classical.choice, Quot.sound]`.
  No hypothesis on `C1 C2` (the witness forces `1 ≤ C1`, `1 ≤ C2`; `eta` uses `max`).

## Lead message (θ₀ = 1/4 windows) — delta
- SC1-a/b/c do not mention `HistoryStrongNeck`; their statements and proofs are unchanged by the
  `θ₀·R⁻¹` redefinition. The only θ₀-sensitive consumer statements are the trigger corollaries below
  (they only pass `HistoryStrongNeck` through, so their proofs are θ₀-agnostic) and the later T3A-2
  extension step (depth `θ₀/R_max` per step, cylinder comparison on `[−θ₀, 0]`) — not in wave 1.
- SP1's `Surgery/Topology/HistoryStrongNeck.lean` exists (R⁻¹ form); compiled against it via scratch
  modules, to be re-checked when the θ₀ revision lands.

**SC1-d = strong-neck triggers** (`Surgery/Topology/HistoryStrongNeckTrigger.lean`, namespace
`…Surgery.Topology.RetainedCoreHistory`), recorded before proving, elaborated with `sorry` first
against SP1's `HistoryStrongNeck.lean` (scratch-module import):
```lean
theorem exists_tolerance_historyStrongNeck_of_spatialNeck (C1 C2 : ℝ) :
    ∃ eta : ℝ, 0 < eta ∧
    ∀ {P₀ : OrientedThreeStage.{u}} (H : RetainedCoreHistory P₀) (k : Fin (H.eventCount + 1))
      {s : ℝ} (G : (H.stage k).IncomingSlab (H.time k) s) {ε ε₁ eps : ℝ}
      {y : (H.stage k).Carrier} {t : ℝ},
      ε ≤ 1 / 1000 → H.StronglyCanonicalAt k G ε ε₁ C1 C2 y t → eps ≤ eta →
      Nonempty (SpatialNeck (G.flow.base.metric t) eps y) →
      H.toHistory.HistoryStrongNeck k G ε₁ y t

theorem eventually_historyStrongNeck_of_mem_hornHalfRange :
    ∃ eta : ℝ, 0 < eta ∧
    ∀ {P₀ : OrientedThreeStage.{u}} (H : RetainedCoreHistory P₀) (k : Fin (H.eventCount + 1))
      {s : ℝ} (G : (H.stage k).IncomingSlab (H.time k) s) (L : G.TerminalLimitMetric)
      (hsing : G.SingularEndpoint) (parameters : CutoffParameters) {εP Λ : ℝ}
      (P : TerminalCorePresentation { stage := H.stage k, startTime := H.time k, endTime := s,
          startTime_nonneg := H.toHistory.time_nonneg k, startTime_lt_endTime := G.lt, slab := G,
          terminal := L, singular := hsing, parameters := parameters } εP Λ), εP ≤ eta →
    ∀ (c : ConnectedComponents G.terminalRegularOpen) (e : P.hornIndex c)
      (x : G.terminalRegularOpen), x ∈ P.hornHalfRange c e →
    ∀ {ε ε₁ C1 C2 qcan : ℝ}, 0 < ε → ε ≤ eta →
      4 * C2 * (Λ * (P.coreRadius ^ 2)⁻¹) < metricScalarAt L.metric x →
      qcan < metricScalarAt L.metric x →
      H.StronglyCanonicalBefore k G ε ε₁ C1 C2 qcan s →
      ∀ᶠ t in 𝓝[<] s, H.toHistory.HistoryStrongNeck k G ε₁ x.val t
```
- The first is the depth-≥1 trigger (SC1-c + the class clause); the second is T3A-1's output at
  depth 0 (SC1-b + the class clause at `R > qcan`). Both only pass `HistoryStrongNeck` through, so
  they are θ₀-agnostic. PROVED (67 lines), clean compile, axioms `[propext, Classical.choice, Quot.sound]`.

## Deliverables (all new, uncommitted, not in the root aggregate)
| File | Lines | Declarations | Depends on uncommitted |
|---|---|---|---|
| `Topology/Connected/InteriorCollar.lean` | 49 | `DifferentialGeometry.Topology.isPreconnected_interior_of_frontier_nhds` | — |
| `Surgery/Topology/TerminalHornCanonicalNeck.lean` | 268 | `TerminalCorePresentation.eventually_neck_alternative_of_mem_hornHalfRange` | InteriorCollar |
| `Perelman/CanonicalNeighborhood/SpatialCanonicalWitnessNeckExclusion.lean` | 146 | `FiniteHorn.exists_tolerance_alternative_eq_neck_of_spatialNeck` | — |
| `Surgery/Topology/HistoryStrongNeckTrigger.lean` | 67 | `RetainedCoreHistory.exists_tolerance_historyStrongNeck_of_spatialNeck`, `RetainedCoreHistory.eventually_historyStrongNeck_of_mem_hornHalfRange` | SP1: `HistoryStrongNeck` (→ `StrongNeckRestriction`); TerminalHornCanonicalNeck; NeckExclusion |

- Compile: each file with `LEAN_NUM_THREADS=2 lake env lean -DmaxSynthPendingDepth=3
  -Dweak.linter.mathlibStandardSet=true`, uncommitted imports through scratch modules `SC1.*`
  (`--root` = scratchpad): zero output (no errors, warnings, lints). `#print axioms` for all five:
  `[propext, Classical.choice, Quot.sound]`; the `#print` lines lived only in scratch copies (deleted).
- Acceptance order: InteriorCollar, SpatialCanonicalWitnessNeckExclusion (committed deps only),
  TerminalHornCanonicalNeck, then SP1's StrongNeckRestriction → HistoryStrongNeck, then
  HistoryStrongNeckTrigger. New names grep-unique. No `open private`, no copies, no deferred merges.
- Deviations: none from a design text (§2 gives rows only; statements written here). T1a was not
  needed as a new brick: `TerminalCorePresentation.monoEpsilon` already exists.

## What the T4′ assembly still lacks (consumer side)
- Uniformity at depth 0: SC1-b/SC1-d are pointwise in `x`; the blow-up needs strong necks at all
  points of a rescaled ball around `xₙ` for one `τₙ`. Either a moving-centre version of
  `eventually_spatial_cap_spherical_barrier` (sequences `xₙ → x∞` inside the horn), or run the
  argument at depth 0 via SC1-d's first form (fine necks of `L` at every ball point transferred to
  `G(τ)` by `eventually_spatialNeck_of_incoming_spatialNecks`'s converse) — the latter needs a
  "necks of `L` ⇒ necks of `G(τ)` uniformly on compacts" lemma (not in the tree).
- T3A-2 proper: the backward extension step on the θ₀ windows (depth `θ₀/R_max` per step, curvature
  comparability on `[−θ₀, 0]` from the neck comparison), event-endpoint handling through
  `backwardSurvivorSlabMetric`, the uniform subsequence, and feeding
  `TerminalScalarAncientLimit.lean:475`'s window hypotheses. At each depth, SC1-c/SC1-d(1) is the
  cap/compact exclusion + trigger, given `eps`-necks at the traced points (from closeness to the
  ℝ×N limit on large balls, `eps → 0`).
- T3A-3 (line ⇒ cylinder ⇒ εc-neck on `L`) and the T4′ constant bookkeeping
  (`eta := min` of SC1-b's and T1's; `εcone ≤ 1/1000`).
- Waiting on SP1's θ₀ revision of `HistoryStrongNeck`: SC1-d must be re-compiled against it (no
  statement change expected).
