# Design: splitting the horn-cutoff factory for `UniformDebitSurgeryStepStrong`

Read-only design, 2026-09-26, worktree `D:\differential-geometry-pc3` (branch `codex/pc-target-c-psf`,
18c uncommitted). Paths are relative to `DifferentialGeometry/Geometry/Flow/RicciFlow/Surgery/`.
No Lean was compiled for this report. Every line number below was checked against the current worktree.

## 0. Verdict, failures first

1. **GAP (design-critical): the one-slab backward window is not available on short terminal slabs.**
   The window that H (`exists_strongNeck_threshold_of_minimizing_arms`) and 18c
   (`IncomingSlab.exists_strongNeck_threshold_of_localNeckChain`) need is
   `a ≤ t − θ/R(x,t)`. At the cut point `R ≈ Q` (the uniform cut scale), so the window needs
   `Q·(s − a) ≥ θ` (with some slack), where `θ = θ(δcut, κ, ρ, Φ)` is an output of H.
   The only lower bound on the length of a singular slab follows from the post-event bound
   `R ≤ Kreset·Q` (`Kreset` at HornCutoffRecord:1281; output clause `∀ q, R ≤ max coreBound (Kreset·Q)` in :1161) and `|∂ₜR| ≤ Ctime R²`. That bound is
   `s − a ≥ 1/(Ctime·Kreset·Q)`. It is scale-invariant, so it gives `Q(s−a) ≥ 1/(Ctime·Kreset)`,
   which says nothing about `θ`. Cutting deeper (at `MQ`) moves the post-event bound to `Kreset·MQ`,
   so the ratio does not change. A step-dependent `M` gives no uniform debit `v`.
   So a coarse+fine split built only on the one-slab window proves S only for **long terminal
   slabs** `2θ ≤ Q·(s − a)`, and S cannot assume that. What replaces it on short slabs is the
   **history window**: the backward parabolic region of `x` is traced through the events in
   `[s − θ/Q, s]` by `RegularCrossing` (the same object `IncomingBackwardNeck.crossing` uses,
   `Topology/GeometricCutoff.lean:69`). It is unscathed because a point with arms of normalized
   length `D` on both sides cannot lie within normalized distance `≈ D` of a cap glued in the window.
   H is then rerun on the survivor flow. That brick (B13) belongs with the Crossing (C3c)
   infrastructure: common survivor flow, buffered survival dichotomy, compactness through events.
   Optional help: if the class also recorded the output bound `R ≤ Kreset·Q` for each event, the
   window would cross at most `N₀ = ⌈2θ·Ctime·Kreset⌉ + 1` events. Today the class
   (`hasCanonicalCutoffRecords`) does not record it.

2. **FALSE as a supply claim: the coarse decomposition cannot supply 18c's local-chain hypothesis
   at a fixed `ε̄`.** 18c requires factor-4 scalar comparability along `c 0 … c (2m)` with step
   `100` and `D ≤ 40m`, where `D = D(δcut)` comes from H.
   Configuration: a spatial `ε̄`-horn whose scalar grows like `R(u) = R₀·e^{cε̄u}` in normalized
   arclength `u`. A warped cylinder with slowly varying radius is an `ε̄`-neck at every point and
   satisfies the spatial CN clause. Comparability then fails once `200·m·c·ε̄ > log 4`, i.e. for
   `m > log 4/(200 c ε̄)`. Forcing comparability therefore forces `ε̄ ≲ 1/m(δcut)`, which is the F1
   circularity again. Generic "bounded curvature at bounded distance" gives only
   `R ≤ C(A)R(x)`, not a factor 4.
   **Design consequence:** do not route the fine necks through 18c. Feed H directly with two
   minimizing arms. Build them from (i) a compactly contained normalized ball of radius `3D` around
   the cut point (KL 71.1, brick B9) and (ii) separation by the central sphere of the coarse neck
   at `x` (a single separating slice, `metricDistance_ge_of_separating_slices`,
   `NeckChainAxialArms.lean:131`). 18c stays valid; it is simply not the supply route here.

3. **Finding (not a failure): after the split, the factory consumes no age-restricted strong
   witnesses.** All five sites (§1) read only time-slice data or `time_derivative`. The fine necks
   come from H using κ and pinching, not from witnesses. S's `CanonicalBefore …` hypotheses (on the
   history and on `G`), `Cgrad`, `a₀` and `NoncollapsedBefore` become idle. `a₀`, `Φ` and the time
   floor `a` come from `P₀ g₀` (PreparedHistoryCutoff:564–566).

4. **Binder traps, all mechanical:**
   - `fixed` and `recenterConstant` are universal (`FiniteMetricEventDebit:231` takes no inputs),
     but the factory states them after `Dtrace Dbig r tol Ctime` (PoincareHornCutoffRecord:461).
     S needs `∃ Λ` before `Ctime` and `Dcap`, so the statement must be reordered.
   - `p₀.modelRadius = Dbig` is an equality. Choose `Dbig := max Dcap (Dtrace+1)` after `Dcap`.
   - The discarded classification needs record precision `≤` the witness accuracy
     (`DiscardedComponentClassification:111`, `∀ j, G.delta j ≤ eps`). Take `ηrecord ≤ ε̄`.

## 1. The five witness-consumption sites

| # | Site (entry → leaves) | Accuracy demanded | Age of the point used | Witness fields read | New input |
|---|---|---|---|---|---|
| S1 | Scalar sublevel, capture, normalization: `Topology/TerminalScalarSublevel:25`, `TerminalCanonicalCapture:108,116`, `TerminalCapCapture:182,304`, `TerminalCapNormalization:69`, `TerminalNeckNormalization:518`, `TerminalComponentClassification:94`, `DiscardedCanonicalCoverage:74,149` | irrelevant | every `(y,t)`, `t∈(a,s)`, `R>q`: unbounded below | `time_derivative`; `scalar_bounds` and `domain` at `TerminalCanonicalCapture:108–109` | derivative clause (entry 17) plus the spatial witness's `scalar_bounds` and `domain` |
| S2 | Terminal neck/cap alternative at high points: `TerminalSphericalRegionExterior:69,91` → `TerminalCapCore:287` → `TerminalCanonicalAlternatives:33–53` | `δreg/4` | `x` in a noncompact terminal component, `R_L(x) > B`, `τ → s`: age `≈ R_L(x)(s−a)` | `alternative` (neck map at `τ` only, via `exists_neckBuffer_pullback_bound`, `TerminalNeckNormalization:74–137`; cap core); `scalar_bounds` to exclude whole-component branches (`TerminalCanonicalAlternatives:50–52`) | `SpatiallyCanonicalBefore ε̄` |
| S3 | Spherical region and barrier: `Contract/TerminalCutoffScale:111` → `TerminalSphericalRegionExterior:162` → `TerminalSphericalRegion:23`, `TerminalSphericalBarrier:369,449`, `TerminalCapCore:146` | `δreg/4`, with `δreg ≤ min η₁ η₂ (εP/26000) (1/156000)` (`Contract/TerminalCorePresentationExistence:466–474`) | levels `C·qcan`, `(δρ)⁻²`, `2C2·A` at `τ → s` | `alternative`, `capTubeHasNeckChart`, `scalar_bounds`, `domain` | spatial |
| S4 | Discarded classification: `PoincareHornCutoffRecord:643` (`htop`, `epsTop = min eta (1/22)`) → `DiscardedComponentClassification:22,106` → `StoppedCapCuttingSide:100,282,321`, `TerminalComponentClassification:72` → `Perelman/CanonicalNeighborhood/CompactCanonicalClassification:32` | `epsTop`; record `δ ≤ eps` | points of discarded components above the protected level, **including young points** (review 3 F5: round `S³`) | full `alternative`, including `positive`/`round` (whole component), cap core, `domain`, `scalar_bounds` | spatial. The compact classification already reduces to `exists_compact_spatial_poincareStandard_tolerance` |
| S5 | Cut-neck precision (the only fine site): `horn_spatial_neck := (data c).spatial_neck` (`TerminalCorePresentationExistence:405`), read at the first-hit point in `HornFirstScalarLevel:68` and in the proof of `:233`, consumed by `Contract/BaseHornMetricEvent:1555` and `HornCutoffRecord:1325` under `ε ≤ ε₀`, where `ε₀ = min εfactory (min (ηstar/2) ((mstar+1)⁻¹))` (`PreparedHistoryCutoff:383`) | today `εcan ≤ δ/208000` | the cut point, `R = Q` at time `s`: age `Q(s−a)` | `horn_spatial_neck` (a `NormalizedNeck`, precision `≤ ε`, order `≥ ⌊ε⁻¹⌋₊+1`) | **not witnesses**: the fine brick B12/B13, which needs the backward window |

Caveats:
- The grouping into five sites is mine. The review called the count unverified.
- Spatial-only reading is line-checked for `TerminalNeckNormalization:74–137`,
  `TerminalCanonicalAlternatives:18–53` and `CompactCanonicalClassification`. The other S2/S3 leaves
  are grep-checked only: no `window`/backward field access.
- The only site that needs the backward window is S5, and it gets that window from H, not from
  witnesses.

## 2. (a) Coarse terminal decomposition at a fixed `ε̄`

Universal constants, all fixed before `B`:
- `εP := min {eta of HornFirstScalarLevel:233, :425; HornNeckEssentiality:35, :125, :280;
  BaseHornMetricEvent:1555; exists_precision_order_compatible's floor; 1/12;
  neckModelTolerance (1/6000)}`.
  The last entry absorbs the transport loss: terminal `εP` neck → slice neck at
  `2·(1/6000) = 1/3000` via `SpatialNeck.exists_transport_of_local_comparisons`.
- `δreg := min η₁ (min η₂ (min (εP/26000) (1/156000)))`.
- `ε̄ := min (δreg/4) (min etaDisc (1/22))`.

S sets `ε := ε̄`. Hence `ε̄ < 1/11`, and `ε̄` depends on nothing.

**A1** `OneStepIncoming.exists_neckRadius_terminalCorePresentation_of_spatial_neighborhoods`
(replaces `TerminalCorePresentationExistence:431/654` for the factory):
```
∃ εP ε̄ : ℝ, 0 < εP ∧ 0 < ε̄ ∧ ε̄ < 1/11 ∧ 104000 * ε̄ ≤ εP ∧
∀ C1 C2 : ℝ, 1 ≤ C2 → ∃ C Λ : ℝ, 1 ≤ C ∧ 1 ≤ Λ ∧
∀ (q : ℝ) (Ctime : ℝ≥0), 0 < q → ∀ D : OneStepIncoming.{u},
  (∀ y, ∀ t ∈ Ioo D.startTime D.endTime, q < D.slab.flow.scalar t y →
     |derivWithin (fun v => D.slab.flow.scalar v y) (Iic t) t| ≤ Ctime * D.slab.flow.scalar t y ^ 2) →
  D.slab.SpatiallyCanonicalBefore ε̄ C1 C2 q D.endTime →
  ∀ q', q ≤ q' → ∃ ρ hρ, … (conclusions of :431 verbatim, P : TerminalCorePresentation (D.withNeckRadius ρ hρ) εP Λ)
```
It is proved from spatial copies of S1–S3 (bricks B2, B3).

**A2** `GeometricCutoffRecord.exists_poincareStandardDiscarded_tolerance_of_spatial_neighborhoods`
(replaces `DiscardedComponentClassification:106`): the same statement, with the hypothesis
`∀ x t … ∃ W : CanonicalWitness … eps …` replaced by the derivative clause above `q` on
`(H.event i).incoming` together with
`(H.event i).incoming.SpatiallyCanonicalBefore eps C1 C2 q (H.time i.succ)`.

Which sites take spatial witnesses and which need the backward window: S1–S4 read only slice
data, so all four take spatial witnesses. None of them needs the window.

## 3. (b) Fine cutting necks at `εcut`

Interface between the bricks. It is not a headline hypothesis; the fine brick proves it.
```
def TerminalCorePresentation.FineCutNecks (P : TerminalCorePresentation D ε Λ) (εc Qc : ℝ) : Prop :=
  ∀ c (e : P.hornIndex c) (x : D.slab.terminalRegularOpen),
    x ∈ interior (range fun p : HalfNeckCylinder => P.horn c e p.1) →
    Qc ≤ metricScalarAt D.terminal.metric x →
    ∃ (δx : ℝ) (kx : ℕ) (N : NormalizedNeck D.terminal.metric δx kx),
      N.center = x ∧ δx ≤ εc ∧ ⌊εc⁻¹⌋₊ + 1 ≤ kx
```

**B12** (long terminal slab) `OneStepIncoming.exists_fineCutNecks_threshold`:
```
∀ {εc} (0 < εc) (εc < 1/2) {κ} (0 < κ) {ρ} (0 < ρ) {Φ} (AdmissiblePinchingFunction Φ)
  (C1 C2 : ℝ) (1 ≤ C2) (Ctime : ℝ≥0),
∃ K θ : ℝ, 1 ≤ K ∧ 0 < θ ∧
∀ (D : OneStepIncoming.{u}) {Λ} (P : TerminalCorePresentation D εP Λ) (q Qc : ℝ), 0 < q →
  (derivative clause above q on D.slab) →
  PhiAlmostNonnegative D.slab.flow (Ico D.startTime D.endTime) Φ →
  D.slab.SpatiallyCanonicalBefore ε̄ C1 C2 q D.endTime →
  (∀ τ (B : FlowMetricBall D.slab.flow τ), D.endTime − θ/Qc ≤ τ → B.radius ≤ ρ →
      B.IsParabolicallyRmControlled → B.IsKappaNoncollapsed κ) →
  K * max (Λ * (P.coreRadius^2)⁻¹) (max q 1) ≤ Qc →
  2 * θ ≤ Qc * (D.endTime − D.startTime) →          -- long slab; B13 removes it
  P.FineCutNecks εc Qc
```

**Depth (KL 71.1).** Take `A := 3·D(εs)`, where `D` is H's arm length at `εs := εc/2` with angle
`π/2`. `K` is chosen so that `R_L(x) ≥ K·Λ·r⁻²` forces the following for every horn point `x`:
- The normalized ball `B_L(x, A·R_L(x)^{-1/2})` is compactly contained in `interior (hornRange c e)`.
- On that ball, `R_L ≤ Cb(A)·R_L(x)`.
- Distance to the protected boundary: `√R_L(x)·dist_L(x, P.core c) ≥ A`. Toward the base this is
  mechanical: along `εP`-necks `log R` drifts by at most `C εP` per normalized unit, so
  `K ≥ e^{C εP A}` suffices.

Toward the singular end the bound needs the escape-radius contradiction (B9).

**Window.** For `τ → s`, `R(x,τ) → R_L(x) ≥ Qc`, so `a ≤ τ − θ/R(x,τ)` holds once
`2θ ≤ Qc(s−a)`. On a short slab this fails; see §0.1.

**Accuracy chain.**
1. The coarse neck at `x` has accuracy `εP`.
2. The spatial neck at `x` has accuracy `εP`; for `τ` near `s` it transfers to a slice neck in
   `g(τ)` at `1/3000`.
3. H gives `StrongNeck G.flow εs x τ` for all `τ` near `s`.
4. `TerminalLimitMetric.eventually_normalizedNeck_of_strongNecks_of_scalar_control`
   (`TerminalNeckNormalization:434`), with `δ := εc`, `eps := εs`, `k := ⌊εc⁻¹⌋₊+1 ≤ ⌈εs⁻¹⌉₊`,
   gives `NormalizedNeck L.metric εc (⌊εc⁻¹⌋₊+1)` at `x`.

**Chain question from the brief.** The brief described the chain as `c 0 … c (2m)`, step `100`,
comparability, separation and `D ≤ 40m`. None of that is needed under this design: the arms come
from the ball and a single separating slice.

- If 18c is used anyway, the hypothesis it needs at the cut point is exactly its statement
  (`LocalNeckChainAxialArms:143`), with `nk : SpatialNeck (G.flow.base.metric t) 3000⁻¹`. That
  hypothesis is supplied only after B9 has shown near-cylindricity over normalized length `2D`,
  which is circular (§0.2).
- `a ≤ t − θ/R` is **not** available on short slabs.
- The replacement is B13 (history window). Its statement is H with the hypotheses `a ≤ t − θ/R`,
  `PhiAlmostNonnegative G.flow (Icc …)` and the κ clause replaced by:
  - a history `H.appendEvent …`;
  - `RegularCrossing` of the region `B(x,t,A R^{-1/2}) × [t − θ/R, t]` through every event it
    meets, shaped like `IncomingBackwardNeck.stageChart/crossing`;
  - pinching on every slab it meets;
  - `NoncollapsedBefore` and `TerminalNoncollapsedBefore` (via
    `HistoryNoncollapsingToSlab.lean:60,95`).

  It also needs a separate unscathedness lemma: a point with two `D`-arms is regularly traced
  (cap-window exclusion).

## 4. The restated chain (option C: thread `FineCutNecks`; everything else unchanged)

The only change is at the first-hit neck. Every tolerance lemma downstream accepts any neck with
`δ_N ≤ ε` and `⌈ε⁻¹⌉₊ ≤ k`. A fine neck satisfies both, because `εc ≤ ε` and
`⌈ε⁻¹⌉₊ ≤ ⌊ε⁻¹⌋₊+1 ≤ ⌊εc⁻¹⌋₊+1`. So the coarse `P` keeps `ε = εP`, and only the precision of the
chosen neck becomes `εc`.

- **R1** `exists_horn_first_scalar_level_inner_scalar_bound_tolerance_of_fineCutNecks`
  (copy of `HornFirstScalarLevel:233`, then `:425`). After `ε ≤ eta` it adds
  `∀ {εc Qc}, 0 < εc → εc ≤ ε → P.FineCutNecks εc Qc →` and `Qc ≤ Q →`. The conclusion reads
  `δ ≤ εc ∧ ⌊εc⁻¹⌋₊ + 1 ≤ k`. The neck at the first-hit point comes from the supplier (`R = Q ≥ Qc`);
  the `:315` use of `horn_spatial_neck` at other points stays coarse.
- **R2** Copies of `BaseHornMetricEvent:1220 → :1380 → :1463 → :1555` (private; use
  `open private`). The hypotheses `2*ε ≤ δ`, `δ⁻¹+2 < (2ε)⁻¹` and `m+6 ≤ ⌊ε⁻¹⌋₊+1` become the same
  statements in `εc`, plus `P.FineCutNecks εc Qc` and `Qc ≤ Q`. The conclusion becomes
  `δOriginal j ≤ 2*εc ∧ ⌊εc⁻¹⌋₊+1 ≤ kOriginal j`.
- **R3** Copies of `HornCutoffRecord:1161 → :2329 → :3090`. The hypothesis `ε ≤ ε₀` splits into
  `ε ≤ εcoarse` (universal) and `∀ εc Qc, 0 < εc → εc ≤ min ε ε₀ → P.FineCutNecks εc Qc → … Qc ≤ Q →`.
  The body from `:1276` on is unchanged except that `hcompat` is applied to `εc`.
- **R4** Copy of `PreparedHistoryCutoff:237`, switched to `exists_threshold_uniform_selected_neck_append_backward`
  (`ProspectiveNeckSurvivalVariableThreshold:1708`):
  ```
  ∀ Dcap … m accuracy ηrecord (a : ℝ) phi, ∃ δ εcut Λsurv, 0<δ ∧ δ<1 ∧ δ ≤ ηrecord ∧ 0<εcut ∧ 0<Λsurv ∧
  ∀ q0 : ℝ, 0 < q0 → ∀ H … (unchanged) …,
    ∀ {ε Λ} (P : TerminalCorePresentation D ε Λ), ε ≤ εcoarse →
    ∀ εc Qc, 0 < εc → εc ≤ min ε εcut → P.FineCutNecks εc Qc →
    ∀ Q, 2*Λ*(P.coreRadius^2)⁻¹ < Q → nominal < Q → Λsurv * max q0 1 ≤ Q → Qc ≤ Q → …
  ```
  Here `εcut := min εfactory (min (ηstar/2) ((mstar+1)⁻¹))`, the old `ε₀`. **`q₀` is deferred at
  exactly this point**: `ηstar`, `mstar` and `Λsurv` are chosen before `∀ q0`, and `q0 := qcan`
  enters only through `Λsurv * max qcan 1 ≤ Q`.
- **R5** The new factory **F\*** replaces `PreparedHistoryCutoff:633` and
  `PoincareHornCutoffRecord:461`:
  ```
  theorem exists_horn_cutoff_record_with_uniform_volume_debit_of_spatial_neighborhoods
      (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    ∃ (fixed : StaticCapScaffold) (recenterConstant : ℝ), 4 ≤ recenterConstant ∧
    ∃ ε̄ : ℝ, 0 < ε̄ ∧ ε̄ < 1 / 11 ∧
    ∀ (Dtrace Dbig r tol : ℝ) (Ctime : ℝ≥0), Dtrace + 1 ≤ Dbig → 0 < tol → tol ≤ 1/1000 →
      transitionEnd + tol⁻¹ + 1 < r → 64 * (r + tol⁻¹) < Dtrace →
    ∃ εold δold : ℝ, 0 < εold ∧ 0 < δold ∧
    ∀ (m : ℕ) (accuracy ηrecord : ℝ), 0 < accuracy → 0 < ηrecord →
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ δ ≤ ηrecord ∧
    ∀ (C1 C2 κ : ℝ), 1 ≤ C2 → 0 < κ →
    ∃ C Λ : ℝ, 1 ≤ C ∧ 1 ≤ Λ ∧
    ∀ qcan originalCoreFloor protectedFloor : ℝ, 0 < qcan → 0 < originalCoreFloor → 0 < protectedFloor →
    ∃ Q v : ℝ, 0 < Q ∧ 0 < v ∧ v = Q ^ (-3/2 : ℝ) ∧
    ∀ p₀, p₀.modelRadius = Dbig → ⌈tol⁻¹⌉₊ + 2 ≤ p₀.modelOrder → p₀.modelAccuracy ≤ εold →
    ∀ H initial (hend : H.time last = H.horizon) ρold, H.hasCanonicalCutoffRecords p₀ δold ρold →
    ∀ s G L hsing stepParameters (hG : G.flow.base.metric (H.time last) = H.initialMetric last),
    let D := …;
    (history derivative clause above qcan) → (G derivative clause above qcan) →
    originalCoreFloor ≤ D.parameters.delta s * D.parameters.neckRadius s →
    protectedFloor ≤ D.parameters.protectedRadius s →
    G.SpatiallyCanonicalBefore ε̄ C1 C2 qcan s →
    (∀ t₀ ∈ Ioo (H.time last) s, H.TerminalNoncollapsedBefore hend G hG κ ε̄ t₀) →
    ∃ … (conclusions of PoincareHornCutoffRecord:461 verbatim, with `ηrecord ≤ δold` in the closure clause)
  ```
  Inside, `Q := max {Λsurv·max qcan 1, K·Λ·(radius floor)⁻², coreBound, neckBound,
  C2²·(radius floor)⁻²} + 1`. `K` and `θ` come from B12 applied at
  `(εcut/2, κ, ρ := ε̄, Φ(P₀ g₀), C1, C2, Ctime)`, and `Qc := Q`.
  Until B13 exists, F\* carries the extra hypothesis `2θ ≤ Q·(s − H.time last)`, i.e. `θ` is
  exported together with `Q`. That is the honest intermediate state, and it is **not** S.

**Survive unchanged:**
- `FiniteMetricEventDebit:231`, `exists_precision_order_compatible`, and all
  `HornNeckEssentiality`/`HornReparametrization`/`HornParameterRescaling` lemmas.
- The cut-cap construction `HornCutoffRecord:1276–1494`.
- `TerminalComponentEnds:15` (spatial).
- `ProspectiveNeckSurvivalVariableThreshold:1708`.
- `hasCanonicalCutoffRecords_of_appendEvent_eq` (`PoincareHornCutoffRecord:203`, private) and
  `…_retainedEvent_heq` (`:18`), via `open private`.
- `TerminalNeckNormalization:434`, H, `HistoryNoncollapsingToSlab:95`,
  `exists_pos_fixedHamiltonIveyRegion_for_identified_histories`,
  `exists_admissiblePinchingFunction_for_identified_incomingSlabs`,
  `exists_pos_le_singular_incoming_time_of_initialIdentification`.

**Restated:** A1, A2, R1–R5, and the S2–S4 leaves listed in §1 (new `…OfSpatial` files).

## 5. S from F\* (binder order `∀ B, ∃ Λ, ∀ Ctime, ∃ ε, ∀ constants, ∃ p₀ δbound ρbound v, ∀ H G …`)

- `∃ Λ := recenterConstant` (universal).
- `∀ Ctime`.
- `∃ ε := ε̄` (universal; chosen before C, hence compatible with C's `∀ ε`).
- `∀ C1 C2 C1s C2s qcan τmin δmax ρmax εcap Dcap mcap Cgrad κ a₀`:
  - `tol := 1/1000`, `r := transitionEnd + 1002`, `Dtrace := 64(r+1000)+1`,
    `Dbig := max Dcap (Dtrace+1)`. This gives `εold` and `δold`.
  - `m := max mcap (⌈tol⁻¹⌉₊+2)`, `accuracy := min εcap εold`,
    `ηrecord := min δmax (min δold ε̄)`. This gives `δ`.
  - `C Λ'` from `(C1s, C2s, κ)`. The spatial constants are used, not `C1 C2`.
  - `stepParameters` constant: `delta := δ`, `neckRadius := ρbound := min ρmax ρ₀`, floors
    `δ·ρbound`. This gives `Q v`.
  - `p₀ := ⟨fixed, recenterConstant, m, accuracy, Dbig, …⟩`, `δbound := min δmax δold`
    (`δ ≤ ηrecord ≤ δbound`).
- Per `H`: HANDOFF_S steps 3–4, unchanged.

How the constants tie to the cut precision:
- `m`, `accuracy`, `ηrecord` and `Dcap` feed `δ`, `k = max (m+6) (2⌊δ⁻¹⌋₊+4)`, `ηstar`, `mstar`
  and `εcut`, hence `K`, `Q` and `v`. They never feed `ε`. That dissolves F1.
- `Ctime` precedes `ε` only formally, since `ε̄` is universal.

## 6. Bricks, in dependency order (each ≤ 1500 lines)

| # | Brick | Lines | Kind |
|---|---|---|---|
| B1 | Reorder `∃ fixed recenterConstant` before `Dtrace…Ctime` (head restatements of :237/:633/:461) | 150–250 | mechanical |
| B2 | Entry 17: derivative-clause versions of the S1 leaves | 200–350 | mechanical |
| B3a | Spatial S2: `TerminalCanonicalAlternatives`, `TerminalCapCore:146–345`, `TerminalSphericalBarrier:369–548` on `SpatialCanonicalWitness` (`SpatialNeck.exists_neckBuffer_pullback_bound`, `SpatialLocalCap`, whole-branch exclusion by `scalar_bounds`) | 900–1300 | mechanical–moderate |
| B3b | Spatial S3 plus A1: `TerminalSphericalRegion:23`, `…Exterior:162`, `TerminalCutoffScale:111`, `TerminalCorePresentationExistence:431/654` | 800–1200 | mechanical |
| B4 | A2: spatial `DiscardedComponentClassification:22/106`, `StoppedCapCuttingSide:100–633` consumers, `TerminalComponentClassification:72` (compact case already spatial) | 700–1100 | mechanical–moderate |
| B5 | `FineCutNecks` plus R1 | 300–450 | mechanical |
| B6 | R2 (BaseHornMetricEvent copies) | 600–800 | mechanical |
| B7 | R3 (HornCutoffRecord copies) | 800–1100 | mechanical |
| B8 | R4 plus R5 (variable threshold, F\* with the long-slab hypothesis) | 900–1300 | moderate |
| B9 | Deep-horn ball (KL 71.1 compact containment plus `R ≤ Cb(A)R(x)`): base side by the log estimate; tip side by the escape-radius contradiction (`TerminalCurvatureEscape:166,358`, `Perelman/CanonicalNeighborhood/TerminalScalarEscape`) with cone exclusion | 1200–1500 | **design-critical** |
| B10 | Terminal → slice transfer at `x` (neck to `1/3000`, ball comparability, `τ → s`) via `SpatialNeck.exists_transport_of_local_comparisons` and `TerminalMetricConverges` | 400–600 | moderate |
| B11 | Two `MinimizingArm`s in `g(τ)` with `√R·ℓ ∈ [D,2D]` and comparison angle `≥ π/2`, from B9, B10 and one separating slice (`NeckChainAxialArms:131`) | 400–600 | moderate |
| B12 | Assembly: H at `τₙ → s`, then `TerminalNeckNormalization:434`, giving `FineCutNecks` (long slab) | 300–450 | mechanical |
| B13 | History window: unscathedness of two-arm points plus H on the survivor flow through `RegularCrossing` (Crossing / C3c lemma set) | ≥ 3000, split later | **design-critical, gates S** |
| B14 | S from F\* plus B12/B13 (HANDOFF_S bookkeeping) | 300–450 | mechanical |

- **Suitable for fast workers:** B1, B2, B3b, B5, B6, B7, B12, B14. Also B3a and B4, with a
  reviewer.
- **Design-critical:** B9 and B13. B8 also needs the lead, because the binder order of F\* is the
  contract with S.
- **Nothing here is refuted as a whole.** Only two things are refuted: the one-slab window as a
  general supply (§0.1), and the 18c chain as a coarse-supplied hypothesis (§0.2).
