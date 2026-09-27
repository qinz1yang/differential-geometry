# OPUS fill log SP2: young cap-window strong-neck producer (2026-09-26)

Worker lane SP2. Scope: case (ii) of `DESIGN_STRONG_INTERFACE.md` §4.3 (young cap-window points),
the §2 rows S2 (splice with `IncomingBackwardNeck`, whole-tube survival, chart transport) and the
C3b′ producer, consuming SP1's predicate file / S1′ / S2e by scratch chain. New files only;
read-only compiles; no git writes, no lake build, no root-aggregate edit.

## Progress

- 00:00 read AGENTS.md (pc3: no header, no module docstring, zero comments), DESIGN_STRONG_INTERFACE,
  H13 digest, SP1/SPT logs. SP1 has delivered nothing yet (log: 1 entry). Grep:
  `HistoryStrongNeck`/`TruncatedNeck` absent from the tree.
- +0:50 read H17 digest (lead message: binding). Surveyed suppliers:
  `CapWindowStandardComparison.lean:20` (bridge), `CapWindowSpatialCanonicalWitness.lean` (spatial
  C3b producer, uncommitted, other lane), `StandardWindowSpatialCanonical.lean:55` (M4),
  `StandardSpatialCanonicalMargins.lean:153` (private tip witness: it BUILDS A CAP at every
  `‖x‖ ≤ D` for an arbitrary `D ≥` far radius, but its statement hides the constructor),
  `SpatialCanonicalWitnessUniformTransport.lean:757` (conclusion keeps only
  `W'.domain.carrier = F '' W.domain.carrier`), `SpatialCanonicalWitnessUniverseTransport.lean`.

## Route decision (delta against DESIGN_STRONG_INTERFACE §4.3(ii) and H17 items 1–5)

**Case (ii) needs no strong neck and no splice: at EVERY cap-window point a non-neck (cap)
witness can be chosen, uniformly.** A cap-window point has standard coordinate `‖x‖ < Dcap + 1`
(bounded distance from the tip) and standard age `σ ≤ θcap < 1`. On the standard solution the
closed Euclidean ball of radius `r(Dcap) ≫ Dcap` with a radial ε-neck collar is a cap witness
centred at every `x` with `‖x‖ ≤ Dcap + 1`, for every `σ ∈ [0, Θ]` (this is exactly what the
private tip construction does with `D := max Dfar (Dcap + 1)`); its constants depend on `Dcap, Θ`,
which is legal because in `StrongNecksOfCutoffClass` `C1h C2h` are `∃` in the same block as `Dcap`
and after `κ` (hence after the X-core's `θcap`). With `W` a cap, `StronglyCanonicalAt`'s implication
`(∃ n, W.alternative = .neck n) → HistoryStrongNeck …` is vacuous. This is the `∃ W` freedom that
F4(b) and H17 item (3) sanction ("prove a cap witness can be chosen"), applied at all cap-window
points instead of only where the tube meets glued material. Consequences:
  - H17 (1) (θcap strict margin `R(t−T) > 1`), (2) (single common flow), (4) (S2e dichotomy) and
    (5) (nominal depth `r²`) concern the neck/splice branch, which this producer never enters.
    They remain binding for any lane that produces NECK witnesses at young points (case (iii),
    X-core). S1′/S2e are NOT consumed by case (ii).
  - The consumer (T3A) already must exclude cap witnesses in its ℝ×N limit (F4(b)); a larger `C1h`
    (depending on `Dcap`) only enlarges the capture radius `4C1h/√R`, fixed before `Kfine`.
  - The cap-ness must survive two transports whose statements hide the constructor. Invariant used
    instead: `IsPreconnected (frontier W.domain.carrier)` (true for a cap: frontier = image of
    `S² × {1}`; false for a neck: frontier = two disjoint spheres). Both transports expose
    `W'.domain = F '' W.domain` / keep the domain, so the invariant passes by
    `frontier (F '' D) = F '' frontier D`.

## Statements (written first; elaborated with `sorry` before proving)

S-a `Perelman/CanonicalNeighborhood/SpatialCanonicalWitnessFrontier.lean`
  - `SpatialLocalNeck.not_isPreconnected_frontier (n : SpatialLocalNeck g eps x U) : ¬ IsPreconnected (frontier U)`
  - `SpatialLocalCap.isPreconnected_frontier (c : SpatialLocalCap g eps x U) : IsPreconnected (frontier U)`
  - `SpatialCanonicalWitness.alternative_ne_neck_of_isPreconnected_frontier (W) (h : IsPreconnected (frontier W.domain.carrier)) (n) : W.alternative ≠ .neck n`
  - `SpatialCanonicalWitness.isPreconnected_frontier_of_alternative_eq_cap (W) (h : W.alternative = .cap c d) : IsPreconnected (frontier W.domain.carrier)`
S-b `Perelman/StandardSolution/StandardCapSpatialCanonical.lean`
  - `StandardSolution.exists_cap_spatialCanonicalWitness_with_margins (heps : 0 < eps) (hsmall : eps < 1/11) (hΘ : Θ < 1) (Dcore : ℝ) : ∃ C, 1 ≤ C ∧ ∀ S x t, t ∈ Icc 0 Θ → ‖x‖ ≤ Dcore → ∃ W : SpatialCanonicalWitness (S.val.metric t) eps C C x, W.capTubeHasNeckChart eps ∧ W.HasMargins (1/20) ∧ ∃ c d, W.alternative = .cap c d`
    (private copy of the tip construction with the constructor exposed; deferred merge: expose it
    in `StandardSpatialCanonicalMargins.exists_tip_spatialCanonicalWitness_with_margins`).
S-c `Perelman/StandardSolution/StandardWindowCapWitness.lean` (static-slice analogue of M4, all
    ages `T ∈ [0, Θ]`): `exists_window_cap_spatialCanonicalWitness_of_standard_close` — for `g` on
    `standardCapWindow D` spatially `e`-close (orders `≤ N`) to `Q.val.metric T`, every `z` with
    `‖z‖ < r` and the gradient bound: `∃ W : SpatialCanonicalWitness g ε Cw C2 z, W.capTubeHasNeckChart ε ∧ IsPreconnected (frontier W.domain.carrier)`; `Cw D N e` depend on `ε Θ r`.
S-d `Surgery/Topology/CapWindowCapWitness.lean` (producer, case (ii)):
  `RetainedCoreHistory.exists_capWindowPoint_nonNeck_spatialCanonicalWitness` — hypotheses exactly
  those of `exists_capWindowPoint_spatialCanonicalWitness` (class-derived: records family,
  identification, recenter bound, slab initial metric, event/terminal derivative bounds, cap-window
  point, `qcan < R`, gradient bound), but `Cs` is `∃` AFTER `Dw θcap`; conclusion
  `∃ W : SpatialCanonicalWitness (Gk.flow.base.metric t) ε Cs (max Cs Cgrad) y, W.capTubeHasNeckChart ε ∧ ∀ n, W.alternative ≠ .neck n`,
  and the corollary `…stronglyCanonicalAt` (`H.StronglyCanonicalAt k Gk ε ε₁ Cs (max Cs Cgrad) y t`,
  every `ε₁`) against SP1's predicate once it lands.

## Progress (cont.)

- +1:30 S-a PROVED, compiles clean (0 warnings): `SpatialCanonicalWitnessFrontier.lean`.
- +2:00 S-b PROVED, compiles clean: `StandardCapSpatialCanonical.lean` (private copy of the tip
  construction with `∃ c d, W.alternative = .cap c d` exposed; wrapper with `D' := max Dfar Dcore`).
  Deferred merge: expose the constructor in
  `StandardSpatialCanonicalMargins.exists_tip_spatialCanonicalWitness_with_margins` and delete the copy.
- +2:20 S-c PROVED, compiles clean: `StandardWindowCapWitness.lean`. Statement delta (recorded
  before re-proving): `Cw` is now `∃` BEFORE the window size, i.e.
  `∃ Cw, 1 ≤ Cw ∧ ∀ ρ, ∃ D N e, r + ρ < D ∧ 0 < e ∧ …` — the history producer needs room
  `Λ(4Cw+2)` around the point inside the window, and `Cw` grows with `r` (cap size), so `D` must be
  chosen after `Cw`. Static slice form (a metric `g` close to `Q.val.metric T`), all `T ∈ [0, Θ]`.
- +2:25 Lead message (HistoryStrongNeck redefined with depth `θ₀·R⁻¹`, `θ₀ = 1/4`; "build your
  splice on that"). Delta recorded: the case-(ii) producer builds NO splice and consumes NO
  `HistoryStrongNeck` field — it proves a non-neck (cap) witness at every cap-window point, so the
  strong clause is vacuous there whatever the depth convention (`R⁻¹` or `θ₀R⁻¹`). The θ₀ form is
  relevant only to lanes that output neck witnesses at young points (case (iii)). The corollary to
  `StronglyCanonicalAt` is written against SP1's file when it lands (only the predicate's shape
  `(∃ n, W.alternative = .neck n) → …` is used).
- +3:10 S-d PROVED, compiles clean: `CapWindowCapWitness.lean`
  (`exists_capWindowPoint_nonNeck_spatialCanonicalWitness`; proof skeleton follows the spatial C3b
  producer `CapWindowSpatialCanonicalWitness.lean`, uncommitted, other lane, with S-c in place of M4 and
  the frontier invariant carried through `pushforwardOfInjectiveULift` and `scaleMetric`).
  Added to S-a: `domain_scaleMetric`, `domain_enlargeConstants`,
  `pushforwardOfInjectiveULift_domain_carrier`, `isPreconnected_frontier_image_of_injective`,
  `isPreconnected_frontier_pushforwardOfInjectiveULift`.
- +3:20 Lead message 2 (θ₀ = 1/5, S1′ retired, "produce the young cap-window neck at history level").
  Delta: NOT needed for case (ii), and not built. Reason (checked against the on-disk predicates):
  SP1's `StronglyCanonicalAt` (`HistoryStrongNeck.lean`) is `∃ W, capTubeHasNeckChart ∧ ((∃ n,
  W.alternative = .neck n) → HistoryStrongNeck …)`; S-d gives a `W` with `∀ n, W.alternative ≠ .neck n`
  at every cap-window point, so the implication is discharged by `absurd`, for every `ε₁` and every
  depth convention. The consumer-side trigger `exists_tolerance_historyStrongNeck_of_spatialNeck`
  (`HistoryStrongNeckTrigger.lean`, SP1) forces `W` to be a neck only where an `η(C1h,C2h)`-fine spatial
  neck exists; with `C1h ≥ Cs(Dcap, θcap)` that `η` is fixed before `Kfine`, as T5-lite already orders
  it. No time jets, no splice, no `TruncatedNeck` datum, no θcap margin are used by this producer.
  H17 (3) ("prove a cap witness can be chosen") is met at ALL cap-window points.
- +3:30 Corollary against SP1's predicate (SP1 files compiled as my scratch oleans:
  StrongNeckRestriction → TruncatedNeck → HistoryStrongNeck): `exists_capWindow_stronglyCanonicalWhere`
  — for any slab `k`, `Gk` with initial metric, event derivative bounds, `Gk.DerivativeBoundBefore
  Ctime qcan s`, `Gk.GradientBoundBefore Cgrad qcan s`, and EVERY `ε₁`:
  `H.StronglyCanonicalWhere k Gk ε ε₁ Cs (max Cs Cgrad) qcan (fun y t => H.CapWindowPoint records k y t Dw θcap)`.
  The leaf's case-(ii) region `R(t−a) < τmin ∧ CapWindowPoint` is a subset (drop the age conjunct).
- +3:40 `#print axioms` (scratch file, removed) on all 11 public/used declarations:
  `propext, Classical.choice, Quot.sound`; no `sorryAx`. Names unique library-wide (grep).
  `git diff --check` clean; no trailing whitespace, no comments, no diagnostics in the four files.

## Result

| File (new) | Lines | Status |
|---|---|---|
| `Perelman/CanonicalNeighborhood/SpatialCanonicalWitnessFrontier.lean` | 148 | proved, clean (direct `lake env lean`) |
| `Perelman/StandardSolution/StandardCapSpatialCanonical.lean` | ~400 | proved, clean (scratch olean) |
| `Perelman/StandardSolution/StandardWindowCapWitness.lean` | 149 | proved, clean (scratch olean) |
| `Surgery/Topology/CapWindowCapWitness.lean` | 227 | proved, clean (scratch olean; imports SP1's `HistoryStrongNeck`) |

Acceptance order: SpatialCanonicalWitnessFrontier → StandardCapSpatialCanonical →
StandardWindowCapWitness → (SP1) StrongNeckRestriction → TruncatedNeck → HistoryStrongNeck →
CapWindowCapWitness. Not registered in the root aggregate.

Deferred merges:
1. `StandardCapSpatialCanonical.exists_tip_cap_spatialCanonicalWitness_with_margins` is a private copy
   (~270 lines) of `StandardSpatialCanonicalMargins.exists_tip_spatialCanonicalWitness_with_margins`
   with `∃ c d, W.alternative = .cap c d` added to the conclusion; merge = add that conjunct in place.
2. `CapWindowCapWitness.exists_capWindowPoint_nonNeck_spatialCanonicalWitness` repeats the bridge part
   of `CapWindowSpatialCanonicalWitness.exists_capWindowPoint_spatialCanonicalWitness` (other lane);
   a shared lemma parametrised by the window-witness producer would remove ~120 duplicated lines.

What remains for the leaf's case (ii) (assembly inside `strongNecksOfCutoffClass`, not done here):
take `Dw := Dcap`, `θcap` from the X-core's `∃`; `C1h ≥ Cs`, `C2h ≥ max Cs Cgrad` (enlarge via SP1's
`mono_constants`); `Rcap ≤ p₀.modelRadius`, `mcap ≤ p₀.modelOrder`, `εcap`, `δmax`, `ρmax` into the leaf's
`p₀` constraints; `records`, identification and `recenterConstant·δbound ≤ 1/2` from `InCutoffClass`;
initial metric from `IsContinuationSlab`/`isContinuationSlab_event`; `EventSlabsDerivative` for
`j.castSucc` by restriction; threshold lift to `qh ≥ qcan` by `of_threshold_le`.

## Justification (lead ACCEPTED the cap-witness route, lane closed)

The route is consistent with the consumer. SC1-c (`SpatialCanonicalWitnessNeckExclusion`) says an
`η(C1h, C2h)`-fine spatial neck at `y` forces every spatial canonical witness at `y` with constants
`(C1h, C2h)` to be a neck. In the §4.3 blow-up the consumer sees long necks: closeness to the ℝ×N
limit on balls of radius `Aₙ → ∞`. At such points the fine neck exists eventually, so the chosen `W`
must be a neck and the strong-neck trigger (`exists_tolerance_historyStrongNeck_of_spatialNeck`)
fires. A cap-window point, which carries this lane's non-neck (cap) witness, therefore cannot be such
a point: cap-window points are excluded eventually, and no backward window is ever needed at them.
The constants are legal. `C1h, C2h ≥ Cs(Dcap, θcap)` grow with `Dcap` and `θcap`, and are chosen in the
same `∃` block as `Dcap`, after `κ` (hence after the X-core's `θcap`). `η(C1h, C2h)` is then fixed
before `Kfine`, as T5-lite orders it. No splice and no history-level neck are built in this lane.
