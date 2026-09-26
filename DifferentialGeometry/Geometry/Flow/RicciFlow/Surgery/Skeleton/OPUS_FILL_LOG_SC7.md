# OPUS fill log SC7: T4′ consumer wave 7 = terminal bounded curvature at distance, core frontier distance, assembly glue (2026-09-26)

Worker lane SC7. Scope: (1) bounded curvature at bounded normalized distance in `L` at the terminal time,
`p₀`-FREE; (2) the core frontier is far from the deep horn point; (3) assembly glue (diagonal choice of
`τₙ`, stage-metric identification, `Rₙ` normalization). New files only; read-only compiles
(`LEAN_NUM_THREADS=2 lake env lean -DmaxSynthPendingDepth=3 -Dweak.linter.mathlibStandardSet=true`);
uncommitted imports through scratch oleans (real module names) under the session scratchpad `sc7/`.
No git writes, no lake build, no root-aggregate edit, no committed file modified.

## Progress
- read AGENTS.md (pc3: no header, no module docstring, zero comments), SC3/SC4/SC5/SC6 logs,
  DESIGN_S_SUPPLY, H13/H17/H18 digests, `BoundedCurvatureAtDistance*.lean` (statements),
  `BoundedCurvatureAtDistanceSliceTerminal.lean` (full), `TerminalScalarBall.lean`,
  `LocalPropagation.lean` (gradient/path machinery), SC4-c `HornSliceSeparatedSides.lean`,
  SC1-b `TerminalHornCanonicalNeck(Uniform).lean`, `RetainedCoreHistoryExtendAt.lean`,
  `TracedRegion.lean:640–680`, B13.

## Findings before the statements (failures first)

1. **Where `p₀` enters the tree's bounded-curvature-at-distance family.** The analytic core is already
   `p₀`-free: `RetainedCoreHistory.exists_normalized_scalar_bound_of_chain_traces`
   (`BoundedCurvatureAtDistanceTracedPositive.lean:97`, committed) takes the backward traces as an
   ABSTRACT hypothesis `htrace` (every point of every bounded-curvature chain from the base point has a
   backward trace of depth `τ ≤ θ/(4M)` across the events). `p₀` enters only through the SUPPLIER of
   `htrace`, `chain_traces_of_not_capWindowPoint_of_incomingSlab` (`BoundedCurvatureAtDistanceSlice.lean:74`,
   non-cap-window points + `Dcap ≤ modelRadius`). The final-slab version
   `exists_scalar_bound_at_distance_of_final_slab_window_of_le_coneAccuracy` is also `p₀`-free but needs
   `time last ≤ t − Λ/R(t,y)`, i.e. `R_L(x)(s − time last) > Λ`, which T4′'s threshold
   `Kfine·max(Λ/r², qcan, 1)` does not supply (DESIGN_S_SUPPLY (D) kills the `(s − a)⁻¹` term).
   So the `p₀`-free route is: replace the cap-window supplier by a STRONG-NECK supplier (a point whose
   class witness is a neck has a `HistoryStrongNeck`, hence a backward trace of depth `1/(5R)` across
   events), keeping the committed analytic core.
2. **Horn necks alone do not give arbitrary `A`.** Every horn point is the centre of an `εP`-neck, so
   `|∇R^{-1/2}| ≤ Cδ` along the horn and the singular end is at normalized distance `≳ 1/(Cδ)`; with
   `εP ≤ eta` FIXED this bounds `A`, not `A → ∞`. Arbitrary `A` is genuinely §4.2's cone exclusion,
   which needs backward flows near the curvature blow-up: the strong-neck traces of Finding 1.
3. **Compactness of `L`-balls reduces to a scalar bound.** `TerminalLimitMetric.isCompact_scalar_sublevel`
   (`TerminalScalarSublevel.lean:28`, committed): scalar sublevel sets of `L` are compact. So the closed
   `L`-ball of radius `r` is compact as soon as `R_L ≤ Q·R_L(x)` on the open ball of radius `2r`.
4. **Time-slice bounds transfer to `L` pointwise.** `TerminalLimitMetric.eventually_riemannianEDistOf_lt`
   (`TerminalScalarBall.lean:23`): `d_L(x,w) < r ⇒` eventually `d_τ(x,w) < r`; with
   `tendsto_metricScalarAt` a contradiction sequence at `L` becomes one at slices `τₙ → sₙ`.
5. **Core frontier distance (item 2) needs only the gradient bound.** On the frontier `R_L ≤ Λ/r²`
   (`frontier_scalar_le`); `R^{-1/2}` is `Cgrad/2`-Lipschitz along any path on which `R > qcan`
   (class gradient bound); the same path argument as `scalar_le_on_ball_of_gradient_bound`
   (`LocalPropagation.lean:347`), stopped at the first point with `R ≤ m`, gives
   `(√m)⁻¹ − (√R(x))⁻¹ ≤ (Cgrad/2)·d(x,y)` whenever `R(y) ≤ m`, `qcan < m`.
6. **Item 3(b) is mostly in the tree.** `RetainedCoreHistory.activeStage_extendHorizon_eq_last`
   (`TracedRegion.lean:647`), `stageMetric_extendHorizon_last` (`:657`), `extendAt`/`extendAtTime`
   (`RetainedCoreHistoryExtendAt.lean`, XA4) and `scalar_ball_bound_extendAt_iff`
   (`CrossingTimeZeroBound.lean:62`) already do the identification for balls and scalars; the missing
   piece is the distance/point transport along the carrier cast used by SC4-b/SC4-c.

## Statements (recorded BEFORE proving; elaborated with `sorry` first)

**SC7-2a** (`Perelman/CanonicalNeighborhood/InverseSqrtScalarDistance.lean`, ns
`DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood`):
```lean
theorem inv_sqrt_sub_inv_sqrt_scalar_le_of_threshold_gradient_bound
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    {C q m s r : ℝ} {x y : M} (hC : 0 ≤ C) (hqm : q < m)
    (hgrad : ∀ z, q < S.scalar s z → ∀ v : TangentSpace I z,
      |scalarDifferential (I := I) S s z v| ≤
        C * S.scalar s z * Real.sqrt (S.scalar s z) * Real.sqrt ((S.base.metric s).inner z v v))
    (hx : m ≤ S.scalar s x) (hy : S.scalar s y ≤ m) (hr : 0 ≤ r)
    (hxy : y ∈ riemannianClosedBallOf (S.base.metric s) x r) :
    (Real.sqrt m)⁻¹ - (Real.sqrt (S.scalar s x))⁻¹ ≤ C / 2 * r
```
**SC7-2b** (`Surgery/Topology/TerminalCoreFrontierDistance.lean`, ns
`…Surgery.Topology.OrientedThreeStage.IncomingSlab`):
```lean
theorem TerminalLimitMetric.inv_sqrt_sub_inv_sqrt_scalar_le_of_gradientBoundBefore
    (L : G.TerminalLimitMetric) {Cgrad : ℝ≥0} {q m r : ℝ} (hgrad : G.GradientBoundBefore Cgrad q s)
    (hqm : q < m) {x y : G.terminalRegularOpen} (hx : m < metricScalarAt L.metric x)
    (hy : metricScalarAt L.metric y < m) (hxy : riemannianEDistOf L.metric x y < ENNReal.ofReal r) :
    (Real.sqrt m)⁻¹ - (Real.sqrt (metricScalarAt L.metric x))⁻¹ ≤ Cgrad / 2 * r
```
**SC7-2c** (same file, ns `…Surgery.Topology.TerminalCorePresentation`):
```lean
theorem ofReal_lt_riemannianEDistOf_frontier_of_gradientBoundBefore
    (P : TerminalCorePresentation D ε Λ) (c) (hc : c ∈ P.component) {Cgrad : ℝ≥0} {q A : ℝ}
    (hgrad : D.slab.GradientBoundBefore Cgrad q D.endTime) (hq : 0 < q) (hA : 0 ≤ A)
    (x : D.slab.terminalRegularOpen)
    (hx : 2 * max (Λ * (P.coreRadius ^ 2)⁻¹) q * (1 + Cgrad * A) ^ 2 < metricScalarAt D.terminal.metric x) :
    ∀ w ∈ frontier (P.core c), ENNReal.ofReal (A / Real.sqrt (metricScalarAt D.terminal.metric x)) <
      riemannianEDistOf D.terminal.metric x w
```
(SC4-c's `hbase` is the case `A := 2A`; `R_L(xₙ)/max(Λ/r², qcan) → ∞` gives it eventually for each `A`.)

**SC7-1a** (`Surgery/Topology/BoundedCurvatureAtDistanceStrongTraces.lean`, ns `…Surgery.Topology`):
the `p₀`-free slice theorem, the cap-window hypothesis replaced by a chain backward-trace supply:
```lean
theorem RetainedCoreHistory.eventually_scalar_bound_at_distance_of_chain_backward_traces
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) {κ C1 C2 : ℝ} (hκ : 0 < κ) {Ctime Cgrad : ℝ≥0}
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) {θ : ℝ} (hθ : 0 < θ)
    (P₀ H hend s G hG) (t) (ht : ∀ n, time last < t n) (hts : ∀ n, t n < s n) (y) (q ρ : ℕ → ℝ)
    (hq : ∀ n, 0 < q n) (hqy : ∀ n, q n ≤ R(t n, y n))
    (hR : R(t n, y n) → ∞) (hRt : R(t n, y n) * t n → ∞)
    (hW : class spatial witnesses above q n at t n) (hslabs) (hder : before t n) (hgrad : before t n)
    (hpinch) (hpinchG) (hnc : TerminalNoncollapsedBefore … κ (ρ n) (t n)) (hρ : ρ n * √R → ∞)
    (D : ℕ → ℝ) (hD : Tendsto D atTop atTop)
    (hsupply : ∀ n N p δ M, p 0 = y n → (∀ k ≤ N, 0 < δ k) →
      (∀ k < N, p (k+1) ∈ ball_{t n}(p k, δ k)) → (∀ k ≤ N, ∀ z ∈ ball_{t n}(p k, δ k), R(t n, z) ≤ M) →
      R(t n, y n) ≤ M → M ≤ D n ^ 2 * R(t n, y n) → ∑ k ∈ range (N+1), δ k ≤ D n / √R(t n, y n) →
      ∀ k ≤ N, ∀ z ∈ ball_{t n}(p k, δ k), ∃ first, time first ≤ t n − θ / M ∧
        Nonempty (BackwardPointTrace (H n).toHistory first last _ z)) :
    ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 1 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ ball_{t n}(y n, A / √R(t n, y n)), R(t n, z) ≤ Q * R(t n, y n)
```
Route: `exists_normalized_scalar_bound_of_chain_traces` with `x := y` (no rebase chain: `q ≤ R(y)`),
`Kc := 1`, `lam := 1`, `θ_chain := 4θ`, chain radius `√8·D n`; subsequence extraction by
`Filter.extraction_forall_of_frequently`; the contradiction as in the private
`false_of_terminal_counterexamples` of `BoundedCurvatureAtDistanceSliceTerminal.lean`.

**SC7-1c** (same file): the terminal-time form. For `Lₙ` terminal limits, points `xₙ ∈ Ωₙ`,
`R_L(xₙ) → ∞`, `R_L(xₙ)·sₙ → ∞`, class data before `sₙ` (witnesses above `q`, derivative, gradient,
pinching, `TerminalNoncollapsedBefore … κ ρ t₀` for all `t₀ < sₙ`, `ρ·√R_L → ∞`), a radius sequence
`D → ∞`, and the supply of SC7-1a at every slice near `sₙ` (`∀ n, ∀ᶠ τ in 𝓝[<] sₙ`, supply at
`(τ, xₙ, D n)`):
```lean
    ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 1 ≤ Q ∧ ∀ᶠ n in atTop,
      (∀ w, riemannianEDistOf (L n).metric (x n) w < ENNReal.ofReal (A / √R_L(x n)) →
        metricScalarAt (L n).metric w ≤ Q * R_L(x n)) ∧
      IsCompact (riemannianClosedBallOf (L n).metric (x n) (A / √R_L(x n)))
```
**SC7-1b** (stretch; discharge of the supply in the horn from SC1-b + the class clause): recorded when
started.

**SC7-3a** (`Topology/Filter/DiagonalChoice.lean` or Surgery glue file, generic):
```lean
theorem exists_seq_forall_of_eventually {α : Type*} {F : ℕ → Filter α} [∀ n, (F n).NeBot]
    {ι : ℕ → Type*} [∀ n, Finite (ι n)] {p : ∀ n, ι n → α → Prop}
    (h : ∀ n i, ∀ᶠ a in F n, p n i a) : ∃ a : ℕ → α, ∀ n i, p n i (a n)
theorem exists_seq_mem_Ioo_forall_of_eventually_nhdsLT {s b : ℕ → ℝ} (hb : ∀ n, b n < s n)
    {ι …} {p} (h : ∀ n i, ∀ᶠ τ in 𝓝[<] s n, p n i τ) :
    ∃ τ : ℕ → ℝ, (∀ n, τ n ∈ Ioo (b n) (s n)) ∧ ∀ n i, p n i (τ n)
```
**SC7-3b** (Surgery glue file): transport of points, scalars and distances along the carrier of
`H.extendAt hend G hG hat hts` at `extendAtTime` (active stage = last): for `ŷ` with `HEq ŷ y`,
`metricScalarAt (stageMetric (activeStage t') t') ŷ = G.flow.scalar t y` and
`riemannianEDistOf (stageMetric …) ŷ ẑ = riemannianEDistOf (G.flow.base.metric t) y z`, plus existence
of the cast point.
**SC7-3c**: normalization. With `R n := G_n.flow.scalar (τ n) (x n)`, `Rl n := R_L(x n)`,
`∀ n, 0 < Rl n`, `Rl → ∞`, `|R n − Rl n| ≤ Rl n / 2` and `sₙ − τₙ ≤ 1/((n+1)·Rl n)`:
`(∀ n, 0 < R n) ∧ Tendsto R atTop atTop ∧ (∀ c, ∃ C, ∀ n, c ≤ C * R n) ∧ Tendsto (R n * (τ n − s n)) (𝓝 0)`
(B13's `hR`, `Tendsto R`, `qs ≤ Cs·R`, `qcan ≤ Cq·R`, `R(t − t₀) → 0`).

## Proof status (incremental)
- SC7-2a `Perelman/CanonicalNeighborhood/InverseSqrtScalarDistance.lean` — elaborated with `sorry`, then
  PROVED as stated (path from `exists_path_lintegral_speed_lt_of_mem_closedBall`, stopped at the first
  parameter where `R ≤ m`; `abs_sub_le_of_hasDerivAt_of_lintegral_le`); clean compile.
- SC7-2b/2c `Surgery/Topology/TerminalCoreFrontierDistance.lean` — elaborated with `sorry`, then PROVED
  as stated (2b: slices `τ → s` + SC7-2a + `le_of_tendsto`; 2c: `m := 2·max(Λ/r², q)`,
  `frontier_scalar_le`); clean compile (scratch module `SC7.TerminalCoreFrontierDistance`).
- SC7-1a `Surgery/Topology/BoundedCurvatureAtDistanceBackwardTraces.lean` — elaborated with `sorry`, then
  PROVED as stated; clean compile (scratch `SC7.BoundedCurvatureAtDistanceBackwardTraces`, 72 s).
  Uses only committed modules (`TracedPositive`, `TracedSecondLevel`, `Constants`, `Limit`).
- SC7-1c statement fixed before proving (same file): hypotheses per `n` on `G n` BEFORE `s n`
  (`SpatiallyCanonicalBefore ε C1 C2 (q n) (s n)`, derivative/gradient before `s n`,
  `∀ t₀ ∈ Ioo (time last) (s n), TerminalNoncollapsedBefore … κ (ρ n) t₀`), `0 < ρ n`,
  `q n < R_L(x n)`, `R_L(x n) → ∞`, `R_L(x n)·s n → ∞`, `ρ n·√R_L(x n) → ∞`, `D → ∞`, and
  `∀ n, ∀ᶠ τ in 𝓝[<] s n` the SC7-1a supply at `(τ, (x n).val, D n)`; conclusion as recorded above.
- SC7-1c PROVED (same file), clean compile (62 s). EXACT statement (for SC8), namespace
  `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology`, file
  `Surgery/Topology/BoundedCurvatureAtDistanceBackwardTraces.lean`:
```lean
theorem RetainedCoreHistory.eventually_terminal_scalar_bound_at_distance_of_chain_backward_traces
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) {κ C1 C2 : ℝ} (hκ : 0 < κ) {Ctime Cgrad : ℝ≥0}
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) {θ : ℝ} (hθ : 0 < θ)
    (P₀ : ℕ → OrientedThreeStage.{u}) (H : ∀ n, RetainedCoreHistory (P₀ n))
    (hend : ∀ n, (H n).time (Fin.last (H n).eventCount) = (H n).horizon) (s : ℕ → ℝ)
    (G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n))
    (hG : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    (L : ∀ n, (G n).TerminalLimitMetric) (x : ∀ n, (G n).terminalRegularOpen)
    (q ρ : ℕ → ℝ) (hq : ∀ n, 0 < q n) (hρ0 : ∀ n, 0 < ρ n)
    (hqx : ∀ n, q n < metricScalarAt (L n).metric (x n))
    (hR : Tendsto (fun n => metricScalarAt (L n).metric (x n)) atTop atTop)
    (hRs : Tendsto (fun n => metricScalarAt (L n).metric (x n) * s n) atTop atTop)
    (hW : ∀ n, (G n).SpatiallyCanonicalBefore ε C1 C2 (q n) (s n))
    (hslabs : ∀ n, (H n).EventSlabsDerivative Ctime (q n) (Fin.last (H n).eventCount))
    (hder : ∀ n, (G n).DerivativeBoundBefore Ctime (q n) (s n))
    (hgrad : ∀ n, (G n).GradientBoundBefore Cgrad (q n) (s n))
    (hpinch : ∀ n, (H n).EventSlabsPinched phi)
    (hpinchG : ∀ n, Perelman.PhiAlmostNonnegative (G n).flow
      (Ico ((H n).time (Fin.last (H n).eventCount)) (s n)) phi)
    (hnc : ∀ n, ∀ t₀ ∈ Ioo ((H n).time (Fin.last (H n).eventCount)) (s n),
      (H n).TerminalNoncollapsedBefore (hend n) (G n) (hG n) κ (ρ n) t₀)
    (hρ : Tendsto (fun n => ρ n * Real.sqrt (metricScalarAt (L n).metric (x n))) atTop atTop)
    (D : ℕ → ℝ) (hD : Tendsto D atTop atTop)
    (hsupply : ∀ n, ∀ᶠ τ in 𝓝[<] s n,
      ∀ (N : ℕ) (p : ℕ → ((H n).stage (Fin.last (H n).eventCount)).Carrier)
        (δ : ℕ → ℝ) (M : ℝ), p 0 = (x n).val → (∀ k ≤ N, 0 < δ k) →
        (∀ k < N, p (k + 1) ∈ riemannianBallOf ((G n).flow.base.metric τ) (p k) (δ k)) →
        (∀ k ≤ N, ∀ z ∈ riemannianBallOf ((G n).flow.base.metric τ) (p k) (δ k),
          (G n).flow.scalar τ z ≤ M) →
        (G n).flow.scalar τ (x n).val ≤ M →
        M ≤ D n ^ 2 * (G n).flow.scalar τ (x n).val →
        ∑ k ∈ Finset.range (N + 1), δ k ≤ D n / Real.sqrt ((G n).flow.scalar τ (x n).val) →
        ∀ k ≤ N, ∀ z ∈ riemannianBallOf ((G n).flow.base.metric τ) (p k) (δ k),
          ∃ first : Fin ((H n).eventCount + 1), (H n).time first ≤ τ - θ / M ∧
            Nonempty (BackwardPointTrace (H n).toHistory first (Fin.last (H n).eventCount)
              (Fin.le_last first) z)) :
    ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 1 ≤ Q ∧ ∀ᶠ n in atTop,
      (∀ w : (G n).terminalRegularOpen,
        riemannianEDistOf (L n).metric (x n) w <
          ENNReal.ofReal (A / Real.sqrt (metricScalarAt (L n).metric (x n))) →
        metricScalarAt (L n).metric w ≤ Q * metricScalarAt (L n).metric (x n)) ∧
      IsCompact (riemannianClosedBallOf (L n).metric (x n)
        (A / Real.sqrt (metricScalarAt (L n).metric (x n))))
```
  NO age hypothesis in the last slab (no `R(τ − time last) → ∞`, no final-slab window): the backward
  windows come from the SUPPLY `hsupply` (traces across events, depth `θ/M`), which is what the class
  clause provides at neck-witness points (`HistoryStrongNeck`, depth `1/(5R)`; `θ = 1/5`). The only
  time hypothesis is `hRs : R_L(xₙ)·sₙ → ∞` (ABSOLUTE time since the start of the history, the `htime`
  of the committed chain theorem; it holds as soon as `sₙ` is bounded below, e.g. by the existence time
  of the flow from the fixed `g₀`) — flagged for the lead below. No `p₀`, no records, no cap window.
- Answer to the lead's constraint (class + horn topology, not the in-slab cone argument): the cone
  argument used here is the committed `exists_normalized_scalar_bound_of_chain_traces`, which is NOT
  in-slab: its backward flows are the history traces of `hsupply`. The horn topology and the class enter
  exactly in discharging `hsupply` (SC7-1b): at slices `τ` near `sₙ`, every point of a bounded-curvature
  chain from `xₙ` is (for `τ` close enough, depending on `n`) a point of a compact subset of `Lₙ`'s horn
  half range, where SC1-b (`eventually_forall_neck_alternative_of_subset_hornHalfRange`) makes every
  class witness a neck, so the strong clause gives a `HistoryStrongNeck`, hence a trace of depth
  `1/(5R) ≥ 1/(5M)`.
- SC7-1b statement fixed (recorded before proving), `Surgery/Topology/HornChainBackwardTraces.lean`,
  ns `…Surgery.Topology.RetainedCoreHistory`:
  `eventually_chain_backward_traces_of_mem_hornHalfRange : ∃ eta > 0, ∀ H G L hsing parameters
  (P : TerminalCorePresentation {…slab := G, terminal := L…} εP Λ), εP ≤ eta → ∀ c ∈ P.component, ∀ e,
  ∀ x ∈ P.hornHalfRange c e, ∀ ε ε₁ C1 C2 qcan Ctime Cgrad, 0 < ε → ε ≤ eta → 0 < qcan →
  H.StronglyCanonicalBefore last G ε ε₁ C1 C2 qcan s → G.DerivativeBoundBefore Ctime qcan s →
  G.GradientBoundBefore Cgrad qcan s → ∀ Dr ≥ 0,
  8·max(4·C2·Λ/r², max(Λ/r², qcan))·(1 + Cgrad·Dr)² < R_L(x) → ∀ᶠ τ in 𝓝[<] s,` SC7-1c's supply at
  `(τ, x, Dr)` with `θ = 1/5`. Route (no `p₀`, no age): the chain region is preconnected (union of
  path-connected balls), has `R_τ ≤ M ≤ 2Dr²R_L(x) + 1` (chain hypothesis) and `R_τ > R_τ(x)/(2κ²)`
  (SC7-2a at `τ`, `κ = 1 + Cgrad·Dr`); for `τ` within `1/(4·Mmax·(Ctime+1))` of `s` the reciprocal
  Lipschitz bound (`lipschitzOnWith_inv_max_scalar`) puts it in `Ω` with `R_L ∈ [mlow/2, 2Mmax]`; it avoids
  the core frontier (`R_L > Λ/r²`), meets the horn at `x`, so lies in `P.hornHalfRange c e`
  (`exists_hornHalfRange_superset_of_isPreconnected`); SC2's
  `eventually_forall_historyStrongNeck_of_subset_hornHalfRange` on the compact
  `B = hornHalfRange ∩ {mlow/2 ≤ R_L ≤ 2Mmax}` gives a `HistoryStrongNeck` at every chain point, whose
  survivor point is a backward trace of depth `1/(5R) ≥ 1/(5M)`.
- SC7-3a `Topology/Sequences/DiagonalChoice.lean` (ns `Filter`): `exists_seq_forall_of_eventually`,
  `exists_seq_mem_Ioo_forall_of_eventually_nhdsLT` — PROVED as stated, clean (DEVIATION: compiled with
  the proof directly, the `sorry` skeleton was written but not compiled separately).
- SC7-3c `Topology/Sequences/RescalingFactor.lean` (ns `DifferentialGeometry`):
  `exists_rescaling_factor_normalization {R Rl s τ} (hpos : ∀ n, 0 < Rl n) (hRl : Rl → ∞)
  (hclose : ∀ n, |R n − Rl n| ≤ Rl n / 2) (hτs : ∀ n, τ n < s n) (hgap : ∀ n, (s n − τ n)·Rl n ≤ 1/(n+1)) :
  (∀ n, 0 < R n) ∧ R → ∞ ∧ (∀ c, ∃ C, ∀ n, c ≤ C·R n) ∧ R n·(τ n − s n) → 0` — PROVED, clean (same
  deviation as 3a).
- SC7-3b statement (recorded before proving), `Surgery/Topology/RetainedCoreHistoryExtendAtTransport.lean`:
  `exists_homeomorph_extendAt_stageAt H hend G hG hat hts : ∃ e : (H'.stageAt t').Carrier ≃ₜ
  (H.stage last).Carrier, (∀ y, HEq y (e y)) ∧ (∀ y z, d_{H'.stageMetric (activeStage t') t'}(y, z) =
  d_{G(t)}(e y, e z)) ∧ ∀ y, R_{H'…}(y) = G.flow.scalar t (e y)` (`H' = H.extendAt …`, `t' = extendAtTime`):
  the carrier cast used to feed SC4-c's separation data (sets in `D.stage.Carrier`, `G(τ)`-distances) into
  SC4-b/B13 (points of `stageAt`, stage-metric distances); open sets transport along `e`.
- SC7-1c REVISED (after the exact statement above was recorded; weaker hypotheses, still proved):
  `hsupply` and `hqx` are now `∀ᶠ n in atTop, …` instead of `∀ n, …` (needed so that SC7-1d can feed
  SC7-1b, whose largeness hypothesis only holds eventually). Recompiled clean.
- SC7-1b PROVED, clean (`HornChainBackwardTraces.lean`). The first single-block proof exceeded the
  per-declaration heartbeat budget; it was split along real interfaces into public lemmas (no budget
  override): `Geometry.Metric.riemannianEDistOf_lt_of_mem_ball_chain`,
  `Geometry.Metric.isPreconnected_biUnion_riemannianBallOf_chain`,
  `IncomingSlab.TerminalLimitMetric.eventually_forall_scalar_bounds_of_scalar_mem_Ioc` (uniform forward
  scalar control: for `τ` near `s`, every point with `m < R_τ ≤ Mx` (`2q < m`) is in `Ω` with
  `m/2 ≤ R_L ≤ 2Mx`), `TerminalCorePresentation.subset_hornHalfRange_of_isPreconnected_of_scalar_gt`
  (a preconnected set through a horn point with `R_L > Λ/r²` stays in that horn), plus one private
  arithmetic lemma (SC7-2a applied along the chain). Deviation: `Mmax := 2(Dr²+1)R_L(x)`.
- SC7-1d (NEW, the T4′-currency form of item 1), `Surgery/Topology/HornTerminalScalarBound.lean`:
  `RetainedCoreHistory.exists_eventually_terminal_scalar_bound_at_distance_of_mem_hornHalfRange :
  ∃ eta > 0, ∀ ε ε₁ κ C1 C2 qcan ρ Ctime Cgrad phi, 0 < ε → ε ≤ eta → 0 < κ → 0 < qcan → 0 < ρ →
  AdmissiblePinchingFunction phi → ∀ (sequences H hend s G hG L hsing parameters εP Λ P), (∀ n, εP n ≤ eta)
  → ∀ c (∀ n, c n ∈ component) e x (∀ n, x n ∈ hornHalfRange (c n) (e n)) →` the strong class before
  `sₙ` (`StronglyCanonicalBefore`, `EventSlabsDerivative`, derivative/gradient before `sₙ`,
  `EventSlabsPinched phi`, `PhiAlmostNonnegative` on the terminal slab, `TerminalNoncollapsedBefore … κ ρ t₀`
  for all `t₀ < sₙ`) `→ R_L(xₙ)/max(Λₙ/rₙ², qcan) → ∞ → R_L(xₙ)·sₙ → ∞ → ∀ A > 0, ∃ Q ≥ 1, ∀ᶠ n,
  (∀ w, d_L(xₙ,w) < A/√R_L(xₙ) → R_L(w) ≤ Q·R_L(xₙ)) ∧ IsCompact (closedBall_L(xₙ, A/√R_L(xₙ)))`.
  Route: `D n := √(R/(8Km))/(4(Cgrad+1)) → ∞` (private `exists_radius_sequence`), SC7-1b supplies
  SC7-1c's `hsupply` eventually, SC7-1c concludes. `eta := min eta(SC7-1b) coneAccuracy`. PROVED, clean.
- SC7-3b REVISED (DEVIATION, recorded): `generalize` cannot abstract the active stage in a
  homeomorphism-valued statement ("result is not type correct"); replaced by the HEq form used in
  `scalar_ball_bound_extendAt_iff`: `riemannianEDistOf_extendAt_stageAt_eq (y z) (yh zh) (HEq yh y)
  (HEq zh z) : d_{H'…}(yh, zh) = d_{G(t)}(y, z) ∧ R_{H'…}(yh) = G.flow.scalar t y` and
  `exists_heq_extendAt_stageAt y : ∃ yh, HEq yh y`. PROVED, clean.

## Axioms (`#print axioms`, scratch file `sc7/SC7/Ax.lean`, deleted)
All 16 public headlines: `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).

## Deliverables (all new, uncommitted, not in the root aggregate; all compile with zero output)
| File | Lines | Headlines | Uncommitted deps |
|---|---|---|---|
| `Perelman/CanonicalNeighborhood/InverseSqrtScalarDistance.lean` | 112 | `inv_sqrt_sub_inv_sqrt_scalar_le_of_threshold_gradient_bound` | — |
| `Surgery/Topology/TerminalCoreFrontierDistance.lean` | 104 | `TerminalLimitMetric.inv_sqrt_sub_inv_sqrt_scalar_le_of_gradientBoundBefore`, `TerminalCorePresentation.ofReal_lt_riemannianEDistOf_frontier_of_gradientBoundBefore` | InverseSqrtScalarDistance |
| `Surgery/Topology/BoundedCurvatureAtDistanceBackwardTraces.lean` | 432 | `RetainedCoreHistory.eventually_scalar_bound_at_distance_of_chain_backward_traces`, `…eventually_terminal_scalar_bound_at_distance_of_chain_backward_traces` | — |
| `Surgery/Topology/HornChainBackwardTraces.lean` | 410 | `Geometry.Metric.riemannianEDistOf_lt_of_mem_ball_chain`, `…isPreconnected_biUnion_riemannianBallOf_chain`, `TerminalLimitMetric.eventually_forall_scalar_bounds_of_scalar_mem_Ioc`, `TerminalCorePresentation.subset_hornHalfRange_of_isPreconnected_of_scalar_gt`, `RetainedCoreHistory.eventually_chain_backward_traces_of_mem_hornHalfRange` | InverseSqrtScalarDistance; SC2 `HistoryStrongNeckUniform` (→ SP1 StrongNeckRestriction, TruncatedNeck, HistoryStrongNeck; TerminalSpatialCapMovingBarrier; InteriorCollar; TerminalHornCanonicalNeckUniform; TerminalFineNeckOfSpatialNecks; SpatialNeckOpenSubset) |
| `Surgery/Topology/HornTerminalScalarBound.lean` | 153 | `RetainedCoreHistory.exists_eventually_terminal_scalar_bound_at_distance_of_mem_hornHalfRange` | HornChainBackwardTraces, BoundedCurvatureAtDistanceBackwardTraces |
| `Surgery/Topology/RetainedCoreHistoryExtendAtTransport.lean` | 77 | `RetainedCoreHistory.riemannianEDistOf_extendAt_stageAt_eq`, `…exists_heq_extendAt_stageAt` | XA4 `RetainedCoreHistoryExtendAt` |
| `Topology/Sequences/DiagonalChoice.lean` | 24 | `Filter.exists_seq_forall_of_eventually`, `Filter.exists_seq_mem_Ioo_forall_of_eventually_nhdsLT` | — |
| `Topology/Sequences/RescalingFactor.lean` | 48 | `DifferentialGeometry.exists_rescaling_factor_normalization` | — |
(paths under `Geometry/Flow/RicciFlow/` except the last two, which are under `DifferentialGeometry/`.)
- No `open private`, no copied private lemmas, no committed file touched; new public names grep-unique.
- Acceptance order: InverseSqrtScalarDistance → TerminalCoreFrontierDistance; BackwardTraces (committed
  deps only); SC2 chain → HornChainBackwardTraces → HornTerminalScalarBound; XA4 ExtendAt → Transport;
  the two `Topology/Sequences` files (Mathlib only).

## What the T4′ final assembly still lacks
1. Inputs of SC7-1d not literally in T4′'s hypothesis list: (a) `EventSlabsPinched phi` and
   `PhiAlmostNonnegative` on the terminal slab for one admissible `phi` (from the initial Hamilton–Ivey
   region + records; SC4-a/X5 derive it inline — needs extraction as a lemma); (b) `R_L(xₙ)·sₙ → ∞`
   (the committed chain theorem's `htime`; follows from a positive lower bound on `sₙ`, e.g. the existence
   time of the flow from the fixed `g₀`, or from any event time — not yet a lemma); (c) `ε ≤ eta(SC7-1d)`
   and `εP ≤ eta(SC7-1d)`: SC4-d's tolerance bundle must add SC7-1d's `eta` (which includes `coneAccuracy`).
2. SC4-c's inputs are now supplied: compact `L`-ball of radius `4A/√R_L` (SC7-1d with `A := 4A`) and the
   core frontier farther than `2A/√R_L` (SC7-2c with `A := 2A`, eventually since `R_L/max(Λ/r²,qcan) → ∞`).
3. SC8's uniform `Qup` for SC6's top-ball input (SC7-1d gives `Q(A)`, `A`-dependent) and the lower bound
   `Qlow(A)` at time `τₙ` (SC7-2a at `τₙ` gives `R ≥ R(x)/(2(1+Cgrad A)²)` on the normalized `A`-ball).
4. The glue remains to be written out in the final theorem: choose `τₙ` by SC7-3a over the finitely many
   per-`n` filters (SC2-e contrapositive, SC4-c clauses for `A = 1..mₙ`, SC6/B13 inputs), transport
   points/sets/distances to `H.extendAt` by SC7-3b, normalization by SC7-3c; T3A-2 (`htraced` on
   extended histories, SC6) and the line/limit steps SC4-a/b; T4′'s `FineCutNeckSupplyStrong` wrapper.
