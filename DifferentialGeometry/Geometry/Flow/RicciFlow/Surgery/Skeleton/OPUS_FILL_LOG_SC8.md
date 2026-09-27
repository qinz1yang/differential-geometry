# OPUS fill log SC8: T4′ consumer wave 8 = the inductive step's geometric content (2026-09-26)

Worker lane SC8. Scope (lead): (1) the finite-window pointed limit flow at depth `T` for the T4′
sequence (finite-window B13 from W1′ + gluing, T4′ inputs, no `hpar`/`hscale`); (2) a line at time 0
of that window limit (SC4's separation route on W1′'s time-0 convergence maps); (3) simple
connectivity of the window limit (or the strongest proved statement); (4) the converter
history → pointed data at depth: the ℝ×N capture at every slice of the window limit, in SC6-c's
per-layer supply shape; (5, lead delta, highest priority after 1) the time-0 blow-up limit at the
deep horn point has globally bounded curvature ⇒ a uniform `Qup` for the approximants' top balls at
every radius (replacing SC6-f, no age hypothesis).
New files only; read-only compiles (`LEAN_NUM_THREADS=4 lake env lean -DmaxSynthPendingDepth=3
-Dweak.linter.mathlibStandardSet=true`); uncommitted imports through scratch modules `SC8.*` under the
session scratchpad `sc8/` (`cc.sh emit|check`, module rename + `rw.sed` rewriting of imports and
`open private … from`). No git writes, no lake build, no root-aggregate edit, no committed file
modified.

## Progress
- read AGENTS.md (pc3), SC1–SC7 logs, XP2/XP3/XA4 logs, DESIGN_S_SUPPLY §0–§3, H13/H17/H18/H20.
- scratch chains: A (XP3 `LocalPointedFlowLimit`, W1′, `OpenClosedGluing`, κ on `(−T,0]`, XP2′
  `LocalFlowLimitWindowTransfer`, XA4 `LocalFlowLimitShiftedConvergence`,
  `TracedRegionTimeZeroScalarBound`, the committed-but-unbuilt `TerminalProductSplitting`, SC5's three
  files, SC4's `SeparatedSidePoint`) and B (SP1 ×3, SC3 ×4, SC1 ×4, `HistoryStrongNeckClassSupply`,
  `HistoryStrongNeckDepthInduction`) building; a real-module-name overlay is impossible (Lean resolves
  the package root `DifferentialGeometry/` at the first search-path entry), hence the rename scheme.
- shared build now HAS `TracedRegionBackwardStep.olean`; `TerminalProductSplitting.olean` still absent.

## Findings before the statements (failures first)

1. **The window limit needs a curvature bound that is UNIFORM in the radius.** SC5-1b's `hbound`
   (bounded `|Rm|` on the whole window, the strong-maximum-principle input of
   `TerminalRankOne`) cannot come from W1′'s per-radius bound `∃ B(k)`, nor from the class at depth
   (bounded curvature at bounded distance at negative times is what the induction is producing). It is
   Perelman's Harnack-type control, which the tree supplies through SC3-c: the slice maximum never
   increases along traces, so SC6-b's traced-region bound is `K = 8√3(1+φ1+φ0)·max Qup 1`, independent
   of the radius and of the depth once `Qup` (item 5) is uniform. SC6-c's `hsupply` premise, however,
   is stated as `∀ A T', … ∃ K` (radius-dependent). DEVIATION (recorded before proving): item 1 takes the
   uniform form `∃ K, ∀ A, ∀ᶠ n, isTracedRegion … (T/Rₙ) (K Rₙ)`; SC6-c's `hsupply` premise must be
   strengthened to `∃ K, ∀ A T' ≤ T, …` (its proof already produces exactly this `K`; the change makes
   SC6-c a stronger theorem). With the uniform `K`, W1′ is called with the CONSTANT schedule `τ k = T`
   (the survivor data's `a = t − T/Rₙ` then coincides with the traced region's), the gluing uses the
   general `exists_openClosed_solution_of_compatible_open_cover` with `c k = T(k+1)/(k+2)`, and the
   uniform bound on `h k n s` follows from trace uniqueness (`Subsingleton (BackwardPointTrace …)`,
   `Backward.lean:52`): the block's survivor maps `f j x` ARE the traced region's trace points.
2. **The window limit exists only on `(−T, 0]`.** W1′'s Shi margin (H14 (d)) leaves no room at the
   bottom slice, so the supply produced from the depth-`T` limit covers slices
   `v ∈ [tₙ − T'/Rₙ, tₙ]` for any fixed `T' < T`, not the closed bottom `T' = T` (a sequence of bad
   slices `sᵢ → −T` has no limit slice). DEVIATION: SC6-c's induction must stagger the depths (traced at
   depth `T` ⇒ supply on depth `≤ T − η` ⇒ SC6-b at `T − η` ⇒ traced at `T − η + δ`; with the fixed
   margin `η = δ/2` the depth still grows by `δ/2` per step) — a one-line change of SC6-c's `hsupply`
   binder (`(t n : ℝ) − T / R n ≤ v` becomes `(t n : ℝ) − T' / R n ≤ v` for a given `T' < T`, or the
   premise's depth becomes `T + η`). Item 5 (`T = 0`, top slice only) is unaffected: the top slice IS
   the limit's time-0 slice, where W1′'s canonical data live.
3. **Item 5 is XA4's generic theorem plus SC6-b at `T = 0`.**
   `ObservedHistory.exists_subseq_scalar_le_on_normalized_balls_of_depth_schedule`
   (`Surgery/Topology/TracedRegionTimeZeroScalarBound.lean:124`, XA4, uncommitted) already proves: traced
   regions at radius `k+3` with ANY depth schedule `τ k ∈ (0,1]` + κ + pinching + class witnesses with
   accuracy `≤ crossingNeckAccuracy` ⇒ a subsequence and ONE `C₀` bounding the scalar on the
   normalized `A`-balls for EVERY `A` (time-0 limit, `Rm ≥ 0`, B6 neck alternatives at `s = 0`, Transfer:440,
   transfer back). The lead's route (line ⇒ Cheeger–Gromoll ⇒ capture ⇒ `N ≈ S²` compact) is NOT
   needed for the bound: Transfer:440's third alternative (whole component bounded) absorbs the
   positive/round witnesses, and the cap witnesses contribute their tube neck (alternative 2). What T4′
   adds is only the depth schedule: SC6-b (`isTracedRegion_of_forall_neckAlternative`) at `T = 0` with
   the per-radius top-ball bounds `Qlow(A) ≤ R ≤ Qup(A)` (SC7's shape) and the top-slice neck supply
   (SC2-b's shape) gives traced regions of normalized depth `(10·Qup(A))⁻¹` at every radius. So item 5 is
   two thin bricks (SC8-5a: SC6-b at `T = 0` per radius; SC8-5b: the wrapper with `τ k := min 1 (θ(k+3))`).
   The bound is along a SUBSEQUENCE (the limit depends on it); T4′'s contradiction argument is free to
   pass to it; SC6-c's `hball` is then applied to `H ∘ ψ`.
4. **Witness capture at a slice is done in the local-pull currency, not through
   `PointedRiemannianConvergenceMaps` at the slice.** SC5-2b consumes canonical convergence maps at one
   fixed slice; the window limit has them only at time 0 (W1′'s `F`), while at a slice `s` it has the
   `hconv` clause (convergence of `localPullMetric (h k n s) (φ k j)` to `(G s)|V k` on compacts of
   `V k`, reference `P.metric|V k`) and, for VARYING slices `sᵢ → s` (SC6-c's `∀ v`), XP2′'s shifted
   convergence `tendsto_metricDerivNormSupOn_localPull_shifted_of_time_lipschitz_on_window`. Building
   convergence maps at every slice would be a diagonal construction; the tree's pattern (B9, XP2′'s
   `NeckAlternativesLocalPullCompact`) is the local-pull one. Hence SC8-4a: SC5-2a's ball form with the
   product chart BUILT from an injective local diffeomorphism `Fm : V → M` (`V` an open of the limit
   slice), the product structure `e : N × ℝ ≃ Y` of the limit slice and `C²`-closeness of
   `localPullMetric g Fm` to `gY|V` on a compact ball — capture by
   `ball_subset_image_of_metric_lower_on_opens` (`OpenEmbeddingBallCapture:52`, `L = √2` from
   `C⁰`-closeness `≤ 1/8`), the chart from `toOpensDiffeo` (`e` on `O := e⁻¹' V`) composed with
   `diffeomorphOntoImage Fm`, closeness transported by `metricDerivNorm_pullbackCross`.
   The reference of the closeness must be the limit slice metric `gY|V` itself (SC5-2a's reference is the
   product metric); `hconv`'s reference is `P.metric|V k`. Reference change on a compact set with
   arbitrary constants: `exists_manifold_uniform_metric_deriv_norm_reference_bound` (the `eps ≤ 1`
   swap lemmas do not apply since `G s` and `G 0` are not within factor 2). Recorded as the plumbing risk
   of SC8-4b.
5. **The shifted-convergence lemma's one-sided hypothesis.** XP2′'s lemma assumes `σ n ≤ s`; a bad
   slice sequence can converge to `s` from above. Its proof uses the hypothesis only for
   `σ (f (ψ i)) ≤ 0`; SC8-4b carries a private copy with `∀ n, σ n ≤ 0` (DEFERRED MERGE into
   `LocalFlowLimitWindowTransfer.lean`: weaken `hσs : ∀ n, σ n ≤ s` to `∀ n, σ n ≤ 0`).
6. **Simple connectivity (item 3): what the tree supports.** Cheeger–Gromoll on `P.M` itself at time 0
   (`cheeger_gromoll_splitting`, no simple connectivity) gives `P.M ≅ N₀ × ℝ`; SC5-1a
   (`curvatureOperatorImageAt_finrank_eq_one_of_line`, on `M` with `[ConnectedSpace M]`) gives rank
   one everywhere at time 0, hence `K_{N₀} > 0` everywhere; then `SimplyConnectedSpace N₀` needs
   Synge (`Geometry/Comparison/Synge/Even.lean`, compact orientable even-dimensional `K > 0`; needs
   the orientation of `N₀`, from `P.M`'s (`PointedLimitOrientation.lean`) through the product) in the
   compact case and Gromoll–Meyer (`Soul/PositiveEuclidean.lean`, stated for a `MetricSpace`-instance
   manifold with `IsRiemannianManifold`) in the noncompact case, then `SimplyConnectedSpace (N₀ × ℝ)`
   and transport along `Phi₀`. The deck-descent alternative (`Geometry/Metric/UniversalCover/DeckProduct*`,
   `AncientCylinderDeckClassification`) is the ancient lane's heavy route. Item 3 is delivered LAST as
   the strongest statement the tree supports (see the item-3 section below); until it closes, SC8-4b
   takes the product structure of the window limit as SC5-1b's OUTPUT applied to the limit under the
   simple-connectivity hypothesis it needs, and the assembly theorem records `SimplyConnectedSpace P.M`
   as the single remaining input (never packaged as a free hypothesis of a public consumer beyond the
   assembly).
7. **`Rm`-norm bound on the limit window** (SC5-1b's `hbound`): `MetricCPConvergenceOn.tendsto_normSq_metricRm04At`
   (`Geometry/Metric/Convergence/Curvature/TensorConvergence.lean:60`) transports the approximants'
   uniform `curvDerivNormSq 0 ≤ K²` (Finding 1) to every limit slice; no "`Rm ≥ 0 ⇒ |Rm| ≤ cR`" lemma
   exists in the tree and none is needed.

## Statements (recorded BEFORE proving; each elaborated with `sorry` first)

**SC8-5a** (`Surgery/Topology/HistoryStrongNeckTopSliceTracedRegion.lean`, ns
`…Surgery.Topology.RetainedCoreHistory`): SC6-b at `T = 0`, per radius, along the sequence:
```lean
theorem exists_eventually_isTracedRegion_of_forall_neckAlternative_at_top
    {P₀ : ℕ → OrientedThreeStage.{u}} (H : ∀ n, RetainedCoreHistory (P₀ n)) (t) (y) (R : ℕ → ℝ)
    (hRlim : Tendsto R atTop atTop) {phi} (hphi) (hpinch : ∀ n, (H n).EventSlabsPinched phi)
    (hlast : ∀ n, activeStage (t n) = last → ∃ h, PhiAlmostNonnegative ((H n).finalSlab h).flow … phi)
    (htop : ∀ n, (H n).time (activeStage (t n)) < t n) {ε ε₁ C1 C2 : ℝ} {qcan : ℕ → ℝ}
    (hε₁ : ε₁ ≤ 1 / 30000) (hq : ∀ c > 0, ∀ᶠ n, qcan n < c * R n)
    (hclass : ∀ n, (H n).EventSlabsStronglyCanonical ε ε₁ C1 C2 (qcan n) last)
    (hterm : ∀ n, activeStage (t n) = last → ∃ s G, t n < s ∧ (G agrees with the stage metric on
      [time last, t n]) ∧ (H n).StronglyCanonicalBefore last G ε ε₁ C1 C2 (qcan n) s)
    (hball : ∀ A > 0, ∃ Qlow Qup, 0 < Qlow ∧ ∀ᶠ n, ∀ x ∈ ball(y n, A/√Rₙ), Qlow Rₙ ≤ R x ∧ R x ≤ Qup Rₙ)
    (hneck : ∀ A c, 0 < A → 0 < c → ∀ᶠ n, ∀ x ∈ ball(y n, A/√Rₙ), c Rₙ ≤ R x →
      ∀ W : SpatialCanonicalWitness (stageMetric (activeStage (t n)) (t n)) ε C1 C2 x,
        W.capTubeHasNeckChart ε → ∃ nk, W.alternative = .neck nk) :
    ∀ A : ℝ, 0 < A → ∃ θ K : ℝ, 0 < θ ∧ 0 ≤ K ∧ ∀ᶠ n in atTop,
      (H n).toHistory.isTracedRegion (t n) (y n) (A / √Rₙ) (θ / Rₙ) (K * Rₙ)
```
(`θ = (10·Qup(A))⁻¹`, `K = 8√3(1+φ1+φ0)·max Qup(A) 1`; the top-slice trace is the singleton, so SC6-b's
supply reduces to `hneck` with `c := Qlow`.)

**SC8-5b** (`Surgery/Topology/TracedRegionTimeZeroUniformBound.lean`, ns `…ObservedHistory`): the
wrapper of XA4's theorem for radius-dependent positive depths:
```lean
theorem exists_subseq_scalar_le_on_normalized_balls_of_forall_radius_positive_depth
    (H t y R hR hRlim)
    (htraced : ∀ A : ℝ, 0 < A → ∃ θ K : ℝ, 0 < θ ∧ 0 ≤ K ∧ ∀ᶠ n in atTop,
      (H n).isTracedRegion (t n) (y n) (A / √Rₙ) (θ / Rₙ) (K * Rₙ))
    {κ ρ} (hκ hρ) {t₀} (hsliver) (hnc) {Phi} (hPhi) (hpinch) {eps C1 C2 Cq} (heps0 : 0 < eps)
    (heps : eps ≤ crossingNeckAccuracy) {qs} (hqs : ∀ n, qs n ≤ R n * Cq) (hwit) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ Qup : ℝ, 1 ≤ Qup ∧ ∀ A : ℝ, 0 < A → ∀ᶠ i in atTop,
      ∀ x ∈ ball(y (ψ i), A/√R(ψ i)), R x ≤ Qup * R (ψ i)
```
(`τ k := min 1 (θ (k+3))`, `mono_depth`.) SC6-c's `hball` (upper half, uniform `Qup`) on `H ∘ ψ` is
SC8-5b's conclusion with SC8-5a as its `htraced`; the lower half stays radius-dependent (SC7-2a's
gradient bound), which SC6-c allows.

**SC8-1** (`Surgery/Topology/TracedRegionWindowLimit.lean`, ns `…ObservedHistory`): the finite-window
B13. Binders: `H t y R hR hRlim {T} (hT : 0 < T)`,
`htraced : ∃ K, 0 ≤ K ∧ ∀ A, 0 < A → ∀ᶠ n, isTracedRegion (t n) (y n) (A/√Rₙ) (T/Rₙ) (K Rₙ)`,
`{κ ρ} hκ hρ {t₀} hsliver hnc {Phi} hPhi hpinch` exactly as W1′. Conclusion, with `X` the rescaled
top-slice sequence (B13's `let`): `∃ W h`, W1′'s per-`k` block with the constant schedule `τ k = T`
(solution on `closed (−T) 0`, current-slab identity, survivor maps `f` with crossings, endpoint and
pull-back identities on `Icc (−T) 0`, approximant κ-test), W1′'s Lipschitz clause on
`Icc (−(T(k+1)/(k+2))) 0`, the UNIFORM curvature bound
`∀ k, ∀ᶠ n, ∀ s ∈ Icc (−T) 0, ∀ x : W k n, curvDerivNormSq 0 (h k n s) x ≤ K²` (and the scalar bound
`≤ 9|K|`), the `e²` clause, the rescaled pinching clause, the limit-ready κ-test; then `f, P, F`
(canonical `MetricConvergenceData`), `MetricComplete P`, `ConnectedSpace P.M`, `hballF`, `V N hV hVF φ
hφ hφF`, and `G : ℝ → SmoothRiemannianMetric ThreeModel P.M` with `G 0 = P.metric`, `IsSolutionOn` on
`openClosed (−T) 0`, `Rm ≥ 0` on `Ioc (−T) 0`, completeness of every slice on `Ioc (−T) 0`,
`∀ s ∈ Ioc (−T) 0, ∀ x, normSq0S (G s) x 4 (metricRm04At (G s) x) ≤ K²` (hence bounded scalar), the
parabolic κ clause `∀ ρ' > 0, ParabolicallyKappaNoncollapsedBelowScale … (κ/250) ρ'`, and `ψ` with the
convergence clause `metricDerivNormSupOn K p (localPullMetric (h k (f (ψ i)) s) (φ k (ψ i) hi)) ((G s)|V k)
(P.metric|V k) < η` on `Icc (−(T(k+1)/(k+2))) 0`.

**SC8-2** (`Surgery/Topology/ScaledPointedLimitLine.lean`, ns `…ObservedHistory`): the line from a
separating set on the approximants, for ANY canonical convergence of the rescaled top slices:
```lean
theorem exists_line_of_scaled_pointed_limit_of_separating_set (H t y R hR) {f}
    (F : PointedRiemannianConvergenceMaps X P f) (C : MetricConvergenceData F) (hcan) (hPc) (hconn)
    (S V W : ∀ n, Set carrier) (hV hW hVW) {B} (hB : 0 ≤ B) (hS : S n within B/√Rₙ of y n)
    (hpoints : ∀ A > B, ∀ᶠ n, closedBall(y n, 3A/√Rₙ) \ S n ⊆ V n ∪ W n ∧ ∃ p ∈ V n, ∃ q ∈ W n, A/√Rₙ ≤ d ≤< 3A/√Rₙ) :
    ∃ line : ℝ → P.M, ∀ a b, riemannianEDistOf P.metric (line a) (line b) = ENNReal.ofReal |a - b|
```
(SC4-b's block verbatim; SC4-b becomes its instance at B13's `F` — deferred merge.) The window limit's
time-0 line is this theorem at SC8-1's `F`.

**SC8-4a** (`Perelman/CanonicalNeighborhood/LocalPullProductNeck.lean`, ns `…FiniteHorn`): SC5-2a in
the local-pull currency:
```lean
theorem SpatialCanonicalWitness.exists_localNeck_of_localPull_product_close
    {M Y : Type*} [3-manifolds] (g : SmoothRiemannianMetric I3 M) (gY : SmoothRiemannianMetric I3 Y)
    {V : Opens Y} {Fm : V → M} (hFm : IsLocalDiffeomorph I3 I3 ∞ Fm) (hinj : Injective Fm)
    (h : SmoothRiemannianMetric J N) (hdim : finrank F = 2) (e : (N × ℝ) ≃ₘ Y)
    (hemetric : pullbackMetricCross gY e = h.prod (euclideanMetric)) (z : V) {r η : ℝ} (hr : 0 < r)
    (hη : η ≤ 1/8) (hcpt : IsCompact (closedBall_{gY}(z.val, r))) (hsub : closedBall_{gY}(z.val, r) ⊆ V)
    (hclose : ∀ w : V, w.val ∈ closedBall_{gY}(z.val, r) → ∀ m ≤ 2,
      metricDerivNorm m (localPullMetric g Fm hFm) (gY.restrictOpen V) (gY.restrictOpen V) w ≤ η)
    {epsc eps C1 C2} (W : SpatialCanonicalWitness g epsc C1 C2 (Fm z)) (hW : W.capTubeHasNeckChart eps)
    (heps : eps ≤ 1/1000) (hsmall : 720 * η < C2⁻¹ * R_g(Fm z) / 16)
    (hrad : 2 * √2 * (C1 / √R_g(Fm z)) < r) :
    ∃ neck : SpatialLocalNeck g epsc (Fm z) W.domain.carrier, W.alternative = .neck neck
```

**SC8-4b** (`Surgery/Topology/TracedRegionWindowProductNeck.lean`, ns `…ObservedHistory`): the per-layer
supply from a product structure of the window limit at every slice. Inputs: SC8-1's data for the
subsequence (the block, `f P F` canonical, `V N hV hVF φ hφ hφF`, `G`, the convergence clause, the
Lipschitz clause), the product data `∀ s ∈ Icc (−T') 0, ∃ N h e, pullbackMetricCross (G s) e = h.prod dz²`
(ONE `N`, `e` for all `s` as SC5-1b gives, or per slice), completeness of the slices, `0 ≤ T' < T`;
conclusion in SC6-c's supply shape along the subsequence:
```lean
    ∀ A c : ℝ, 0 < A → 0 < c → ∀ᶠ i in atTop, ∀ x ∈ ball(y (f (ψ i)), A/√R), ∀ v, t − T'/R ≤ v →
      ∀ hvt : v ≤ t, time (activeStage v) < v → ∀ B : BackwardPointTrace … x,
        c * R ≤ R_v(B.point) → ∀ W : SpatialCanonicalWitness (stageMetric (activeStage v) v) ε C1 C2 (B.point),
          W.capTubeHasNeckChart ε → ε ≤ 1/1000 → ∃ nk, W.alternative = .neck nk
```
Route: contradiction ⇒ bad subsequence `(xᵢ, vᵢ, Bᵢ, Wᵢ)`, `sᵢ := R(vᵢ − tₙ) ∈ [−T', 0]` ⇒ convergent
subsequence `sᵢ → s`; `Bᵢ.point = f_j(xᵢ)` by trace uniqueness; `xᵢ = φ k (ψ i) zᵢ` with `zᵢ` in a
compact ball of `V k` (inverse capture at time 0); `zᵢ → z`; the shifted convergence (Finding 5) at `s`
on a compact neighbourhood; reference change (Finding 4); SC8-4a with `Fm := f_j ∘ φ` at the scaled stage
metric (`W.scaleMetric Rₙ`, SC5's `exists_neck_of_scaleMetric`).

**SC8-3** (item 3; file and statement recorded when started): the strongest supported statement is
planned as `SimplyConnectedSpace P.M` from (a) Cheeger–Gromoll at time 0, (b) rank one ⇒ `K_{N₀} > 0`,
(c) orientability of the factor, (d) Synge / Gromoll–Meyer, (e) product transport; each piece is logged
with its supplier before proving.

## Proof status (incremental)
- scratch chains A (12 modules) and B (13 modules) built as `SC8.*` (all exit 0; `TerminalProductSplitting`
  compiled from source, 35 s). Script: `sc8/cc.sh emit|check`, `sc8/chain.sh`.
- SC8-5b `Surgery/Topology/TracedRegionTimeZeroUniformBound.lean` — PROVED as stated (wrapper of XA4's
  `exists_subseq_scalar_le_on_normalized_balls_of_depth_schedule` with `τ k := min 1 (θ (k+3))`,
  `isTracedRegion.mono_depth`); clean compile (46 s, zero output).
- SC8-5a `Surgery/Topology/HistoryStrongNeckTopSliceTracedRegion.lean` — PROVED as stated (SC6-b at
  `T = 0`; `Qup > 0` from the centre of the ball; the top-slice trace is the singleton so the supply is
  `hneck` with `c := Qlow`; `θ = (10·Qup)⁻¹`, `K = 8√3(1+φ1+φ0)·max Qup 1`, `isTracedRegion.mono_bound`
  once `Rₙ ≥ 1`); clean compile (46 s, zero output). Together: item 5 = SC8-5a ∘ SC8-5b (uniform `Qup`
  along a subsequence from per-radius bounds, the top-slice neck supply and the class). No age hypothesis.
- SC8-2 `Surgery/Topology/ScaledPointedLimitLine.lean` — PROVED as stated (SC4-b's block; binder
  `StrictMono f` added since the convergence maps do not carry it; imports `HistoryRestriction`,
  `SeparatingSegments`, `DistanceScaling`, `Ball`, `CompactMinimizer`, `Continuity`, `SeparatedSidePoint`,
  `Compactness/Construction`); clean compile (18 s, zero output). DEFERRED MERGE: SC4-b
  (`TracedRegionLineNeck.lean`) is this theorem at B13's `F` followed by the κ-solution neck transport.
- SC8-1 `Surgery/Topology/TracedRegionWindowLimit.lean` — PROVED as stated with the statement refined to
  `{K : ℝ} (hK : 0 ≤ K) (htraced : ∀ A, 0 < A → ∀ᶠ n, isTracedRegion … (T/Rₙ) (K Rₙ))` (the uniform
  bound is the theorem's `K`, not an existential); the curvature clauses are stated as
  `curvDerivNormSq 0 (h k n s) x ≤ K²` (approximants, all `s ∈ Icc (−T) 0`) and
  `curvDerivNormSq 0 (G s) x ≤ K²` (limit, all `s ∈ Ioc (−T) 0`) — this is exactly SC5-1b's `hbound`
  after `curvDerivNormSq_zero_eq_normSq0S` (private bridge, `curvCovDeriv g 0 = metricRm04 g` by `rfl`).
  Route as planned: W1′ with `τ k = T`, `exists_openClosed_solution_of_compatible_open_cover` with
  `c k = T(k+1)/(k+2)` (private `depth_schedule_facts`), `G 0 = P.metric` by `ext_inner`, the convergence
  clause rewritten with the restriction identity, `curvatureOperator_nonnegative_of_local_pinching_limit_on_window`,
  `complete_at_earlier_time_of_ricci_nonnegative`, the κ theorem of XP3 with `radii n = ρ√Rₙ`
  (`Real.tendsto_sqrt_atTop`), the uniform bound by trace uniqueness (`Subsingleton.elim` against the
  trace `⟨fun j => fs j x, hlast x, hcross ⋯⟩` built from the block's survivor maps; `mem_Icc_of_mem_window`
  and `riemannianBallOf_scaleMetric_eq` by `open private` from the committed `TracedRegionAncientLimit`),
  and its transport to the limit by `MetricCPConvergenceOn.tendsto_normSq_metricRm04At` + `le_of_tendsto`.
  Three private local instances (`SigmaCompactSpace`/`MeasurableSpace`/`BorelSpace` on `Opens`) copied
  as in B13/W1′/SC6-d (deferred merge into a shared home). Clean compile (41 s, zero output).
- SC8-4a `Perelman/CanonicalNeighborhood/LocalPullProductNeck.lean` — PROVED as stated. Chart:
  `O := e⁻¹' V`, `ι : O ≃ₘ V := (toOpensDiffeo e.toPartialDiffeomorph _).trans (diffeomorphOfOpensEq _)`
  (private `diffeomorphOfOpensEq (h : U₁ = U₂) := h ▸ Diffeomorph.refl`, with `_val` and `mfderiv_` lemmas by
  `subst`), `q := Fm ∘ ι` (injective local diffeomorphism, `localDiffeomorph_isSmoothEmbedding_of_injective`),
  `Φ : O ≃ₘ V'` from `exists_diffeomorph_onto_range_pullback_eq_immersionInducedMetric`; the two `ext_inner`
  identities `pullbackMetricCross (g|V') Φ = pullbackMetricCross (localPullMetric g Fm) ι` (chain rule) and
  `(h.prod dz²)|O = pullbackMetricCross (gY|V) ι` (`hemetric`, `mfderiv_toOpensDiffeo`), naturality
  `metricDerivNorm_pullbackCross`, capture by `ball_subset_image_of_metric_lower_on_opens` with `L = √2`
  from `inner_bounds_of_metricDerivNorm_le` at order 0 (`η ≤ 1/8`). Clean compile (33 s, zero output).
  CORRECTION to Finding 4: the reference change for SC8-4b is `MetricCInfConvergenceOnCompacts.change_reference`
  (`Geometry/Metric/Convergence/CovariantDerivative/Norm/ReferenceChange.lean:199`): convergence on
  compacts is reference-independent, so the slice convergence with reference `P.metric|V k` gives the one
  with reference `(G s)|V k` directly; no comparability constants are needed.
- Lead delta received: SC7 delivered (`OPUS_FILL_LOG_SC7.md`): `eventually_terminal_scalar_bound_at_distance_of_chain_backward_traces`
  (SC7-1c, `L`-balls: `R_L ≤ Q(A)·R_L(xₙ)` + compactness) and SC7-2c (core frontier far). They are the
  per-radius inputs of SC8-5a's `hball` (upper half; transported to the slices `τₙ` by SC7-3b and
  SC1-b's slice comparison) and of SC8-2's `hpoints` (through SC4-c); the uniform `Qup` is SC8-5a ∘ SC8-5b.
- SC8-4b `Surgery/Topology/TracedRegionWindowProductNeck.lean` — PROVED as stated (statement refined:
  the non-event hypothesis on `v` is dropped, the conclusion is along `f ∘ ψ`, the product data is ONE
  `Nf`, `hN : ℝ → SmoothRiemannianMetric (𝓡 2) Nf`, `Phi : Nf × ℝ ≃ₘ P.M` with
  `pullbackMetricCross (G s) Phi = (hN s).prod dz²` for all `s ∈ Icc (−T') 0`, exactly SC5-1b's output
  shape; inputs are SC8-1's block/limit clauses verbatim). Route: extraction of the bad subsequence
  (`Filter.extraction_of_frequently_atTop`, `push Not`), convergent slices (`isCompact_Icc.tendsto_subseq`),
  the shift making `N k ≤ ψ (σ (ρ m))` hold everywhere (no `dite`), the reindexed shifted-convergence copy
  (private `tendsto_localPull_shifted_of_subseq`, Finding 5), `change_reference`, inverse capture at
  time 0 (`pointed_metric_eventually_inverse_ball_capture`, buffer `2A < 2A+1`), the compact-in-ball
  lemma (private `exists_subset_riemannianClosedBallOf_of_isCompact`, via `riemannianEDistOf_ne_top_iff`),
  trace identification with the block's survivor maps (`BackwardPointTrace.restrictFirst`,
  `Subsingleton.elim`), SC8-4a on `Fm := fs j ∘ φ k (ψ (σ (ρ m)))` with the scaled stage metric, and
  SC5's `exists_neck_of_scaleMetric`. Clean compile (61 s, zero output; `push_neg` is deprecated in this
  toolchain, `push Not` used).

**SC8-3** (`Geometry/Neck/LineNeckSimplyConnected.lean`, ns `…FiniteHorn`; recorded before its first
compile): the strongest supported form of item 3 is a generic theorem, not a limit-specific one:
```lean
theorem SpatialNeck.simplyConnectedSpace_of_line (g : SmoothRiemannianMetric I3 M)
    (hg : RiemannianMetricComplete g) (hRic : ∀ x v, 0 ≤ ricciTensor g x v v) {gamma}
    (hline : ∀ s t, riemannianEDistOf g (gamma s) (gamma t) = ENNReal.ofReal |s - t|)
    {eps p} (nk : SpatialNeck g eps p) (heps : eps ≤ 1 / 1000) : SimplyConnectedSpace M
```
(`M` a connected 3-manifold). Route: `cheeger_gromoll_splitting` on `M` itself (no simple
connectivity), its inner-product identity converted to `pullbackMetricCross g Phi = h.prod dz²`
(`prod_inner`, `euclideanMetric_inner`, `RCLike.inner_apply`), the `⊤`-opens chart
`ι : ⊤ ≃ₘ ⊤` from `toOpensDiffeo Phi.toPartialDiffeomorph` (private opens-equality diffeomorphism as in
SC8-4a), `SpatialNeck.exists_diffeomorph_graph_in_product_chart` at level `s = 0` with `η = 0`
(`metricDerivNorm_self`), which returns `ψ : N ≃ₘ Sphere 2`, then `sphereTwoSimplyConnectedSpace`,
`HomotopyEquiv.simplyConnectedSpace` along `ψ`, the contractible factor (`CylindricalModel`'s
argument for `N × ℝ`) and `Phi`. For the window limit: `Ric ≥ 0` at time 0 is SC8-1's cone clause
through `algebraicCurvatureOperatorNonnegativeCone_le_sectionalNonnegativeCone` +
`ricciTensor_nonneg_of_sectionalNonnegative`, the line is SC8-2, and the neck of `P.metric` at some
point is the remaining assembly input: from the top-slice necks (SC2-b) by the time-0 neck-alternative
transfer (B9w `neck_alternatives_of_local_flow_limit_on_window` at `s = 0`, whose third alternative
`CompactSpace P.M` is excluded by the line; its threshold `4·max q 1 < R(x)` needs a limit point of
scalar `> 4`, i.e. the assembly rescales by a constant or uses a point of the limit above that
threshold — recorded as the one remaining interface choice for T4′).
- `#print axioms` (scratch file importing the six `SC8.*` modules, deleted after use):
  `exists_window_pointed_flow_limit_of_isTracedRegion`, `exists_line_of_scaled_pointed_limit_of_separating_set`,
  `exists_subseq_scalar_le_on_normalized_balls_of_forall_radius_positive_depth`,
  `exists_eventually_isTracedRegion_of_forall_neckAlternative_at_top`,
  `SpatialCanonicalWitness.exists_localNeck_of_localPull_product_close`,
  `eventually_forall_neckAlternative_of_window_product_structure`: all `[propext, Classical.choice, Quot.sound]`.
- SC8-3: `Geometry/Comparison/Splitting/IntrinsicLine` (committed) has NO olean in the shared build, nor
  have `Busemann`, `AffineFunctionSplitting`, `AffineZeroLevelCompleteness`; compiled as scratch modules
  (chain D) before SC8-3's check. An acceptance build must build them first (as for
  `TerminalProductSplitting`).

## Deliverables (all new, uncommitted, not in the root aggregate)
| File | Lines | Declarations | Uncommitted deps |
|---|---|---|---|
| `Surgery/Topology/LocalFlowLimitBaseScalar.lean` | 95 | `FiniteHorn.metricScalarAt_basepoint_eq_of_local_flow_limit_on_window` (+ one `Opens` instance) | — (committed deps only) |
| `Surgery/Topology/TracedRegionWindowLimit.lean` | 416 | `ObservedHistory.curvDerivNormSq_zero_le_of_survivor_maps_of_isTracedRegion`, `ObservedHistory.normSq0S_metricRm04At_le_of_local_flow_limit_on_window`, `ObservedHistory.exists_window_pointed_flow_limit_of_isTracedRegion` (+ private `depth_schedule_facts`, `curvDerivNormSq_zero_eq_normSq0S`, three `Opens` instances) | `LocalFlowLimitBaseScalar`; XP3 `TracedRegionLocalLimitDepthSchedule`, `LocalPointedFlowLimit`, `OpenClosedGluing`, `LocalPointedFlowLimitNoncollapsing`; XP2′ `LocalFlowLimitWindowTransfer` |
| `Surgery/Topology/ScaledPointedLimitLine.lean` | 138 | `ObservedHistory.exists_line_of_scaled_pointed_limit_of_separating_set` | SC4 `Geometry/Metric/Distance/SeparatedSidePoint` |
| `Surgery/Topology/TracedRegionTimeZeroUniformBound.lean` | 59 | `ObservedHistory.exists_subseq_scalar_le_on_normalized_balls_of_forall_radius_positive_depth` | XA4 `TracedRegionTimeZeroScalarBound` (→ `LocalFlowLimitShiftedConvergence`, W1′) |
| `Surgery/Topology/HistoryStrongNeckTopSliceTracedRegion.lean` | 112 | `RetainedCoreHistory.exists_eventually_isTracedRegion_of_forall_neckAlternative_at_top` | SC6 `HistoryStrongNeckDepthInduction` (→ SC3-e chain, SC1 chain, SP1 chain) |
| `Perelman/CanonicalNeighborhood/LocalPullProductNeck.lean` | 184 | `SpatialCanonicalWitness.exists_localNeck_of_localPull_product_close` (+ private opens-equality diffeomorphism and two lemmas) | SC5 `SpatialCanonicalWitnessProductChart` |
| `Surgery/Topology/TracedRegionWindowProductNeck.lean` | 641 | `ObservedHistory.eventually_forall_neckAlternative_of_window_product_structure` (+ private `exists_subset_riemannianClosedBallOf_of_isCompact`, `tendsto_localPull_shifted_of_subseq`, `depth_schedule_exists_gt`, one `Opens` instance) | `LocalPullProductNeck`; SC5 `PointedProductLimitNeck`; XP2′ `LocalFlowLimitWindowTransfer` |
| `Geometry/Neck/LineNeckSimplyConnected.lean` | 191 | `SpatialNeck.exists_diffeomorph_sphere_of_product_structure`, `not_compactSpace_of_line` (any model), `SpatialNeck.simplyConnectedSpace_of_line`, `SpatialNeck.simplyConnectedSpace_of_line_of_scaleMetric` (+ the same three private opens-equality helpers) | — (committed deps only; `IntrinsicLine` chain unbuilt in the shared build) |
(paths under `Geometry/Flow/RicciFlow/` except the last.) Compiles: each file with the standard linter
set through scratch modules `SC8.*`: zero output. Acceptance order: `LocalFlowLimitBaseScalar`,
`LocalPullProductNeck` (after SC5's `SpatialCanonicalWitnessProductChart`), `ScaledPointedLimitLine`
(after SC4's `SeparatedSidePoint`), `LineNeckSimplyConnected` (after the committed-but-unbuilt chain
`AffineZeroLevelCompleteness`, `AffineFunctionSplitting`, `Busemann`, `IntrinsicLine` under
`Geometry/Comparison/Splitting/`, all compiled here as scratch modules); `TracedRegionWindowLimit`
after `LocalFlowLimitBaseScalar` and XP3/XP2′; `TracedRegionTimeZeroUniformBound` after XA4;
`HistoryStrongNeckTopSliceTracedRegion` after SC6; `TracedRegionWindowProductNeck` last.

## Deviations (with reasons)
1. Item 1 takes the traced-region bound UNIFORM in the radius (Finding 1); SC6-c's `hsupply` premise must
   expose it (`∃ K, ∀ A T' ≤ T, …`); SC6-c's proof already has it (`K = 8√3(1+φ1+φ0)·max Qup 1`).
2. Item 4's supply covers `[tₙ − T'/Rₙ, tₙ]` for `T' < T` only (Finding 2: no limit slice at `−T`); SC6-c's
   induction must stagger the depth by a fixed fraction of its step (it then gains `δ/2` per step).
3. Item 5 is along a SUBSEQUENCE (the limit's bound depends on the subsequence); T4′'s contradiction
   argument passes to it and applies SC6-c to `H ∘ ψ`. The `Qlow(A)` half of `hball` stays radius-dependent.
4. Item 3 is delivered as the generic `SpatialNeck.simplyConnectedSpace_of_line` (Cheeger–Gromoll on `M`
   itself + the neck-graph diffeomorphism `N ≃ Sphere 2`), not as a limit-specific statement: its neck
   input is the assembly's (time-0 transfer of the top-slice necks; threshold caveat recorded above).
   Synge/Gromoll–Meyer are not used (no factor-orientation lemma in the tree; the noncompact case would
   need `MetricSpace`-instance plumbing).
5. SC8-4b drops SC6-c's non-event hypothesis on `v` (not needed for the capture) — a stronger theorem.
6. The reindexed shifted-convergence lemma is a private copy of XP2′'s with `∀ n, σ n ≤ 0` (Finding 5);
   the private opens-equality diffeomorphism helpers are duplicated in `LocalPullProductNeck` and
   `LineNeckSimplyConnected`; `depth_schedule_facts` is duplicated in SC8-1 and SC8-4b (the same facts are
   proved inside XP3's gluing corollary). DEFERRED MERGES: generalize XP2′'s lemma in place; one public
   `Diffeomorph.ofOpensEq` (e.g. `Topology/Manifold/Diffeomorph/OpensEq.lean`); the committed X5d
   `metricScalarAt_basepoint_eq_of_local_flow_limit` becomes the corollary `c k := k + 1` of
   `metricScalarAt_basepoint_eq_of_local_flow_limit_on_window`; one public depth-schedule
   lemma next to `OpenClosedGluing`; the three `Opens` local instances (now in six files) into a shared
   home; SC4-b as an instance of SC8-2; `curvDerivNormSq_zero_eq_normSq0S` public next to `curvDerivNormSq`.

## What the T4′ final assembly still lacks (after SC1–SC8)
1. SC6-c′: the staggered depth induction consuming SC8-4b — a NEW file owned by lane T4A
   (`HistoryStrongNeckStaggeredDepthInduction.lean`, with the three interface deltas: the uniform `K`
   premise, the depth margin `T' < T`, and the subsequence→full-sequence extraction). The committed
   `HistoryStrongNeckDepthInduction.lean` is not edited by anyone.
2. The window product for SC8-4b: SC5-1b on SC8-1's `G` over `[−T', 0]` (its `hbound` is SC8-1's
   `curvDerivNormSq 0 (G s) x ≤ K²` after unfolding `rm04`; `hnonflat` from the base scalar `1` at time 0,
   X5d's `metricScalarAt_basepoint_eq_of_local_flow_limit`; the line is SC8-2 at SC8-1's `F`;
   `[SimplyConnectedSpace P.M]` is SC8-3 with a neck of `P.metric`).
3. The neck of the time-0 limit (SC8-3's input): the top-slice necks (SC2-b) through B9w
   (`neck_alternatives_of_local_flow_limit_on_window` at `s = 0`, third alternative excluded by the line);
   its threshold `4·max q 1 < R(x)` needs a limit point above scalar 4 (rescale the blow-up by a constant,
   or take the point from Transfer:440's alternatives) — an assembly choice.
4. SC8-5a's `hball` from SC7: the upper half from SC7-1c (`L`-balls) transported to the slices `τₙ`
   (SC7-3b + SC1-b's slice comparison), the lower half from SC7-2a at the slice; the top-slice neck supply
   `hneck` from SC2-b (`eventually_forall_neck_alternative_of_subset_hornHalfRange`) once the normalized
   ball lies in the horn half-range (SC7-2c). SC8-5b's class inputs are B13's (SC6-d's discharge map,
   `t₀ = s`, sliver from SC7-3c) with `eps ≤ crossingNeckAccuracy` added to SC4-d's tolerance list.
5. Everything is stated for `ObservedHistory` sequences; the assembly threads `(Hext n).toHistory`
   (XA4's `extendAt`) as in SC6-d, and reindexes by the subsequences of SC8-5b and SC8-1.

## Final status (after the watcher's cycles 1, 2 and 4)
- SC8-3 `Geometry/Neck/LineNeckSimplyConnected.lean` — PROVED as recorded, split into
  `SpatialNeck.exists_diffeomorph_sphere_of_product_structure` (a neck in a manifold with a global
  product structure `N × ℝ`, metric `h ⊕ dz²`, gives `N ≃ₘ Sphere 2`), `not_compactSpace_of_line`
  (any model, `[ConnectedSpace]`: a line has unbounded distance from its origin while a compact
  manifold has a farthest point, `riemannianEDistOf_ne_top`), `SpatialNeck.simplyConnectedSpace_of_line`
  (Cheeger–Gromoll on `M`, the sphere diffeomorphism, `HomotopyEquiv.simplyConnectedSpace` along
  `ψ`, the contractible factor and `Phi`) and the scaled corollary
  `SpatialNeck.simplyConnectedSpace_of_line_of_scaleMetric` (neck for `scaleMetric c g`, line and
  `Ric ≥ 0` for `g`: `edistOf_scale`, `ricciTensor_scaleMetric`, `RiemannianMetricComplete.of_lower`) —
  the form the assembly uses after rescaling the limit so that the neck threshold `4·max q 1 < R` is
  met (watcher (3)). The single-theorem draft exceeded the default heartbeat budget; the split (no
  option override) compiles clean (30 s, zero output).
- Watcher (1): SC8-1 now exports `(∀ n, R(tₙ, yₙ) = Rₙ) → metricScalarAt P.metric P.basepoint = 1`
  (X5d's route); the new generic `metricScalarAt_basepoint_eq_of_local_flow_limit_on_window`
  (`Surgery/Topology/LocalFlowLimitBaseScalar.lean`, 95 lines) is X5d with an arbitrary window
  schedule `c` (hypothesis `0 ≤ c 0`). `hnonflat` of SC5-1b then follows from
  `metricScalarAt_eq_zero_of_metricRm04At_eq_zero` (`Geometry/Curvature/Coordinates/RiemannTensorBridge.lean:64`)
  at the basepoint. With T4A's normalization `Rₙ := R_L(xₙ)` the hypothesis is discharged through
  SC7-3c's slice-scalar comparison or by normalizing at the slice scalar; the `Qlow`-half alternative
  (`Qlow ≤ R(base)`) would be the same lemma with the equality replaced by an inequality — not needed.
- Watcher (2): SC8-1's limit clause is now stated in SC5-1b's form
  `Tensor0SBundle.normSq0S (G s) x 4 (metricRm04At (G s) x) ≤ K ^ 2` (`S.base.rm04 t x` unfolds to it);
  the bridge `curvDerivNormSq_zero_eq_normSq0S` stays private (internal use only). SC8-1 is split into
  the two public lemmas `curvDerivNormSq_zero_le_of_survivor_maps_of_isTracedRegion` (one history: the
  block's survivor maps ARE the traced region's trace, `Subsingleton (BackwardPointTrace …)`) and
  `normSq0S_metricRm04At_le_of_local_flow_limit_on_window` (generic transport of a window curvature
  bound to every limit slice) plus the main theorem (per-declaration heartbeat budget; no override).
- Watcher (4): SC8-4b's import of XP2′'s `LocalFlowLimitWindowTransfer` noted (accepted by ACC14).
- Watcher (5): the unused `open …Surgery.Topology` of `LineNeckSimplyConnected.lean` is now the
  selective `open … (ThreeSpace Sphere)`; the duplicated opens-equality helpers are a deferred merge.
- FINAL `#print axioms` (scratch file importing all eight `SC8.*` modules, deleted): all thirteen
  public declarations (`exists_window_pointed_flow_limit_of_isTracedRegion`,
  `curvDerivNormSq_zero_le_of_survivor_maps_of_isTracedRegion`,
  `normSq0S_metricRm04At_le_of_local_flow_limit_on_window`,
  `metricScalarAt_basepoint_eq_of_local_flow_limit_on_window`,
  `exists_line_of_scaled_pointed_limit_of_separating_set`,
  `exists_subseq_scalar_le_on_normalized_balls_of_forall_radius_positive_depth`,
  `exists_eventually_isTracedRegion_of_forall_neckAlternative_at_top`,
  `SpatialCanonicalWitness.exists_localNeck_of_localPull_product_close`,
  `eventually_forall_neckAlternative_of_window_product_structure`,
  `SpatialNeck.simplyConnectedSpace_of_line`, `SpatialNeck.simplyConnectedSpace_of_line_of_scaleMetric`,
  `SpatialNeck.exists_diffeomorph_sphere_of_product_structure`, `not_compactSpace_of_line`):
  `[propext, Classical.choice, Quot.sound]`. Final compiles of every file: exit 0, zero output.
- Total: 8 new files, 1836 lines; no committed file modified (`git status`: only other lanes' logs);
  `git diff --check` clean for these files; no `sorry`, `axiom`, `nolint`, option override, comment,
  docstring or diagnostic command; nothing registered in `DifferentialGeometry.lean` (lead's job).
