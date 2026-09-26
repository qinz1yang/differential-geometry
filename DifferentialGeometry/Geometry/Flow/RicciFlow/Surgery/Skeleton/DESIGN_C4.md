# C4 design: `SpatialCanonicalContinuation` (2026-09-26)

This is a read-only design. No Lean file, git state or build was touched, and nothing below was
elaborated. Paths are relative to `DifferentialGeometry/Geometry/Flow/RicciFlow/`. It reads the
working-tree version of `Surgery/Topology/SpatialCanonicalContinuation.lean` after lane 28:
`C1s C2s Cs` come before `κ`, the floor `q₄` comes after `κ phi`, and `qcan ≤ qs ≤ Cs·qcan`.

## 0. Failures first

1. **C4 does not receive C3's output on `[t₀, t₀+η)`, so the old points are not a projection.**
   The leaf gets `CanonicalBefore` (strong witnesses, age ≥ τmin, threshold `qcan`, times in
   `(a, t₀)`), `Derivative/GradientBoundBefore t₀`, `SpatiallyCanonicalBefore t₀`, the
   `EventSlabs*` clauses for earlier slabs, pinching, and `NoncollapsedBefore κ ε t₀` (or the
   terminal pair). The conclusion needs witnesses at `t ∈ [t₀, t₀+η)`, including `t = t₀`, where
   none of the `Before` clauses say anything. So case (A) cannot come from `toSpatial` of a given
   witness, and case (B) cannot feed the bridge its `Gk.DerivativeBoundBefore C qcan t`.
   **Fix (interface I0, about 15 lines, no circularity):** add C3's own continuation output as a
   hypothesis, in both branches, right after the noncollapsing hypothesis:
   ```lean
   (∃ η : ℝ, 0 < η ∧ (H.toHistory.event j).incoming.DerivativeBoundOn Ctime qcan t₀ η ∧
      (H.toHistory.event j).incoming.GradientBoundOn Cgrad qcan t₀ η ∧
      (H.toHistory.event j).incoming.CanonicalOn ε C1 C2 qcan τmin t₀ η) →
   ```
   In the terminal branch use `G.` in place of `(H.toHistory.event j).incoming.`. Assembly
   (`CanonicalNeighborhoodsThroughSurgeryStrong.lean`, about lines 330 and 367): call
   `hS'.1 j … hn (hF'.1 j … hn)` and `hS'.2 s G … hn (hF'.2 s G … hn)`; the combiner
   `exists_boundsOn_spatiallyCanonicalOn` stays as it is. This is sound. C3's output at `t₀` uses
   only `Before t₀` hypotheses, and it is the other leaf's output, not C4's conclusion. It also
   removes C4's copy of the L10a/L10b problem (`DESIGN_C3B.md` failure 3). The derivative bound up
   to `t` then follows from `Before t₀ ∪ On[t₀, t)` (brick P0).
2. **Persistence of the induction's spatial witnesses cannot close case (C). FALSE as an induction
   step.** Two separate reasons:
   - (i) *Accuracy.* The spatial clause is at exactly `ε` and has no margin. Any forward
     persistence loses accuracy (`ε → 2ε`; the tree's `SpatialNeck.exists_transport_of_local_comparisons`
     needs the source at `neckModelTolerance α` to output `2α`), but the conclusion must be at the
     same `ε`. Chaining makes it worse: consecutive events can be arbitrarily close in time, so a
     young point traces into a young point of the previous slab, then into the one before.
     Configuration: on the Bryant steady soliton, a point `x` at fixed `x ∈ M` moves toward the tip
     (`∂ₜR > 0`), and the best neck accuracy at `x` strictly worsens in `t`. If it equals `ε` at
     `t₁`, then no `ε`-neck is centred at `x` for any `t > t₁`. "An ε-neck persists as an ε-neck
     for `t − t₁ ≤ c/R`" is therefore false.
   - (ii) *Time scale.* Young means `R(t − a) < τmin`, and `τmin` is C3's constant (at least
     `τ₀ ≥ δ⁻¹`, not small). After the event the trace needs normalized time up to `τmin`, plus the
     gap before `a` (the earlier clause is open at `a`). A neck pinches in normalized time about 1,
     so no `c(ε)/R` persistence reaches these points.

   **Case (C) must be produced fresh, by the crossing machine.** The machine is the
   uniform-κ model theorem on the traced common flow through the retained cores. That is exactly
   C3c's open core, so C4(C) and C3c should share one brick (X-core, §3).
3. **Cap-window constants versus `Θ → 1`.** `θcap` (and so the bridge's `Θ`) is chosen after `κ`,
   while `C1s C2s` come before `κ`. The standard-solution witness constant must therefore be
   uniform over all `T < 1`. As stated, `StandardSolution.exists_…_of_bounded_curvature` has `C`
   depending on `Θ`. This is repairable: by `exists_standard_scalar_lower_bound`
   (`StandardSolution/StandardTerminalBlowup.lean:61`, `c₀/(1−t) ≤ R`), a young standard point
   (`t·R < τ_std`) has `t ≤ Θ₂ := τ_std/(τ_std + c₀) < 1`, and the old ones are covered by the
   `Θ`-free `PartialStandardSolution.exists_spatialCanonicalWitness_with_cap_neck_charts_of_age`
   (`t < 1`). Brick S1 gives a `C_std(ε)` valid for every `T ∈ [0,1)`. It is still conditional on
   27c (`BoundedCurvatureSpatiallyCanonical` at `Θ₂`).
4. **Transporting a cap alternative needs a depth margin that the producers do not give.** Under a
   small metric perturbation, `10000/√R ≤ dist(x, tube)` survives only if the source satisfies it
   with a margin. This is the same `margin` as in E3's
   `LocalCap.exists_deep_transport_tolerance_of_metricComparisonOn`. 27a (projection of the
   standard `CanonicalWitness`), 27b and 27c currently output the bare inequality. **Fix:** their
   producers must expose `(10000 + 1)/√R ≤ dist` (the initial tip construction has `r ≥ 20000`, so
   it very likely has room), or a `deep`-with-margin field in a variant.
5. **No spatial transport API exists.** The only operations on `SpatialCanonicalWitness` are
   `enlargeConstants` and the projection `toSpatial`. E3 is for the time-dependent
   `CanonicalAlternative` and needs `IsSolutionOn`. There is no restriction, pushforward, scaling or
   metric-close transport, so bricks SW-R, SW-P, SW-S and SW-T (§4) are new.
6. **No uncovered points.** The partition (A) / (B) / (C) is exhaustive by `le_or_lt` and
   `by_cases CapWindowPoint`. Round and positive components arise only in (C), from compact
   κ-solution limits (review E item 7: three `S³` components). They never arise in (B), because the
   standard solution lives on non-compact `E3`, so `whole : U = connectedComponent x` with `U`
   compact is impossible there.

## 1. What C4 receives (current tree), and the partition

Fix a branch (event `j` with `a = time j.castSucc`, `Gk = (H.toHistory.event j).incoming`; or
terminal with `a = time last`, `Gk = G`). Take `t₀ ∈ Ico a s`, and assume I0. Obtain
`(p, records)` from `hH.2.2.2.1` via
`hasCanonicalCutoffRecords_iff_exists_isCanonicalCutoffRecordFamily`, and let `k` be the stage.
For `(y,t)` with `a < t`, `t₀ ≤ t < t₀+η`, `t < s` and `qs < R := Gk.flow.scalar t y`:

- **(A) old**, `τmin ≤ R(t−a)`. If `t < t₀`, the point is excluded (the conclusion is only for
  `t ≥ t₀`). Otherwise `CanonicalOn` from I0 at `(y,t)` (`qcan ≤ qs < R`) gives `W`, `hW`. Then
  `⟨(W.toSpatial).enlargeConstants hC1 hC2, (W.capTubeHasNeckChart_toSpatial hW).enlarge_constants …⟩`
  with `C1 ≤ C1s`, `C2 ≤ C2s`.
- **(B) cap window**, `CapWindowPoint records k y t Dw θcap`, where `(Dw, θcap)` comes from X-core.
  This case uses no age condition; see §2.
- **(C) young, not in a cap window**: `R(t−a) < τmin ∧ ¬CapWindowPoint records k y t Dw θcap`.
  X-core with `θ := τmin` gives a strong witness on a traced common flow `S` over the ball
  `U = B_{g(t)}(y, A/√R)` through the events. Then `toSpatial`, the identity
  `S.base.metric t = (Gk.flow.base.metric t).restrictOpen U`, and SW-P along `U ↪ carrier` (§3).

## 2. Case (B): the exact transport chain

Unpack `(j', hl, Atr, b, x)` from `CapWindowPoint`. Set `q := ((records j').static b).neck.scale`
and `T := q(t − time j'.succ) ≤ θcap`. Let `Θ := max θcap (1/2) < 1`, and let `α := ε/2`,
`ε₁ := neckModelTolerance α`.

1. **Standard source (S1).** `C_std := C_std(ε₁)`. For every standard solution `Q`, every
   `T ∈ [0,1)` and every `z : E3`, there are `W_Q : SpatialCanonicalWitness (Q.val.metric T) ε₁ C_std C_std z`,
   `W_Q.capTubeHasNeckChart ε₁`, and a cap depth margin (failure 4). `W_Q` is only `.neck` or
   `.cap`.
2. **Bridge.** Call `exists_standard_comparison_of_cap_window_trace Θ Ctime` for `(P, Creset, Cbirth)`.
   Then take `D := Dw + 1 + Λ(Θ)·4·C_std + 1`, with `Λ(Θ)` the `Q(T)`-versus-Euclidean distance
   factor on `[0, Θ]` (from `standard_metric_bounds_on_shorter_windows` and
   `StandardCap/Distance`). Take `e := e_tr(ε, C_std, K(Θ), Λ(Θ))` from SW-T, where `K(Θ)` is the
   standard curvature bound on `[0, Θ]`, and `N := ⌈ε₁⁻¹⌉₊ + 3`, `η_b := 1`. This yields
   `(Rb, m₀, ζ₀, δ₀)`. The hypotheses are:
   - the record family and `δbound ≤ δ₀`, `Rb ≤ modelRadius`, `m₀ ≤ modelOrder`,
     `accuracy ≤ ζ₀`: from C4's `δmax Dcap mcap εcap` outputs;
   - `0 < qcan`;
   - `θcap ≤ Θ`;
   - Hamilton–Ivey and `−3/a₀ ≤ R` on `g₀`: from
     `exists_pos_fixedHamiltonIveyRegion_for_identified_histories P₀ g₀` (pull `a₀` before `ρmax`);
   - `Gk.base.metric a = initialMetric k`: from `H.event_initial j` or `hG.2`;
   - `EventSlabsDerivative Ctime qcan k`: a hypothesis;
   - `Gk.DerivativeBoundBefore Ctime qcan t`: from P0 (I0 plus `Before t₀`);
   - `qcan ≤ Cbirth·q` and `1 ≤ a₀·q`: from `ρmax ≤ √(Cbirth/(2qcan))`, `ρmax ≤ √(a₀/2)` and
     `IsCanonicalCutoffRecordFamily.inv_two_mul_sq_lt_static_scale` (uses `recenterConstant·δbound ≤ 1/2`
     from `InCutoffClass`).

   The output is: `z` with `z.val = x.val`, `Ξ`, `gflow`, `S` on `closed 0 T`,
   `S.base.metric T = localPullMetric (scaleMetric q (gflow (time j'.succ + T/q))) Ξ hΞ`,
   `gflow τ = backwardSurvivorIncomingMetric … G L τ` on `[a, t]`, `Q`, and
   `metricDerivNorm i (S.base.metric T) ((Q T)|_D) … < e` for `i ≤ N`.
3. **Restrict** `W_Q` to `standardCapWindow D` (SW-R). This works because `‖z‖ < Dw+1` and the
   `Q(T)`-ball of radius `4·C_std/√R_Q ≤ 4C_std` stays inside `window(D−1)` (`R_Q ≥ 1`).
4. **Metric-close transport** from `(Q T)|_D` to `S.base.metric T` on the same window, with the
   identity map (SW-T). Output: accuracy `2α = ε`, constants `2C_std`. This is the only lossy step.
5. **Unpull and unscale.** Apply SW-P along `Φ := fun v => (Ξ v)` (after L7a turns it into a
   `PartialDiffeomorph` with open image), then SW-S with factor `q`. This gives a witness for
   `gflow t` on `backwardSurvivorIncomingDomain` at `Ξ z`, exactly.
6. **Into the carrier.** `gflow t = backwardSurvivorIncomingMetric … L t`, which is
   `(Gk.flow.base.metric t).restrictOpen _`. That identification is still to check at `τ = t`,
   through `L.metric` (the same check as `DESIGN_C3B.md` L7). Then apply SW-P along the inclusion.
   The incoming map sends `Ξ z ↦ ⟨y, hy⟩`, and the `G` versus `Gk` metrics agree
   (`∀ v, G… = Gk…`). Finish with `enlargeConstants` to `C1s C2s`.

The capture hypothesis of SW-P in steps 5–6 is `B_{g(t)}(y, 3·radius) ⊆ image`. It holds by
`PartialDiffeomorph.riemannianBallOf_subset_image_of_metric_lower`
(`Geometry/Metric/Comparison/IntrinsicBallImage.lean`) with the buffer from step 2.

Accuracy bookkeeping: `ε₁ = neckModelTolerance(ε/2)` at the source, `2·(ε/2) = ε` after SW-T, and
exact from there on. `capTubeHasNeckChart`: `ε₁ → ε` in SW-T, where the tube map is unchanged
because `partialDiffeomorphTransMixed nk.map id = nk.map`. It is then carried by map composition.
The pipeline `alpha`, `2α` and E3 play no role.

## 3. Case (C) and X-core

**X-core (shared with C3c; the essential open mathematics).** Its hypotheses have C3c's shape. For
`B ε` (`ε ≤ εbar`), `C1 C2 τmin Ctime Cgrad` above C3c's floors, `C1s C2s Cs ≥ 1`, `κ phi` and
`θ > 0`, it provides `∃ Dw θcap q₀ δ ρ ε' m, θcap < 1`. Then for `qcan ≥ q₀`, `qs ∈ [qcan, Cs·qcan]`,
the class, the records, the pinched slabs, all the earlier-slab clauses, the current-slab
`Before t₀` clauses, noncollapsing, and I0's C3 output, there is `η > 0` such that for every
`(y,t)` in the window with `qs < R`, `R(t−a) < θ` and `¬CapWindowPoint records k y t Dw θcap`:

```lean
∃ (U : Opens carrier) (hU : (U : Set _) = riemannianBallOf (Gk.flow.base.metric t) y (A/√R))
  (S : SolutionOn (M := U) (closed (t − τ/R) t)), IsSolutionOn S ∧
  S.base.metric t = (Gk.flow.base.metric t).restrictOpen U ∧
  ∃ W : CanonicalWitness S ε Cx Cx ⟨y, _⟩ t, W.capTubeHasNeckChart ε ∧
    (W.alternative is .round/.positive → connectedComponent y ⊆ U)
```

Here `Cx = Cx(ε)` is the κ-solution canonical constant, which is independent of `κ`, as C3a
already uses (`UniformKappaCanonicalThreshold`). `A ≥ 4Cx` is fixed. `S` is the common flow from
`exists_event_common_flow_with_compact_neighborhood_of_isTracedRegion` or its terminal version
(`TracedRegion.lean:598/722`). The traced region comes from
`exists_isTracedRegion_or_capWindowPoint_at_scale` (B5); its "scalar ≤ 2QR along traces" input
comes from the bounded-curvature-at-distance chain (B3), which consumes the spatial clauses. C3c is
then the corollary for `τmin ≤ R(t−a) < θ`: the witness window lies in the slab, so
`S = Gk.flow|_U` there, followed by a restriction to `Gk.flow` (a temporal/spatial version of L3).
C4(C) is the corollary with `θ := τmin`: `W.toSpatial`, then SW-P along `U ↪ carrier`. For a
`whole` alternative, `connectedComponentIn U y = connectedComponent y` by the last clause.

**Persistence lemma (asked for; true, not needed, and does not close (C)).**
```lean
theorem SpatialCanonicalWitness.exists_forward_of_bounded_curvature
    {α : ℝ} (hα : 0 < α) (hα' : 2 * α < 1 / 11) (C1 C2 Λ : ℝ) :
    ∃ c C1' C2' : ℝ, 0 < c ∧ ∀ (G : P.IncomingSlab a s) (t₁ t : ℝ) (x : P.Carrier),
      a < t₁ → t₁ ≤ t → t < s →
      (W : SpatialCanonicalWitness (G.flow.base.metric t₁) (neckModelTolerance α) C1 C2 x) →
      W.capTubeHasNeckChart (neckModelTolerance α) → W.depthMargin →
      (∀ τ ∈ Icc t₁ t, ∀ y ∈ riemannianBallOf (G.flow.base.metric t₁) x (4 * C1 / √R₁),
         G.riemannNorm τ y ≤ Λ * R₁) →
      R₁ * (t - t₁) ≤ c →
      ∃ W' : SpatialCanonicalWitness (G.flow.base.metric t) (2 * α) C1' C2' x,
        W'.capTubeHasNeckChart (2 * α)
```
Here `R₁ := G.flow.scalar t₁ x`. Ingredients:
- Shi on the terminal ball (`Estimates/Shi/Derivatives/TerminalBall.lean:373`);
- `exists_metricDerivNormSupOn_time_lipschitz_of_finite_ricci_bounds`
  (`Estimates/InitialMetricTimeBounds.lean:100`), which gives `C^N` time-Lipschitz closeness of
  `g(t)` to `g(t₁)`;
- `exists_sliver_forward_comparison` (B1) for `C⁰` and balls;
- SW-T with the identity map.

Estimate 150–250 lines on top of SW-T. Its source must be at `neckModelTolerance α` with a depth
margin, and the induction's clause is at `ε` with no margin (failure 2). It is therefore not a
route for C4.

## 4. Bricks in dependency order (line estimates)

| # | Brick | Content | Lines |
|---|---|---|---|
| I0 | Interface | C3's `∃ η, DerivativeBoundOn ∧ GradientBoundOn ∧ CanonicalOn` as a C4 hypothesis (both branches) plus 2 assembly arguments | 15 |
| P0 | `IncomingSlab.derivativeBoundBefore_of_before_of_on` | `Before t₀ ∧ On t₀ η ∧ t < t₀+η → Before t` (same for gradient) | 20 |
| S0 | Depth margin | 27a/27b/27c expose `(10000+1)/√R ≤ dist` on cap tubes | 40–120 |
| S1 | `StandardSolution.exists_uniform_spatialCanonicalWitness` | `∀ ε, ∃ C, ∀ Q, ∀ T ∈ Ico 0 1, ∀ z, witness`, using `of_age` and `c₀/(1−t)` giving `Θ₂`, plus 27b/27c at `Θ₂` (conditional on 27c) | 60–100 |
| SW-S | `SpatialCanonicalWitness.scaleMetric` | every field; `SpatialLocalCap`/chain via `SpatialNeck.scaleMetric`; `SecLower` and round are scale-free | 250–350 |
| SW-P | `SpatialCanonicalWitness.map` along an open isometric embedding `Φ` (`g_N = Φ^* g_M`) with ball capture `B(Φx, 3r) ⊆ range` | balls, frontier of the image, volume under isometry, neck/chain/cap maps, `whole` alternatives under `connectedComponent ⊆ range` | 400–600 |
| SW-R | Restriction to an open `U ⊇ B(x, 4r)` | intrinsic versus ambient balls (as L3) | 150–250 |
| SW-T | Metric-close transport, identity map, uniform tolerance `e_tr(ε, C, K, Λ)` | neck via `SpatialNeck.exists_transport_of_local_comparisons` (explicit `neckSourceTolerance`), chain necks, depth with margin, scalar/rm/gradient from `C³`, volume from `C⁰`, balls from bi-Lipschitz plus capture; output constants `2C` | 350–550 |
| L7a | `PartialDiffeomorph` from `IsSmoothEmbedding` with open image | shared with C3b | 80–150 |
| B | Case (B) assembly | §2 steps 1–6, including the `gflow t = Gk t` check | 300–450 |
| X | X-core | shared with C3c; the essential open content (common-flow blow-up, B3, B5, κ-model theorem on the traced flow, whole-component clause) | 1500–3000 (counted under C3c) |
| C | Case (C) from X-core | `toSpatial` plus SW-P along `U ↪ carrier` | 120–200 |
| Leaf | `spatialCanonicalContinuation` | both branches, the (A)/(B)/(C) split, constants | 300–400 |

The C4-specific total, excluding X, is about 2.1k–3.3k lines. SW-S, SW-R, SW-P, P0, S0 and L7a are
independent. SW-T needs SW-R. B needs S1, SW-* and L7a. C needs X and SW-P.

## 5. Constants and the assembly

```
intro B ε hB hε hε' C1 C2 τmin Ctime Cgrad hC1 hC2 hτ
obtain Cstd := S1 (neckModelTolerance (ε/2));  Cx := X-core constant (ε)
refine ⟨max C1 (max (2*Cstd) Cx), max C2 (max (2*Cstd) Cx), 1, …⟩   -- Cs := 1
intro κ phi hκ hphi
obtain ⟨a₀, ha₀, hfix⟩ := exists_pos_fixedHamiltonIveyRegion_for_identified_histories P₀ g₀
obtain ⟨Dw, θcap, q₀, δX, ρX, εX, mX, …, hX⟩ := X-core … κ phi (θ := τmin)
obtain ⟨P, Creset, Cbirth, …, hbr⟩ := exists_standard_comparison_of_cap_window_trace (max θcap (1/2)) Ctime
obtain ⟨Rb, m₀, ζ₀, δ₀, …⟩ := hbr D e N 1           -- D e N from §2 step 2
refine ⟨max q₀ 1, …⟩
intro qcan hq
refine ⟨qcan, min δ₀ δX, min ρX (min √(Cbirth/(2qcan)) √(a₀/2)), min ζ₀ εX, max Rb DX,
  max m₀ mX, le_rfl, by simpa, …⟩                      -- qs := qcan ≤ 1·qcan
intro p₀ δb ρb hacc hD hm hδ hρ H hH hpinch
obtain ⟨p, records, hfam⟩ := (hasCanonicalCutoffRecords_iff_…).1 hH.2.2.2.1
refine ⟨fun j hcanP hderP hgradP hspatP t₀ ht₀ hc hd hg hs hn hC3 => ?_, fun s G hG … hC3 => ?_⟩
-- each branch:
obtain ⟨η₃, hη₃, hdOn, hgOn, hcOn⟩ := hC3
obtain ⟨ηX, hηX, hXcore⟩ := hX … (C3's output passed in)
refine ⟨min η₃ ηX, …, fun y t hat ht₀ htη hts hR => ?_⟩
rcases le_or_lt τmin (R * (t - a)) with hold | hyoung
· -- (A)
by_cases hcw : H.CapWindowPoint records k y t Dw θcap
· -- (B): §2
· -- (C): hXcore y t … hyoung hcw, then toSpatial and SW-P
```

Why `Cs := 1` and `qs := qcan`: C4 needs nothing above `qcan`. (A) uses `qcan ≤ qs`, (B) uses no
threshold, and X-core, like C3c, accepts every `qs ∈ [qcan, Cs·qcan]`. If X-core's picking
argument needs a gap, take `Cs := 1 + Ctime·(τmin + 1)`. Then along backward traces of normalized
length `≤ τmin + 1`, integrating `|∂ₜR| ≤ Ctime R²` gives `R ≥ qs/Cs ≥ qcan`, so the derivative
clause stays valid all along the trace. `Cs` depends only on inputs given before `∃ C1s C2s Cs`.
`q₄ := max q₀ 1` depends on `κ phi` only through X-core. The bridge needs only `0 < qcan`; its
class inputs go through `ρmax`, which is chosen after `qcan` as lane 28 already allows.
