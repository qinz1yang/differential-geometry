# C4 case (B) design: cap-window spatial witnesses (2026-09-26)

Design only. No tree file other than this one was touched, and no build or git write was made.
Every statement in §2 was elaborated with `sorry` bodies in the scratch probes
`ProbeC4B1.lean` and `ProbeC4B2.lean` (outside the tree, `LEAN_NUM_THREADS=2 lake env lean`).
Both gave 0 errors; the only warnings were the `sorry` warnings. Paths are relative to
`DifferentialGeometry/Geometry/Flow/RicciFlow/`. Settled by review G, and not reopened here:
the transport takes the target-centre gradient from C3's `GradientBoundOn`; the `Rm` loss goes into
`C2s`; `C_std(ε)` comes before `Θ`; case (C) is out of scope.

## 0. Failures first

1. **Quantifier order: SW-T's tolerance comes after the source witness. FATAL for DESIGN_C4 §2
   steps 2–4 as written.** `SpatialNeck.exists_transport_tolerance_of_metricComparisonOn`,
   `SpatialLocalCap.exists_deep_transport_tolerance_of_metricComparisonOn` and
   `SpatialCanonicalAlternative.exists_transport_tolerance_of_metricComparisonOn`
   (`Perelman/CanonicalNeighborhood/SpatialCanonicalWitnessComparisonTransport.lean:28/96/146`) all
   have the shape `∀ witness, ∃ delta`. `delta` depends on the centre scalar `q`, on `delta₁` from
   `exists_tolerance_abs_metricScalarAt_sub_lt` (which uses `|Rm|` at the centre,
   `CanonicalWitnessComparisonTransport.lean:175`), on the chain count through `Finset.inf'`, and on
   the depth tolerance of `exists_tolerance_depth_image_of_metricComparisonOn`
   (`CapComparisonTransport.lean:110`). The bridge
   `exists_standard_comparison_of_cap_window_trace` (`Surgery/Topology/CapWindowStandardComparison.lean:20`)
   fixes `e` in `∀ D e η N, ∃ R m₀ ζ₀ δ₀`. That is before the history, so before `(Q, T, z)`, so
   before `W_Q`. A per-witness `delta` therefore cannot be fed back into `e`. The fix is a
   **uniform-tolerance** transport (M4): `δ` depends only on `(α, m, C1, C2, Rlow)`. The
   dependencies are all explicit. The neck tolerance needs `q ≥ Rlow`. `|Rm| ≤ C2·q` holds on the
   domain. The depth needs a margin `m/√q`. The comparison is unnormalized, so at scale `q ≥ Rlow`
   the normalized error is at most `δ·Rlow^{-a/2}`, and no upper bound on `q` is needed.
2. **DESIGN_C4's S1 old branch has no uniform margins. FALSE as a transport source.** Old standard
   points come from `PartialStandardSolution.exists_spatialCanonicalWitness_with_cap_neck_charts_of_age`
   (`StandardSolution/StandardSpatialCanonical.lean:18`), through the windowed κ-model pipeline. Its
   reserves are the per-witness `BufferedCanonical.margin` / `a b`
   (`CanonicalNeighborhood/BufferedCanonical.lean:28`). They are not uniform, so failure 1 cannot be
   repaired on that branch. **Fix: split (B) at model age `τ' := max τQ δ⁻¹`** (C3b's own threshold,
   `CapWindowContinuationLeaf.lean:29`):
   - **(B-old)** `τ' ≤ T·R_S(T,z)`. Build the witness *on the window flow `S` itself* and transport
     nothing. The chain is: L6e `exists_uniform_orientedWitness_of_standard_close_endpoint`
     (`StandardClosenessEndpointWitness.lean:706`) gives `OrientedWitness S o δ κstd z T`;
     `exists_uniform_windowed_bufferedCanonical_with_cap_neck_charts.{0}`
     (`WindowedBufferedCanonical.lean:20`) applies because the window is
     `Ioo (T − (δR)⁻¹) T ⊆ Ioo 0 T = (closed 0 T).regular` (from `δ⁻¹ ≤ τ'`); then `toSpatial`
     (`SpatialCanonicalWitnessProjection.lean:92/110`). The constant is Θ-free.
     C3b could not do this on `Gk`, because its window must sit inside slab `k`
     (`hage2`, `CapWindowContinuationLeaf.lean:180`). A *spatial* witness needs only the slice `T`,
     so history-young but model-old points are covered here.
   - **(B-young)** `T·R_S < τ'`. By `le_mul_of_half_standard_scalar_lower`
     (`CapWindowContinuationAssembly.lean:142`) this forces `T < Θ₃ := 2τ'/(c₀ + 2τ')`, which is
     **Θ-free**. The source is 27c at `Θ₃` with explicit margins (M1a), followed by the uniform
     transport M4. This resolves DESIGN_C4 failure 3 without `Θ₂` or `of_age`.
3. **Margins cannot be produced a posteriori for caps. They must come from the producer.** Review F's
   `W.radius > 5000/√R` is true for caps (tube ⊆ domain ⊆ `B(x, 2r)`, and tube points are at
   distance `≥ 10000/√R`), so a radius margin is free. Two other margins are not free:
   - *Ball sandwich.* `B(x,r) ⊆ U ⊆ B(x,2r)` allows the ratio `ρ_out/ρ_in = 2` exactly. Under a
     `(1±δ)` comparison you need `μ²·ρ_out < 2ρ_in`. With radius `r' = r` this takes a strict
     margin both inside and outside.
   - *Depth.* `deep` is non-strict and can hold with equality.

   The records give no geometric margins. They give only placement: `‖x‖ < Dw+1` inside
   `modelRadius ≥ Rcap`. The producers do have room:
   - Neck witnesses (`StandardInitialSpatialCanonical.lean:120`, `r = 9/√Q`): the inner ball is
     `10√(1−ε) ≥ 9.53`, and the outer ball is `16√(1+ε) ≤ 16.71 < 17.55 = (2 − 1/20)·9`.
   - Tip witnesses (`StandardSliceSpatialCanonical.lean:356`, private): the depth is
     `≥ 0.995·11200 − 1 > 10000 + 1/20` (in units with `√Q ≥ 1`), and the outer ball is
     `≤ 1.005(r+c) + 2√ΛD < (1.95/1.05)·ρ` because `r ≥ 4√ΛD + 4D₁ + 11200`. The inner sandwich
     is tight *as constructed* (`ρ` is exactly the threshold). Replace `ρ` by `ρ/(1+m)`.

   Conclusion: `m = 1/20` is uniform. M1a exposes it as the Prop `HasMargins` (checked below as
   non-vacuous).
4. **DESIGN_C4's window size `D` is too small.** Step 3 used `D = Dw + 1 + Λ·4C_std + 1`. Two
   things are larger:
   - SW-R (`SpatialCanonicalWitness.restrictOpen`, `SpatialCanonicalWitnessTransport.lean:1106`)
     needs the *full* source neck windows `univ ×ˢ Ioo (-ε₁⁻¹) ε₁⁻¹` inside the window. That is a
     radius of about `(ε₁⁻¹ + 6)·√(1+ε)·√C/√R`.
   - The carry's closed ball must be larger than `2·radius`.

   Fix: avoid SW-R entirely. Transport from `Q.val.metric T` *on `E3`* to `S.base.metric T` along
   `F := (subtypeVal (standardCapWindow D)).symm`, with `U := standardCapWindow D` (M2 produces
   exactly this `MetricComparisonOn`). SW-T itself only needs the `α⁻¹`-windows (`hout`). `D` is
   then fed to L6e as its `r` parameter (next item).
5. **One `D` for L6e, the bridge and the carry.** L6e fixes its own `D` (`∀ Θ r, ∃ D > r`). Pass
   `r' := r + Λ(Θ)(L + 1) + 1`, with `L` covering both the M4 ball and the carry ball. The result
   `D > r'` then serves all three. Restricting `S` between windows is never needed.
6. **Universe (`ULift`).** `pushforwardOfInjective` (`SpatialCanonicalWitnessTransport.lean:1048`)
   is same-universe. The window is `Type 0` and `P.Carrier : Type u`. Carrying the witness needs one
   cross-universe step: `N : Type v`, `M : Type (max u v)`, the pattern of
   `WindowedModelWitness.ofLocalPull` (`WindowedModelLocalPull.lean:288`). The obstruction is that
   `CapCore.projective` (`FiniteHornGeometry.lean:155`) and `SpatialRoundComponent.Z` carry
   `Z : Type u`, so a naive restatement does not typecheck. Their `Z` must be replaced by
   `ULift.{u} Z` using `uliftChartedSpace` / `isManifold_ulift` / `uliftDiffeomorph`
   (`Topology/Manifold/ULift.lean:14/28/52`). Probe: `T2Space` and `SigmaCompactSpace` on
   `ULift N` are found by `inferInstance`. `IsManifold` needs the explicit
   `isManifold_ulift I3 N` term.
7. **DESIGN_C4 steps 5–6 are longer than needed.** No L7a partial diffeomorphism and no separate
   `gflow t = Gk t` check are required. `capWindow_flow_metric_eq`
   (`CapWindowContinuationAssembly.lean:199`) already gives
   `S.base.metric T = localPullMetric (scaleMetric q (Gk.flow.base.metric t)) (fun w => (Ξ w).val.val) hΦ`,
   and `injective_backwardSurvivorIncomingDomain_val_val` (`CapWindowFlowPushforward.lean:83`)
   supplies injectivity. The carry is therefore: M3 (hetero `pushforwardOfInjective`), then
   `SpatialCanonicalWitness.scaleMetric` by `q⁻¹` (`:168`).
8. **Reference conversion (SPT log item 3) is already supplied, uniformly.**
   `exists_uniform_standard_metric_deriv_norm_reference_bound`
   (`StandardSolution/StandardMetricReference.lean:19`) is
   `∀ θ<1 p, ∃ D, ∀ U S t∈[0,θ] A B r≤p x, metricDerivNorm r A B (S t|_U) x ≤ D·Σ_{k≤p} metricDerivNorm k A B (cap|_U) x`.
   It holds uniformly over the family, over every open `U`, and at any fixed `Θ < 1`. What is missing
   is only the glue into `MetricComparisonOn` (M2), via `MapMetricApproximationOn.ofMetricDerivNorm`
   (`…/MetricApproximation/OfMetricDerivNorm.lean:23`) and `MetricComparisonOn.ofMapMetricApproximation`
   (`CanonicalNeighborhood/StaticMetricApproximation.lean:21`), plus naturality along
   `subtypeVal.symm`.
9. **Leaf quantifiers: nothing false.** The leaf gives `δmax ρmax εcap Dcap mcap` after `qcan`. M5
   produces `Rcap mcap` after `(Dw, θcap)`, and `δmax ρmax εcap` after `qcan`.
   - `recenterConstant·δbound ≤ 1/2` is `hH.2.2.2.2`. It is consumed only by
     `birth_scale_bounds` (`CapWindowContinuationAssembly.lean:154`), together with
     `ρmax := min √(Cb/(4qcan)) √(a₀/2)`. There is no circularity: `δmax` does not depend on
     `δbound`.
   - `Cs` depends on `ε` only, so it can precede `κ`.
   - The gradient hypothesis at `(y,t)` is C3's `GradientBoundOn` output. It needs
     `qcan < R(y,t)`, which is the `SpatiallyCanonicalOn` premise when `qs = qcan`. It is supplied,
     not packaged.
10. **Non-vacuity of `HasMargins`.** Neck witnesses at `r = 9/√Q` satisfy it with `m = 1/20` (see
    item 3), and so do tip witnesses after the shrink. It constrains the witness: the shape clause
    excludes `.round` and `.positive`, which is correct on `E3` because a `whole` alternative with a
    compact domain would make `E3` compact.

## 1. Case (B) pipeline

Given `CapWindowPoint records k y t Dw θcap`, obtain `(j, hl, A, b, x)`, `q := static scale`,
`T := q(t − t_{j+1}) ≤ θcap`, and `Θ := max θcap (1/2)`. The bridge (as in C3b) gives `S` on
`standardCapWindow D`, together with `z`, `Ξ`, `Q` and closeness `< e` up to order `N` on `[0,T]`.
Then:

1. Apply M4★ (the window theorem, §2) at `z`, with the gradient bound pulled back by G (§2). This
   gives `W : SpatialCanonicalWitness (S.base.metric T) ε Cw C2 z`.
2. Rewrite by `capWindow_flow_metric_eq`, apply M3 along `Φ = val∘val∘Ξ` (the ball comes from M1b
   with `g := S T` and the `1/2` lower bound from `exists_uniform_standard_metric_scalar_lower_comparison`,
   `StandardActionComparison.lean:40`), then `scaleMetric q⁻¹`. The result is a witness for
   `Gk.flow.base.metric t` at `y`.
3. `enlargeConstants` to `(C1s, C2s)`.

## 2. Exact statements (all elaborated)

Namespaces: `FiniteHorn` for M1a-def, M3 and M4; `DifferentialGeometry.PDE.RicciFlow` for M1a, M1b,
M2 and M4★; `Surgery.Topology` for G and M5. The local instance
`SigmaCompactSpace (standardCapWindow D)` is used as in `StandardFamilyCompactness`.

**M1a margins (def + producer).**
```lean
def SpatialCanonicalWitness.HasMargins {g : SmoothRiemannianMetric I3 M} {eps C1 C2 : ℝ}
    {x : M} (W : SpatialCanonicalWitness g eps C1 C2 x) (m : ℝ) : Prop :=
  ((∃ n, W.alternative = .neck n) ∨ ∃ c d, W.alternative = .cap c d) ∧
    (1 + m) / Real.sqrt (metricScalarAt g x) ≤ W.radius ∧
    riemannianBallOf (I := I3) g x ((1 + m) * W.radius) ⊆ W.domain.carrier ∧
    W.domain.carrier ⊆ riemannianBallOf (I := I3) g x ((2 - m) * W.radius) ∧
    ∀ c d, W.alternative = .cap c d →
      ∀ y ∈ c.tube, (10000 + m) / Real.sqrt (metricScalarAt g x) ≤ metricDistance g x y

theorem StandardSolution.exists_spatialCanonicalWitness_with_margins
    {eps Θ : ℝ} (heps : 0 < eps) (hsmall : eps < 1 / 11) (hΘ : Θ < 1) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (S : StandardSolution) (x : EuclideanSpace ℝ (Fin 3)) (t : ℝ),
      t ∈ Icc 0 Θ →
        ∃ W : SpatialCanonicalWitness (S.val.metric t) eps C C x,
          W.capTubeHasNeckChart eps ∧ W.HasMargins (1 / 20)
```

**M1b placement (uniform, explicit `Λ`).** The key supplier is `standardCap_edist_zero`
(`Surgery/Topology/StaticCap.lean:201`: `d_cap(0,x) = ‖x‖`). By the triangle inequality and
Λ-equivalence (`uniformStandardLifetime_metricComparison`), `‖y‖ ≤ ‖z‖ + √Λ·d`. Compactness in the
window comes from `isCompact_riemannianClosedBallOf_of_metric_lower_on_opens`
(`Geometry/Comparison/OpenEmbeddingBallCompactness.lean:18`).
```lean
theorem StandardSolution.exists_ball_placement {Θ : ℝ} (hΘ : Θ < 1) :
    ∃ Λ : ℝ, 1 ≤ Λ ∧ ∀ (Q : StandardSolution) (T : ℝ), T ∈ Icc 0 Θ →
      ∀ (L : ℝ) (z : EuclideanSpace ℝ (Fin 3)), 0 ≤ L →
        IsCompact (riemannianClosedBallOf (I := I3) (Q.val.metric T) z L) ∧
          ∀ y ∈ riemannianClosedBallOf (I := I3) (Q.val.metric T) z L,
            ‖y‖ ≤ ‖z‖ + Λ * (L + 1)

theorem StandardSolution.exists_window_ball_placement {Θ : ℝ} (hΘ : Θ < 1) :
    ∃ Λ : ℝ, 1 ≤ Λ ∧ ∀ (D L : ℝ) (z : standardCapWindow D), 0 ≤ L →
      ‖(z : EuclideanSpace ℝ (Fin 3))‖ + Λ * (L + 1) < D + 1 →
      ∀ (Q : StandardSolution) (T : ℝ), T ∈ Icc 0 Θ →
      ∀ g : SmoothRiemannianMetric I3 (standardCapWindow D),
        (∀ y (v : TangentSpace I3 y),
          (1 / 2) * ((Q.val.metric T).restrictOpen (standardCapWindow D)).inner y v v ≤
            g.inner y v v) →
        IsCompact (riemannianClosedBallOf (I := I3) g z L) ∧
          ∀ y ∈ riemannianClosedBallOf (I := I3) g z L,
            ‖(y : EuclideanSpace ℝ (Fin 3))‖ ≤ ‖(z : EuclideanSpace ℝ (Fin 3))‖ + Λ * (L + 1)
```

**M2 window comparison.** `e := η/(D_ref·(p+1))`, with `D_ref` from `StandardMetricReference:19`.
Source on `E3`, target on the window.
```lean
theorem StandardSolution.exists_window_metricComparisonOn {Θ : ℝ} (hΘ0 : 0 ≤ Θ) (hΘ : Θ < 1)
    (order : ℕ) {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∃ e : ℝ, 0 < e ∧ ∀ (D : ℝ) (hne : Nonempty (standardCapWindow D)) (Q : StandardSolution)
      (T : ℝ), T ∈ Icc 0 Θ →
      ∀ g : SmoothRiemannianMetric I3 (standardCapWindow D),
        (∀ i ≤ order, ∀ v : standardCapWindow D,
          metricDerivNorm i g ((Q.val.metric T).restrictOpen (standardCapWindow D))
            (StandardCap.metric.restrictOpen (standardCapWindow D)) v < e) →
        Nonempty (MetricComparisonOn (fun _ => Q.val.metric T) (fun _ => g)
          ((DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := I3)
            (standardCapWindow D) hne).symm : EuclideanSpace ℝ (Fin 3) → standardCapWindow D)
          (standardCapWindow D) {0} order η)
```

**M3 ULift bridge.** Recommended form: generalize the existing `pushforwardOfInjective` in place.
The probe name was `…Hetero`. Internally it ulifts `CapCore.projective`'s and the round
component's `Z`.
```lean
variable {N : Type v} [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold I3 ∞ N]
  [T2Space N] [SigmaCompactSpace N]
  {M : Type (max u v)} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
  [T2Space M] [SigmaCompactSpace M]

def SpatialCanonicalWitness.pushforwardOfInjective {g : SmoothRiemannianMetric I3 M}
    {eps C1 C2 : ℝ} {f : N → M} (hf : IsLocalDiffeomorph I3 I3 ∞ f)
    (hinj : Function.Injective f) {x : N}
    (W : SpatialCanonicalWitness (localPullMetric g f hf) eps C1 C2 x) {R : ℝ}
    (hR : 2 * W.radius < R)
    (hcpt : IsCompact (riemannianClosedBallOf (I := I3) (localPullMetric g f hf) x R)) :
    SpatialCanonicalWitness g eps C1 C2 (f x)

theorem SpatialCanonicalWitness.capTubeHasNeckChart.pushforwardOfInjective
    {g : SmoothRiemannianMetric I3 M} {eps C1 C2 alpha : ℝ} {f : N → M}
    (hf : IsLocalDiffeomorph I3 I3 ∞ f) (hinj : Function.Injective f) {x : N}
    {W : SpatialCanonicalWitness (localPullMetric g f hf) eps C1 C2 x}
    (hW : W.capTubeHasNeckChart alpha) {R : ℝ} (hR : 2 * W.radius < R)
    (hcpt : IsCompact (riemannianClosedBallOf (I := I3) (localPullMetric g f hf) x R)) :
    (W.pushforwardOfInjective hf hinj hR hcpt).capTubeHasNeckChart alpha
```

**M4 uniform transport.** `δ` depends on `(α, m, C1, C2, Rlow)` only. The constants `2·C1` and
`C2' ≥ 1000·C2` are explicit: `324·2` for `Rm` via `modelComparison_riemannOp_norm_le`
(`WitnessTransport.lean:393`), plus the relative scalar error. The radius is kept (`r' = r`), which
the `HasMargins` sandwich makes possible.
```lean
theorem SpatialCanonicalWitness.exists_uniform_comparison_transport_tolerance
    {alpha m C1 C2 Rlow : ℝ} (ha : 0 < alpha) (hsmall : 2 * alpha < 1 / 11)
    (hm : 0 < m) (hm1 : m ≤ 1 / 2) (hC1 : 1 ≤ C1) (hC2 : 1 ≤ C2) (hRlow : 0 < Rlow) :
    ∃ δ : ℝ, 0 < δ ∧
    ∀ (g : SmoothRiemannianMetric I3 P) (x : P)
      (W : SpatialCanonicalWitness g (neckModelTolerance alpha) C1 C2 x),
      W.capTubeHasNeckChart (neckModelTolerance alpha) → W.HasMargins m →
      Rlow ≤ metricScalarAt g x →
    ∀ U : TopologicalSpace.Opens P,
      IsCompact (riemannianClosedBallOf (I := I3) g x
        ((8 * C1 + 3 * (alpha⁻¹ + 7) * Real.sqrt C2) / Real.sqrt (metricScalarAt g x))) →
      riemannianClosedBallOf (I := I3) g x
        ((8 * C1 + 3 * (alpha⁻¹ + 7) * Real.sqrt C2) / Real.sqrt (metricScalarAt g x)) ⊆ U →
    ∀ (N : Type u) [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold I3 ∞ N]
      [T2Space N] [SigmaCompactSpace N] (g' : SmoothRiemannianMetric I3 N)
      (F : PartialDiffeomorph I3 I3 P N ∞), (U : Set P) ⊆ F.source →
      MetricComparisonOn (fun _ => g) (fun _ => g') F U {0} (max 2 ⌈(2 * alpha)⁻¹⌉₊) δ →
    ∀ C2' : ℝ, 1000 * C2 ≤ C2' →
      (∀ v : TangentSpace I3 (F x),
        |(show ℝ from mfderiv I3 𝓘(ℝ, ℝ) (metricScalarAt g') (F x) v)| ≤
          C2' * metricScalarAt g' (F x) * Real.sqrt (metricScalarAt g' (F x)) *
            Real.sqrt (g'.inner (F x) v v)) →
      ∃ W' : SpatialCanonicalWitness g' (2 * alpha) (2 * C1) C2' (F x),
        W'.capTubeHasNeckChart (2 * alpha) ∧ W'.domain.carrier = F '' W.domain.carrier
```
The ball radius covers the following, using `R ≥ C2⁻¹ q` on the domain:
- `3·rho < R_b` with `rho = (2−m)r ≤ 2C1/√q`;
- every chain neck's `α⁻¹`-window, via `SpatialNeck.image_slab_subset_closedBall`
  (`NeckRegionBall.lean:156`) at a centre in the tube;
- the `capTubeHasNeckChart` neck, whose centre `nk.map (center,0)` lies in the tube.

**M4★ window theorem (risk carrier; case (B) on the model window).**
`Cw := max C_old (1000·C_std(Θ₃, neckModelTolerance(ε/2)))` is chosen before `Θ`. The theorem
takes its gradient hypothesis at `(S T, z)`. That hypothesis is needed only for young points and is
harmless for old ones.
```lean
theorem exists_window_spatialCanonicalWitness_of_standard_close {ε : ℝ} (hε : 0 < ε)
    (hε' : ε < 1 / 11) :
    ∃ Cw : ℝ, 1 ≤ Cw ∧ ∀ (Θ r : ℝ), Θ < 1 →
    ∃ (D : ℝ) (N : ℕ) (e : ℝ), r < D ∧ 0 < e ∧
    ∀ (Q : StandardSolution) (T : ℝ) (hT : 0 ≤ T), T ≤ Θ →
    ∀ (S : SolutionOn (I := ThreeModel) (M := standardCapWindow D)
        (RealTimeInterval.closed 0 T hT)), IsSolutionOn S →
    (∀ τ ∈ Icc 0 T, ∀ i ≤ N, ∀ v : standardCapWindow D,
      metricDerivNorm i (S.base.metric τ)
        ((Q.val.metric τ).restrictOpen (standardCapWindow D))
        (StandardCap.metric.restrictOpen (standardCapWindow D)) v < e) →
    ∀ z : standardCapWindow D, ‖z.val‖ < r →
    ∀ C2 : ℝ, Cw ≤ C2 →
      (∀ v : TangentSpace I3 z,
        |(show ℝ from mfderiv I3 𝓘(ℝ, ℝ) (metricScalarAt (S.base.metric T)) z v)| ≤
          C2 * S.scalar T z * Real.sqrt (S.scalar T z) *
            Real.sqrt ((S.base.metric T).inner z v v)) →
      ∃ W : SpatialCanonicalWitness (S.base.metric T) ε Cw C2 z, W.capTubeHasNeckChart ε
```

**G gradient pull-back** (scale-invariant form):
```lean
theorem abs_mfderiv_metricScalarAt_localPullMetric_scaleMetric_le
    (g : SmoothRiemannianMetric I3 M) (f : N → M) (hf : IsLocalDiffeomorph I3 I3 ∞ f)
    {q C : ℝ} (hq : 0 < q) (z : N)
    (h : ∀ w : TangentSpace I3 (f z),
      |(show ℝ from mfderiv I3 𝓘(ℝ, ℝ) (metricScalarAt g) (f z) w)| ≤
        C * metricScalarAt g (f z) * Real.sqrt (metricScalarAt g (f z)) *
          Real.sqrt (g.inner (f z) w w)) :
    ∀ v : TangentSpace I3 z,
      |(show ℝ from mfderiv I3 𝓘(ℝ, ℝ)
          (metricScalarAt (localPullMetric (scaleMetric q hq g) f hf)) z v)| ≤
        C * metricScalarAt (localPullMetric (scaleMetric q hq g) f hf) z *
          Real.sqrt (metricScalarAt (localPullMetric (scaleMetric q hq g) f hf) z) *
          Real.sqrt ((localPullMetric (scaleMetric q hq g) f hf).inner z v v)
```

**M5 case (B) per-point theorem.** Template: `exists_capWindowPoint_bounds`,
`CapWindowContinuationLeaf.lean:29`. Namespace `RetainedCoreHistory`.
```lean
theorem exists_capWindowPoint_spatialCanonicalWitness (P₀ : OrientedThreeStage.{u})
    (g₀ : P₀.Metric) {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 11) :
    ∃ Cs : ℝ, 1 ≤ Cs ∧
    ∀ (Ctime Cgrad : ℝ≥0) (Dw θcap : ℝ), 0 < Dw → θcap < 1 →
    ∃ (Rcap : ℝ) (mcap : ℕ), Dw + 1 < Rcap ∧
    ∀ qcan : ℝ, 0 < qcan →
    ∃ (δmax ρmax εcap : ℝ), 0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧
    ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
      p₀.modelAccuracy ≤ εcap → Rcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
      δbound ≤ δmax → ρbound ≤ ρmax →
    ∀ H : RetainedCoreHistory P₀, Nonempty (InitialIdentification P₀ g₀ H.toHistory) →
      p₀.recenterConstant * δbound ≤ 1 / 2 →
    ∀ (p : CutoffParameters) (records : ∀ i, GeometricCutoffRecord H.toHistory i p),
      H.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
    ∀ (k : Fin (H.eventCount + 1)) (s : ℝ) (Gk : (H.stage k).IncomingSlab (H.time k) s),
      Gk.flow.base.metric (H.time k) = H.initialMetric k →
      H.EventSlabsDerivative Ctime qcan k →
    ∀ t : ℝ, H.time k < t → t < s → Gk.DerivativeBoundBefore Ctime qcan t →
    ∀ y : (H.stage k).Carrier, H.CapWindowPoint records k y t Dw θcap →
      qcan < Gk.flow.scalar t y →
      (∀ v : TangentSpace I3 y,
        |Perelman.CanonicalNeighborhood.scalarDifferential Gk.flow t y v| ≤
          Cgrad * Gk.flow.scalar t y * Real.sqrt (Gk.flow.scalar t y) *
            Real.sqrt ((Gk.flow.base.metric t).inner y v v)) →
      ∃ W : SpatialCanonicalWitness (Gk.flow.base.metric t) ε Cs (max Cs (Cgrad : ℝ)) y,
        W.capTubeHasNeckChart ε
```
The leaf consumes M5 in both branches as follows:
- `Cs` enters `C1s`/`C2s` before `κ`.
- `(Dw, θcap)` come from X-core.
- `Rcap ≤ Dcap` and `mcap` are output after `qcan`.
- The inputs come from:
  - `hH.1`, `hH.2.2.2.2`;
  - `(hasCanonicalCutoffRecords_iff_…).1 hH.2.2.2.1`;
  - `H.event_initial j` / `hG.2`;
  - `EventSlabsDerivative`;
  - P0 (`Before t₀ ∪ On[t₀, t₀+η)`);
  - C3's `GradientBoundOn`.

## 3. Suppliers, bricks, order

The suppliers are cited inline in §0–§2. The bricks:

| # | Brick | Content | Lines |
|---|---|---|---|
| M1a | `HasMargins` + producer | Expose `m = 1/20` in the tip constructor (shrink `ρ` by `1+m`, depth room) and the neck constructor; `enlargeConstants` keeps it; re-prove the 27c headline with margins | 150–250 |
| M1b | placement | `standardCap_edist_zero` + Λ-equivalence + open-embedding ball compactness | 60–100 |
| M2 | window comparison | reference bound (exists) → `MapMetricApproximationOn.ofMetricDerivNorm` → `ofMapMetricApproximation`, naturality along `subtypeVal.symm` | 60–120 |
| M3 | hetero `pushforwardOfInjective` | generalize universes; ulift `CapCore.projective` and the round `Z` | 250–400 |
| G | gradient pull-back | chain rule for `localPull`, scale weights | 40–80 |
| M4 | uniform transport | uniform versions of neck / scalar / depth tolerances (explicit in `q ≥ Rlow`, `Kb ≤ C2 q`, `m`); fields: sandwich with `r' = r`, scalar, `Rm` (`riemannOp`), volume from C⁰, gradient from hypothesis | 450–700 |
| M4★ | window theorem | old: L6e → B8 buffered → `toSpatial`; young: `Θ₃`, M1a at `Θ₃`, M1b, M2, M4; one `D` via L6e's `r` | 250–400 |
| M5 | per-point | bridge (as in C3b) + `capWindow_flow_metric_eq` + G + M4★ + M1b + M3 + `scaleMetric q⁻¹` | 250–350 |
| Leaf-B | wiring | `by_cases CapWindowPoint`, P0, constants | 60–100 |

Total: about 1.6k–2.5k lines (DESIGN_C4 estimated 2.1k–3.3k, which included SPT, now delivered).
M1b, M2, G, M3 and M1a are independent of each other. M4 needs M1a's def. M4★ needs M1a, M1b,
M2 and M4. M5 needs M4★, M3 and G.

## 4. Single-statement review prompt (M4★)

请审查下面这一个 Lean 陈述（标准解窗口上的空间典范邻域，C4 情形 (B) 的风险所在）：

`exists_window_spatialCanonicalWitness_of_standard_close`：对 `0<ε<1/11`，存在 `Cw≥1`（只依赖 ε），使得对任意 `Θ<1` 与 `r`，存在 `D>r`、阶 `N`、容差 `e>0`，满足：对任意标准解 `Q`、`0≤T≤Θ`、`standardCapWindow D` 上 `[0,T]` 的 Ricci 流 `S`（`IsSolutionOn`），若对所有 `τ∈[0,T]`、`i≤N`、窗口内点 `v`，`metricDerivNorm i (S τ) (Q τ|_D) (StandardCap.metric|_D) v < e`，则对 `‖z‖<r` 及任意 `C2≥Cw`，只要 `S T` 在 `z` 处满足标量梯度界 `|dR(v)| ≤ C2·R^{3/2}|v|`，就存在 `SpatialCanonicalWitness (S T) ε Cw C2 z` 且 `capTubeHasNeckChart ε`。

拟证路线：取 `τ' = max τQ δ⁻¹`（τQ 来自 L6e）。
- 老点 `τ' ≤ T·R_S`：由 L6e 得到 `OrientedWitness S`，再经缓冲典范管线得到 `S` 上的含时见证，投影为空间见证，不做任何度量搬运。
- 幼点：由标量下界 `c₀/(1−T) ≤ R_Q` 推出 `T < Θ₃ = 2τ'/(c₀+2τ')`（与 Θ 无关）。在 `Θ₃` 处取带显式裕度（`m=1/20`：球夹心、深度、半径）的标准解见证，经一致参考度量换算（`StandardMetricReference`）得到 `MetricComparisonOn`，再用容差只依赖 `(α,m,C1,C2,Rlow)` 的一致搬运定理搬到 `S T`；梯度由假设提供，`Rm` 损失并入 `1000·C`。

请回答：
1. 陈述是否为真？尤其是 `Cw` 在 `Θ` 之前选取是否真的可能，`T` 接近 1 的老点是否确实都被 L6e 覆盖。
2. 常数与量词顺序是否正确：`D`、`N`、`e` 依赖于 `Θ` 和 `r`；`e` 必须对 `(Q, T, z)` 一致。
3. 各输入能否由现有定理供给：L6e、B8、27c 在 `Θ₃` 处、参考换算。
4. 请尝试构造反例，例如：夹心比恰为 2 的帽见证、深度取等号、`T·R_S` 恰为 τ′ 的边界、`z` 靠近窗口边界。
