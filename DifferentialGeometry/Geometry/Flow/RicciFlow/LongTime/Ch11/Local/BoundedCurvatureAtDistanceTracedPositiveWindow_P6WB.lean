import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.BoundedCurvatureAtDistanceTracedPositive_P6L
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.BoundedCurvatureAtDistanceTracedLimit2Window_P6WB
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.BoundedCurvatureAtDistanceBoundedThresholdWindow_P6WB
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.BoundedCurvatureAtDistanceTracedSecondLevelWindow_P6WB
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.BoundedCurvatureAtDistanceNecksWindow_P6WA
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.BoundedCurvatureAtDistanceTracedConeWindow_P6WA

/-!
# P6WIN-B G4：`TracedPositive:55`（= `TP:97`，L6 装配）的时间窗形（`_P6WB`）

P6CON G2b 窗口 spine（A 段 → 02:5x RELEASE 给 B）：`TP:97_P6L` 的 `hderiv` / `hfinal` / `hgradient` /
`hpinch` / `hpinchFinal` / `htested` 只经窗口 `[a i, time i]` 内的叶子求值 ⇒ 窗口形（接口约定 §2–§3，
与 A 的 `TC:493` 窗口版、B 的 `TL2:73` / `BT:98` / `TSL:231` 窗口版同形）：
* `U` 后 `(a : ℕ → ℝ) (ha : ∀ i, a i < time i)`（F6）；`hqQ` 后
  `hQa : Q i * (time i - a i) → ∞`（F5：`hbuf` 的 `θ` 是存在量）；
* `hderiv` / `hfinal` / `hgradient`：`∀ t ∈ Ioo …,` 后 guard `a i ≤ t →`；`hpinch` / `hpinchFinal` 取
  `Ico … ∩ Ici (a i)`；`htested`：`hts` 后 `a i ≤ t →`；
* 证明体照抄，叶子换：`TL2:73` / `BT:98` / `TSL:231`（`_window_P6WB`）、`Necks:413`（`_window_P6WA`）与
  `TC:493` `…_of_radius_window_P6WA`；`TP:33`（`traced_buffer_of_chain_traces_P6L`）与 `TC:844` 桥无窗口前提
  （原名）。结论逐字（`∀ R, 0 < R → R + 2 ≤ Rad → ∃ B, …`）。
consumer：`TP:97_P6L`（全 slab 形）⇐ 窗口形（`a i = time i - (i + 1) / Q i`，`exists_window_start_P6WA`）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s) :
    SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

private local instance pointedLimitRegular (L : PointedRiemannianManifold.{u, 0, 0} ThreeModel) :
    RegularSpace L.M := by
  let _ : LocallyCompactSpace L.M := ChartedSpace.locallyCompactSpace ThreeSpace L.M
  infer_instance

/-- **`_window_P6WB`（`TP:55` = `TP:97` 窗口形，L6 装配）**：`_P6L` 之上（接口约定 §2、§3）：
`U` 后 `(a : ℕ → ℝ) (ha : ∀ i, a i < time i)`（F6）；`hqQ` 后 `hQa : Q i * (time i - a i) → ∞`（F5）；
`hderiv` / `hfinal` / `hgradient` 的 `∀ t ∈ Ioo …,` 后 guard `a i ≤ t →`；`hpinch` / `hpinchFinal` 取
`… ∩ Ici (a i)`；`htested` 的 `hts` 后加 `a i ≤ t →`；`htrace`、`hW`、`hU`、结论（`R + 2 ≤ Rad`）逐字。
叶子换窗口版：`TL2:73`（`_P6WB`）、`BT:98`（`_P6WB`，`c := a ∘ ind`）、`Necks:413`（`_P6WA`）、`TSL:231`
（`_P6WB`）、`TC:493` 的 `…_of_radius_window_P6WA`；`TP:33`（`traced_buffer_of_chain_traces_P6L`）无窗口前提。 -/
theorem RetainedCoreHistory.exists_normalized_scalar_bound_of_chain_traces_window_P6WB
    (H : ℕ → RetainedCoreHistory.{u}) (time : ℕ → ℝ)
    (A : ∀ i, ((H i).stage (Fin.last (H i).eventCount)).ClosedSlab
      ((H i).time (Fin.last (H i).eventCount)) (time i))
    (hinit : ∀ i, (A i).flow.base.metric ((H i).time (Fin.last (H i).eventCount)) =
      (H i).initialMetric (Fin.last (H i).eventCount))
    (hs : ∀ i, (H i).horizon < time i) (Ctime Cgrad : ℝ≥0) (q : ℕ → ℝ) (hq : ∀ i, 0 < q i)
    (U : ∀ i, Set ((H i).stage (Fin.last (H i).eventCount)).Carrier)
    (a : ℕ → ℝ) (ha : ∀ i, a i < time i)
    (hderiv : ∀ i, ∀ j : Fin (H i).eventCount,
      ∀ (first : Fin ((H i).eventCount + 1)) (hf : first ≤ j.castSucc),
      ∀ z ∈ U i, ∀ B : BackwardPointTrace (H i).toHistory first (Fin.last (H i).eventCount)
        (Fin.le_last first) z,
      ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ), a i ≤ t →
      q i < ((H i).toHistory.event j).incoming.flow.scalar t
        (B.point j.castSucc hf (Fin.le_last _)) →
      |derivWithin (fun v => ((H i).toHistory.event j).incoming.flow.scalar v
        (B.point j.castSucc hf (Fin.le_last _))) (Iic t) t| ≤
        Ctime * ((H i).toHistory.event j).incoming.flow.scalar t
          (B.point j.castSucc hf (Fin.le_last _)) ^ 2)
    (hfinal : ∀ i, ∀ y ∈ U i, ∀ t ∈ Ioo ((H i).time (Fin.last (H i).eventCount)) (time i),
      a i ≤ t → q i < (A i).flow.scalar t y →
      |derivWithin (fun v => (A i).flow.scalar v y) (Iic t) t| ≤
        Ctime * (A i).flow.scalar t y ^ 2)
    (hgradient : ∀ i, ∀ y ∈ U i, ∀ t ∈ Ioo ((H i).time (Fin.last (H i).eventCount)) (time i),
      a i ≤ t → q i < (A i).flow.scalar t y → ∀ v : TangentSpace ThreeModel y,
        |Perelman.CanonicalNeighborhood.scalarDifferential
            ((A i).restrictIncoming le_rfl (A i).lt le_rfl).flow t y v| ≤
          Cgrad * (A i).flow.scalar t y * Real.sqrt ((A i).flow.scalar t y) *
            Real.sqrt (((A i).flow.base.metric t).inner y v v))
    (x : ∀ i, ((A i).restrictIncoming le_rfl (A i).lt le_rfl).terminalRegularOpen)
    (hQ : ∀ i, 1 ≤ (A i).flow.scalar (time i) (x i).val)
    (hqQ : ∀ i, q i ≤ (A i).flow.scalar (time i) (x i).val)
    (hQa : Tendsto (fun i => (A i).flow.scalar (time i) (x i).val * (time i - a i)) atTop atTop)
    (Rad : ℝ) (hU : ∀ i, ∀ y ∈ riemannianBallOf
      (scaleMetric ((A i).flow.scalar (time i) (x i).val) (zero_lt_one.trans_le (hQ i))
        ((A i).endpointTerminalLimitMetric ((H i).stage (Fin.last (H i).eventCount))).metric)
      (x i) Rad, y.val ∈ U i)
    (hQlim : Tendsto (fun i => (A i).flow.scalar (time i) (x i).val) atTop atTop)
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hpinch : ∀ i j, Perelman.PhiAlmostNonnegative ((H i).toHistory.event j).incoming.flow
      (Ico ((H i).time j.castSucc) ((H i).time j.succ) ∩ Ici (a i)) Phi)
    (hpinchFinal : ∀ i, Perelman.PhiAlmostNonnegative
      ((A i).restrictIncoming le_rfl (A i).lt le_rfl).flow
      (Ico ((H i).time (Fin.last (H i).eventCount)) (time i) ∩ Ici (a i)) Phi)
    {κ σ₀ : ℝ} (σ : ℕ → ℝ) (hκ : 0 < κ) (hσ₀ : 0 < σ₀)
    (hσQ : ∀ i, σ₀ ≤ σ i * Real.sqrt ((A i).flow.scalar (time i) (x i).val))
    (htested : ∀ i (t : ℝ) (ht : (H i).horizon < t) (hts : t < time i), a i ≤ t →
      let B := (H i).extendHorizon t ht.le
        (((A i).restrictIncoming le_rfl (A i).lt le_rfl).closedPrefix t
          ((H i).time_le_horizon.trans_lt ht) hts) (hinit i)
      let tm : Icc (0 : ℝ) B.horizon := ⟨t, (H i).horizon_nonneg.trans ht.le, le_rfl⟩
      ∀ z ∈ U i, ∀ (y : (B.toHistory.stageAt tm).Carrier), HEq y z →
      ∀ (b : ℝ), 0 < b → b ≤ σ i →
        B.toHistory.isParabolicallyRmControlledBall tm y b →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel (B.toHistory.stageAt tm).Carrier
              (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
              (riemannianBallOf (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm) y b))
    {eps C1 C2 : ℝ}
    (heps : 13000 * (13000 * eps) ≤
      min (neckModelTolerance (1 / 4000000 / 26000)) (1 / 4000000 / 26000 / 64))
    (hW : ∀ i, ∀ y ∈ U i, q i < (A i).flow.scalar (time i) y →
      ∃ W : SpatialCanonicalWitness ((A i).flow.base.metric (time i)) eps C1 C2 y,
        W.capTubeHasNeckChart eps)
    (htime : Tendsto (fun i => (A i).flow.scalar (time i) (x i).val * time i) atTop atTop)
    {Kc lam θ : ℝ} (hlam : 0 ≤ lam) (hθ : 0 < θ) (D : ℕ → ℝ) (hD : Tendsto D atTop atTop)
    (htrace : ∀ i (N : ℕ) (p : ℕ → ((H i).stage (Fin.last (H i).eventCount)).Carrier)
      (δ : ℕ → ℝ) (M τ : ℝ), p 0 = (x i).val → (∀ k ≤ N, 0 < δ k) →
      (∀ k ≤ N, ∀ z ∈ riemannianBallOf ((A i).flow.base.metric (time i)) (p k) (δ k), z ∈ U i) →
      (∀ k < N, p (k + 1) ∈ riemannianBallOf ((A i).flow.base.metric (time i)) (p k) (δ k)) →
      (∀ k ≤ N, ∀ z ∈ riemannianBallOf ((A i).flow.base.metric (time i)) (p k) (δ k),
        (A i).flow.scalar (time i) z ≤ M) →
      Kc * (A i).flow.scalar (time i) (x i).val ≤ M → 1 ≤ M → 0 ≤ τ → τ ≤ time i →
      (Ctime : ℝ) * M * τ ≤ 1 / 2 → 4 * M * τ ≤ θ →
      2 * StandardCap.transitionEnd + Real.sqrt (8 * M) *
        Real.exp (9 * (8 * Real.sqrt 3 * (1 + Phi 1 + Phi 0) * M) * τ) *
          (lam / Real.sqrt ((A i).flow.scalar (time i) (x i).val) +
            ∑ k ∈ Finset.range (N + 1), δ k) < D i →
      ∀ k ≤ N, ∀ z ∈ riemannianBallOf ((A i).flow.base.metric (time i)) (p k) (δ k),
        ∃ first : Fin ((H i).eventCount + 1), (H i).time first ≤ time i - τ ∧
          Nonempty (BackwardPointTrace (H i).toHistory first (Fin.last (H i).eventCount)
            (Fin.le_last first) z)) :
    ∀ R : ℝ, 0 < R → R + 2 ≤ Rad → ∃ B : ℝ, ∀ᶠ i in atTop,
      ∀ y : ((A i).restrictIncoming le_rfl (A i).lt le_rfl).terminalRegularOpen,
        riemannianEDistOf (scaleMetric ((A i).flow.scalar (time i) (x i).val)
          (zero_lt_one.trans_le (hQ i))
          ((A i).endpointTerminalLimitMetric ((H i).stage (Fin.last (H i).eventCount))).metric)
          (x i) y < ENNReal.ofReal R →
        metricScalarAt
          ((A i).endpointTerminalLimitMetric ((H i).stage (Fin.last (H i).eventCount))).metric y /
            (A i).flow.scalar (time i) (x i).val ≤ B := by
  intro R hR hRRad
  by_contra hB
  have hbuf : ∀ R' ε' B' : ℝ, 0 < R' → 0 < ε' → (∀ᶠ i in atTop, ∀ y ∈ riemannianClosedBallOf
        (scaleMetric ((A i).flow.scalar (time i) (x i).val) (zero_lt_one.trans_le (hQ i))
          ((A i).endpointTerminalLimitMetric ((H i).stage (Fin.last (H i).eventCount))).metric)
          (x i) (R' + ε'),
        metricScalarAt ((A i).endpointTerminalLimitMetric
          ((H i).stage (Fin.last (H i).eventCount))).metric y ≤
          B' * (A i).flow.scalar (time i) (x i).val) →
      ∃ θ₁ : ℝ, 0 < θ₁ ∧ ∀ᶠ i in atTop, ∃ first : Fin ((H i).eventCount + 1),
        (H i).time first ≤ time i - θ₁ / (A i).flow.scalar (time i) (x i).val ∧
        ∀ y ∈ riemannianClosedBallOf
          (scaleMetric ((A i).flow.scalar (time i) (x i).val) (zero_lt_one.trans_le (hQ i))
            ((A i).endpointTerminalLimitMetric ((H i).stage (Fin.last (H i).eventCount))).metric)
          (x i) R',
          Nonempty (BackwardPointTrace (H i).toHistory first (Fin.last (H i).eventCount)
            (Fin.le_last first) y.val) := by
    intro R' ε' B' hR' hε' hB'
    by_cases hlt : R' + ε' < R
    · exact RetainedCoreHistory.traced_buffer_of_chain_traces_P6L H time A x hQ U Rad hU hθ D hD
        htime htrace R' ε' B' hR' hε' (by linarith) hB'
    · exfalso
      apply hB
      refine ⟨B', hB'.mono fun i hi y hy => ?_⟩
      rw [div_le_iff₀ (zero_lt_one.trans_le (hQ i))]
      exact hi y (hy.trans_le (ENNReal.ofReal_le_ofReal (not_lt.mp hlt))).le
  have hL1 :=
    RetainedCoreHistory.exists_pointed_convergence_at_scalar_escape_of_traced_buffer_rad_window_P6WB
    H time A hinit hs Ctime Cgrad q hq U a ha hderiv hfinal hgradient x hQ hqQ hQa Rad hU hbuf
    ⟨R, hR, hRRad, hB⟩ Phi hPhi hpinch hpinchFinal κ σ₀ σ hκ hσ₀ hσQ htested
  dsimp only at hL1
  obtain ⟨rho, hrho, hrhoRad, ind, hind, z, f, hf, r, hr, hrlim, Pl, F₀, M, _, hcan, hradial,
      hcompact, hcapture, hmetric, hfinite, hdist, hescape⟩ := hL1
  let F := PointedRiemannianConvergenceMaps.liftTargetOpen
    (S := { obj := fun i =>
          { M := ((A (ind i)).restrictIncoming le_rfl (A (ind i)).lt le_rfl).terminalRegularOpen
            basepoint := x (ind i)
            metric := scaleMetric ((A (ind i)).flow.scalar (time (ind i)) (x (ind i)).val)
              (zero_lt_one.trans_le (hQ (ind i)))
              ((A (ind i)).endpointTerminalLimitMetric
                ((H (ind i)).stage (Fin.last (H (ind i)).eventCount))).metric } })
    (fun i => connectedComponentOpen (I := ThreeModel) (x (ind i)))
    (fun i => (mem_connectedComponent : x (ind i) ∈
      connectedComponentOpen (I := ThreeModel) (x (ind i)))) F₀
  have halpha : (0 : ℝ) < 1 / 4000000 := by norm_num
  obtain ⟨g, hg, hg0, hblow, hnecks⟩ :=
    exists_isometric_ray_with_spatialNecks_of_bounded_threshold_window_P6WB
    (fun i => (H (ind i)).stage (Fin.last (H (ind i)).eventCount))
    (fun i => (H (ind i)).time (Fin.last (H (ind i)).eventCount)) (fun i => time (ind i))
    (fun i => A (ind i)) Cgrad (fun i => q (ind i)) (fun i => U (ind i))
    (fun i => a (ind i)) (fun i => ha (ind i)) (fun i => hgradient (ind i))
    (fun i => x (ind i)) (fun i => hQ (ind i)) (fun i => hqQ (ind i)) halpha (by norm_num) heps
    (fun i => hW (ind i)) hrho f hf r (fun n => (hr n).1) hrlim Pl F M hcan hradial hcompact
    hcapture (fun ε hε => (hmetric ε hε).mono fun n hn y hy v => (hn y hy v).1)
    (fun n => z (f n)) hfinite hdist hescape (Rad := rho + 1) (by linarith) (fun i y hy => by
      have hQi : 0 < (A (ind i)).flow.scalar (time (ind i)) (x (ind i)).val :=
        zero_lt_one.trans_le (hQ (ind i))
      have hlpr := Perelman.CanonicalNeighborhood.localPropagationRadius_pos Cgrad.coe_nonneg
      have hlpr' := Perelman.CanonicalNeighborhood.localPropagationRadius_le Cgrad.coe_nonneg
      have hsQ : 0 < Real.sqrt ((A (ind i)).flow.scalar (time (ind i)) (x (ind i)).val) :=
        Real.sqrt_pos.mpr hQi
      have hs2 : Real.sqrt ((A (ind i)).flow.scalar (time (ind i)) (x (ind i)).val) ≤
          Real.sqrt (2 * (A (ind i)).flow.scalar (time (ind i)) (x (ind i)).val) :=
        Real.sqrt_le_sqrt (by linarith)
      have hs2pos := hsQ.trans_le hs2
      have h1 : Real.sqrt ((A (ind i)).flow.scalar (time (ind i)) (x (ind i)).val) *
          (Perelman.CanonicalNeighborhood.localPropagationRadius Cgrad /
            Real.sqrt (2 * (A (ind i)).flow.scalar (time (ind i)) (x (ind i)).val)) ≤
          Perelman.CanonicalNeighborhood.localPropagationRadius Cgrad := by
        rw [mul_div_assoc', div_le_iff₀ hs2pos]
        exact (mul_comm _ _).trans_le (mul_le_mul_of_nonneg_left hs2 hlpr.le)
      refine (A (ind i)).eventually_moving_ball_subset_of_terminal_ball_P6L (U (ind i)) y.val
        (by positivity) ?_
      exact (A (ind i)).ball_subset_of_scaled_dist_lt_P6L hQi (x (ind i)) y (U (ind i))
        (by linarith) (by positivity) hy (by nlinarith) (hU (ind i)))
  have hsec := metricRm04StandardAt_nonneg_of_normalized_terminal_pinching_window_P6WA
    (fun i => (H (ind i)).stage (Fin.last (H (ind i)).eventCount))
    (fun i => (H (ind i)).time (Fin.last (H (ind i)).eventCount)) (fun i => time (ind i))
    (fun i => A (ind i)) (fun i => a (ind i)) (fun i => ha (ind i)) (fun i => x (ind i))
    (fun i => hQ (ind i)) hPhi (fun i => hpinchFinal (ind i)) Pl F M hcan
    (hQlim.comp (hind.comp hf).tendsto_atTop)
  let _ : EMetricSpace Pl.M := Pl.emetricSpace
  have hfin : ∀ a b : Pl.M, edist a b ≠ ⊤ := by
    intro a b
    apply ne_top_of_le_ne_top _ (edist_triangle_left a b Pl.basepoint)
    exact ENNReal.add_ne_top.mpr ⟨(hradial a).ne_top, (hradial b).ne_top⟩
  let _ : MetricSpace Pl.M := EMetricSpace.toMetricSpace hfin
  obtain ⟨qc, hqc, _⟩ :=
    DifferentialGeometry.Geometry.exists_completion_endpoint_of_isometry hrho hg
  obtain ⟨W, hWc, hrest⟩ := exists_punctured_cone_end_of_spatial_necks_with_ray_scalar_bound
    Pl.metric (fun _ _ => rfl) hrho halpha (by norm_num) hsec g hg hblow qc hqc hnecks
  let _ : PathConnectedSpace W := hWc
  let mW : MetricSpace W :=
    let _ : PseudoMetricSpace W := (Pl.metric.restrictOpen W).toPseudoMetricSpace
    MetricSpace.ofT0PseudoMetricSpace W
  let _ : MetricSpace W := mW
  let _ : PseudoMetricSpace W := mW.toPseudoMetricSpace
  let _ : UniformSpace W := mW.toPseudoMetricSpace.toUniformSpace
  let eW : PseudoEMetricSpace W :=
    @PseudoMetricSpace.toPseudoEMetricSpace W mW.toPseudoMetricSpace
  let _ : WeakPseudoEMetricSpace W :=
    @PseudoEMetricSpace.toWeakPseudoEMetricSpace W eW
  obtain ⟨qW, delta, hdelta, _, _, hK, hcover, xW, times, hux, _, hxW, _, hQW, hlowerW, hupperW,
    hcone, Kr, hKr1, hKr⟩ := hrest
  have hQW' : Tendsto (fun n => metricScalarAt Pl.metric (xW n : Pl.M)) atTop atTop := by
    simpa only [metricScalarAt_restrictOpen] using hQW
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.mp (hKr.and (hQW'.eventually_ge_atTop 3))
  have hlower' : ∀ᶠ n in atTop, ((2 * (1 / 4000000 : ℝ))⁻¹) ^ 2 / 8 ≤
      metricScalarAt Pl.metric (xW (n + m₀) : Pl.M) *
        dist (xW (n + m₀) : UniformSpace.Completion W) qW ^ 2 :=
    Eventually.of_forall fun n => by
      simpa only [metricScalarAt_restrictOpen] using hlowerW (n + m₀)
  have hupper' : ∃ B : ℝ, ∀ᶠ n in atTop, metricScalarAt Pl.metric (xW (n + m₀) : Pl.M) *
      dist (xW (n + m₀) : UniformSpace.Completion W) qW ^ 2 ≤ B := by
    obtain ⟨B, _, hB⟩ := hupperW
    have hB' : ∀ᶠ n in atTop, metricScalarAt Pl.metric (xW n : Pl.M) *
        dist (xW n : UniformSpace.Completion W) qW ^ 2 ≤ B := by
      simpa only [metricScalarAt_restrictOpen] using hB
    exact ⟨B, (tendsto_add_atTop_nat m₀).eventually hB'⟩
  have hux' (m : ℕ) : (xW (m + m₀) : Pl.M) = g (times (m + m₀)) := hux (m + m₀)
  obtain ⟨θ₂, hθ₂, htr₂⟩ :=
    RetainedCoreHistory.eventually_second_level_traces_of_chain_traces_window_P6WB
    (fun i => H (ind i)) (fun i => time (ind i)) (fun i => A (ind i))
    Cgrad (fun i => q (ind i)) (fun i => U (ind i)) (fun i => a (ind i)) (fun i => ha (ind i))
    (fun i => hgradient (ind i)) (fun i => x (ind i)) (fun i => hQ (ind i)) (fun i => hqQ (ind i))
    Rad (fun i => hU (ind i))
    (fun i => hW (ind i)) hlam hθ hPhi
    (fun i => D (ind i)) (hD.comp hind.tendsto_atTop) (htime.comp hind.tendsto_atTop)
    (fun i => htrace (ind i)) hf Pl F M hcan g (fun s t => (hg.edist_eq s t : _)) hrhoRad
    ⟨0, le_rfl, hrho⟩ rfl hg0 (fun m => times (m + m₀)) (fun m => (xW (m + m₀) : Pl.M)) hux'
    hKr1 (fun m => by
      have h := (hm₀ (m + m₀) (Nat.le_add_left _ _)).1
      intro s hs
      rw [← hux (m + m₀)] at h ⊢
      exact h s hs)
    (fun m => by
      rw [← hux (m + m₀)]
      exact (hm₀ (m + m₀) (Nat.le_add_left _ _)).2)
  open RetainedCoreHistory in
  exact final_slab_punctured_cone_end_exclusion_of_trace_chains_of_radius_window_P6WA
    (fun i => H (ind i)) (fun i => time (ind i)) (fun i => A (ind i)) (fun i => hinit (ind i))
    (fun i => hs (ind i)) Ctime (fun i => q (ind i)) (fun i => hq _) (fun i => U (ind i))
    (fun i => a (ind i)) (fun i => ha (ind i)) (fun i => hderiv (ind i))
    (fun i => hfinal (ind i)) (fun i => x (ind i)) (fun i => hQ _) (fun i => hqQ _)
    (hQa.comp hind.tendsto_atTop) Rad (fun i => hU (ind i)) hPhi (fun i => hpinch _)
    (fun i => hpinchFinal _) (fun i => σ (ind i)) hκ hσ₀ (fun i => hσQ _)
    (fun i => htested (ind i)) (fun i => hW (ind i)) hf Pl F M hcan hradial hrhoRad W hWc qW
    delta hdelta hK
    hcover hcone (fun n => xW (n + m₀)) (hxW.comp (tendsto_add_atTop_nat m₀))
    (hQW'.comp (tendsto_add_atTop_nat m₀)) θ₂ hθ₂ htr₂ _ (by norm_num) hlower' hupper'

/-- consumer：`TP:97_P6L`（全 slab 形）⇐ 窗口形（`a i = time i - (i + 1) / Q i`）。 -/
example : type_of% @RetainedCoreHistory.exists_normalized_scalar_bound_of_chain_traces_P6L.{u} := by
  intro H time A hinit hs Ctime Cgrad q hq U hderiv hfinal hgradient x hQ hqQ Rad hU hQlim Phi hPhi
    hpinch hpinchFinal κ σ₀ σ hκ hσ₀ hσQ htested eps C1 C2 heps hW htime Kc lam θ hlam hθ D hD
    htrace
  obtain ⟨a, ha, hQa⟩ := exists_window_start_P6WA time
    (fun i => (A i).flow.scalar (time i) (x i).val) (fun i => zero_lt_one.trans_le (hQ i))
  exact RetainedCoreHistory.exists_normalized_scalar_bound_of_chain_traces_window_P6WB H time A
    hinit hs Ctime Cgrad q hq U a ha
    (fun i j first hf z hz B t ht _ => hderiv i j first hf z hz B t ht)
    (fun i y hy t ht _ => hfinal i y hy t ht) (fun i y hy t ht _ => hgradient i y hy t ht) x hQ hqQ
    hQa Rad hU hQlim hPhi (fun i j t ht w => hpinch i j t ht.1 w)
    (fun i t ht w => hpinchFinal i t ht.1 w) σ hκ hσ₀ hσQ
    (fun i t ht hts _ => htested i t ht hts) heps hW htime hlam hθ D hD htrace

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
