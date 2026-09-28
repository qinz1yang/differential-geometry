import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BoundedCurvatureAtDistanceLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BoundedCurvatureAtDistanceNecks
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BoundedCurvatureAtDistanceCone
import DifferentialGeometry.Geometry.Neck.FiniteEnd
import DifferentialGeometry.Geometry.Metric.Segment

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

theorem RetainedCoreHistory.exists_normalized_scalar_bound_of_final_slab_window
    (H : ℕ → RetainedCoreHistory.{u}) (time : ℕ → ℝ)
    (A : ∀ i, ((H i).stage (Fin.last (H i).eventCount)).ClosedSlab
      ((H i).time (Fin.last (H i).eventCount)) (time i))
    (hinit : ∀ i, (A i).flow.base.metric ((H i).time (Fin.last (H i).eventCount)) =
      (H i).initialMetric (Fin.last (H i).eventCount))
    (hs : ∀ i, (H i).horizon < time i) (Ctime Cgrad : ℝ≥0) (q : ℕ → ℝ) (hq : ∀ i, 0 < q i)
    (hderiv : ∀ i (j : Fin (H i).eventCount) (y : ((H i).stage j.castSucc).Carrier),
      ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
        q i < ((H i).toHistory.event j).incoming.flow.scalar t y →
        |derivWithin (fun v => ((H i).toHistory.event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * ((H i).toHistory.event j).incoming.flow.scalar t y ^ 2)
    (hfinal : ∀ i y, ∀ t ∈ Ioo ((H i).time (Fin.last (H i).eventCount)) (time i),
      q i < (A i).flow.scalar t y →
      |derivWithin (fun v => (A i).flow.scalar v y) (Iic t) t| ≤
        Ctime * (A i).flow.scalar t y ^ 2)
    (hgradient : ∀ i y, ∀ t ∈ Ioo ((H i).time (Fin.last (H i).eventCount)) (time i),
      q i < (A i).flow.scalar t y → ∀ v : TangentSpace ThreeModel y,
        |Perelman.CanonicalNeighborhood.scalarDifferential
            ((A i).restrictIncoming le_rfl (A i).lt le_rfl).flow t y v| ≤
          Cgrad * (A i).flow.scalar t y * Real.sqrt ((A i).flow.scalar t y) *
            Real.sqrt (((A i).flow.base.metric t).inner y v v))
    (x : ∀ i, ((A i).restrictIncoming le_rfl (A i).lt le_rfl).terminalRegularOpen)
    (hQ : ∀ i, 1 ≤ (A i).flow.scalar (time i) (x i).val)
    (hqQ : ∀ i, q i ≤ (A i).flow.scalar (time i) (x i).val)
    (hQlim : Tendsto (fun i => (A i).flow.scalar (time i) (x i).val) atTop atTop)
    (hqlim : Tendsto (fun i => q i / (A i).flow.scalar (time i) (x i).val) atTop (𝓝 0))
    {θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    (hwindow : ∀ i, (H i).time (Fin.last (H i).eventCount) ≤
      time i - θ₀ / (A i).flow.scalar (time i) (x i).val)
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hpinch : ∀ i j, Perelman.PhiAlmostNonnegative ((H i).toHistory.event j).incoming.flow
      (Ico ((H i).time j.castSucc) ((H i).time j.succ)) Phi)
    (hpinchFinal : ∀ i, Perelman.PhiAlmostNonnegative
      ((A i).restrictIncoming le_rfl (A i).lt le_rfl).flow
      (Ico ((H i).time (Fin.last (H i).eventCount)) (time i)) Phi)
    {κ σ₀ : ℝ} (σ : ℕ → ℝ) (hκ : 0 < κ) (hσ₀ : 0 < σ₀)
    (hσQ : ∀ i, σ₀ ≤ σ i * Real.sqrt ((A i).flow.scalar (time i) (x i).val))
    (htested : ∀ i (t : ℝ) (ht : (H i).horizon < t) (hts : t < time i),
      let B := (H i).extendHorizon t ht.le
        (((A i).restrictIncoming le_rfl (A i).lt le_rfl).closedPrefix t
          ((H i).time_le_horizon.trans_lt ht) hts) (hinit i)
      let tm : Icc (0 : ℝ) B.horizon := ⟨t, (H i).horizon_nonneg.trans ht.le, le_rfl⟩
      ∀ (y : (B.toHistory.stageAt tm).Carrier) (b : ℝ), 0 < b → b ≤ σ i →
        B.toHistory.isParabolicallyRmControlledBall tm y b →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel (B.toHistory.stageAt tm).Carrier
              (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
              (riemannianBallOf (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm) y b))
    {eps C1 C2 : ℝ}
    (heps : 13000 * (13000 * eps) ≤
      min (neckModelTolerance (1 / 4000000 / 26000)) (1 / 4000000 / 26000 / 64))
    (hW : ∀ i y, q i < (A i).flow.scalar (time i) y →
      ∃ W : SpatialCanonicalWitness ((A i).flow.base.metric (time i)) eps C1 C2 y,
        W.capTubeHasNeckChart eps) :
    ∀ R : ℝ, 0 < R → ∃ B : ℝ, ∀ᶠ i in atTop,
      ∀ y : ((A i).restrictIncoming le_rfl (A i).lt le_rfl).terminalRegularOpen,
        riemannianEDistOf (scaleMetric ((A i).flow.scalar (time i) (x i).val)
          (zero_lt_one.trans_le (hQ i))
          ((A i).endpointTerminalLimitMetric ((H i).stage (Fin.last (H i).eventCount))).metric)
          (x i) y < ENNReal.ofReal R →
        metricScalarAt
          ((A i).endpointTerminalLimitMetric ((H i).stage (Fin.last (H i).eventCount))).metric y /
            (A i).flow.scalar (time i) (x i).val ≤ B := by
  intro R hR
  by_contra hB
  have hL1 := RetainedCoreHistory.exists_pointed_convergence_at_scalar_escape_of_final_slab_window
    H time A hinit hs Ctime Cgrad q hq hderiv hfinal hgradient x hQ hqQ θ₀ hθ₀ hwindow
    ⟨R, hR, hB⟩ Phi hPhi hpinch hpinchFinal κ σ₀ σ hκ hσ₀ hσQ htested
  dsimp only at hL1
  obtain ⟨rho, hrho, ind, hind, z, f, hf, r, hr, hrlim, Pl, F₀, M, _, hcan, hradial, hcompact,
      hcapture, hmetric, hfinite, hdist, hescape⟩ := hL1
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
  obtain ⟨g, hg, _, hblow, hnecks⟩ := exists_isometric_ray_with_spatialNecks_of_scalar_escape
    (fun i => (H (ind i)).stage (Fin.last (H (ind i)).eventCount))
    (fun i => (H (ind i)).time (Fin.last (H (ind i)).eventCount)) (fun i => time (ind i))
    (fun i => A (ind i)) Ctime Cgrad (fun i => q (ind i)) (fun i => hfinal (ind i))
    (fun i => hgradient (ind i)) (fun i => x (ind i)) (fun i => hQ (ind i))
    (fun i => hqQ (ind i)) (hqlim.comp hind.tendsto_atTop) halpha (by norm_num) heps
    (fun i => hW (ind i)) hrho f hf r (fun n => (hr n).1) hrlim Pl F M hcan hradial hcompact
    hcapture (fun ε hε => (hmetric ε hε).mono fun n hn y hy v => (hn y hy v).1)
    (fun n => z (f n)) hfinite hdist hescape
  have hsec := metricRm04StandardAt_nonneg_of_normalized_terminal_pinching
    (fun i => (H (ind i)).stage (Fin.last (H (ind i)).eventCount))
    (fun i => (H (ind i)).time (Fin.last (H (ind i)).eventCount)) (fun i => time (ind i))
    (fun i => A (ind i)) (fun i => x (ind i)) (fun i => hQ (ind i)) hPhi
    (fun i => hpinchFinal (ind i)) Pl F M hcan (hQlim.comp (hind.comp hf).tendsto_atTop)
  let _ : EMetricSpace Pl.M := Pl.emetricSpace
  have hfin : ∀ a b : Pl.M, edist a b ≠ ⊤ := by
    intro a b
    apply ne_top_of_le_ne_top _ (edist_triangle_left a b Pl.basepoint)
    exact ENNReal.add_ne_top.mpr ⟨(hradial a).ne_top, (hradial b).ne_top⟩
  let _ : MetricSpace Pl.M := EMetricSpace.toMetricSpace hfin
  obtain ⟨qc, hqc, _⟩ :=
    DifferentialGeometry.Geometry.exists_completion_endpoint_of_isometry hrho hg
  obtain ⟨W, hWc, hrest⟩ := exists_punctured_cone_end_of_spatial_necks Pl.metric
    (fun _ _ => rfl) hrho halpha (by norm_num) hsec g hg hblow qc hqc hnecks
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
  obtain ⟨qW, delta, hdelta, _, _, hK, hcover, xW, _, _, _, hxW, _, hQW, hlowerW, hupperW,
    hcone⟩ := hrest
  have hQW' : Tendsto (fun n => metricScalarAt Pl.metric (xW n : Pl.M)) atTop atTop := by
    simpa only [metricScalarAt_restrictOpen] using hQW
  have hlower' : ∀ᶠ n in atTop, ((2 * (1 / 4000000 : ℝ))⁻¹) ^ 2 / 8 ≤
      metricScalarAt Pl.metric (xW n : Pl.M) *
        dist (xW n : UniformSpace.Completion W) qW ^ 2 :=
    Eventually.of_forall fun n => by simpa only [metricScalarAt_restrictOpen] using hlowerW n
  have hupper' : ∃ B : ℝ, ∀ᶠ n in atTop, metricScalarAt Pl.metric (xW n : Pl.M) *
      dist (xW n : UniformSpace.Completion W) qW ^ 2 ≤ B := by
    obtain ⟨B, _, hB⟩ := hupperW
    exact ⟨B, by simpa only [metricScalarAt_restrictOpen] using hB⟩
  exact RetainedCoreHistory.final_slab_punctured_cone_end_exclusion
    (fun i => H (ind i)) (fun i => time (ind i)) (fun i => A (ind i)) (fun i => hinit (ind i))
    (fun i => hs (ind i)) Ctime (fun i => q (ind i)) (fun i => hq _) (fun i => hderiv (ind i))
    (fun i => hfinal (ind i)) (fun i => x (ind i)) (fun i => hQ _) (fun i => hqQ _)
    (hqlim.comp hind.tendsto_atTop) hθ₀ (fun i => hwindow _) hPhi (fun i => hpinch _)
    (fun i => hpinchFinal _) (fun i => σ (ind i)) hκ hσ₀ (fun i => hσQ _)
    (fun i => htested (ind i)) (fun i => hW (ind i)) hf Pl F M hcan W hWc qW delta hdelta hK
    hcover hcone xW hxW hQW' _ (by norm_num) hlower' hupper'

theorem RetainedCoreHistory.exists_scalar_bound_at_distance_of_final_slab_window
    (κ C1 C2 : ℝ) (hκ : 0 < κ) (Ctime Cgrad : ℝ≥0) {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi) :
    ∃ εcone : ℝ, 0 < εcone ∧ ∀ ε : ℝ, ε ≤ εcone → ∀ A : ℝ, 0 < A →
      ∃ Q Λ : ℝ, 1 ≤ Q ∧ 1 ≤ Λ ∧
      ∀ (H : RetainedCoreHistory.{u})
        (hend : H.time (Fin.last H.eventCount) = H.horizon) {t : ℝ}
        (S : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) t)
        (hS : S.flow.base.metric (H.time (Fin.last H.eventCount)) =
          H.initialMetric (Fin.last H.eventCount))
        (y : (H.stage (Fin.last H.eventCount)).Carrier) (q ρ : ℝ),
        1 ≤ q → Λ * q < S.flow.scalar t y →
        H.time (Fin.last H.eventCount) ≤ t - Λ / S.flow.scalar t y →
        (∀ x, q < S.flow.scalar t x →
          ∃ W : SpatialCanonicalWitness (S.flow.base.metric t) ε C1 C2 x,
            W.capTubeHasNeckChart ε) →
        H.EventSlabsDerivative Ctime q (Fin.last H.eventCount) →
        (S.restrictIncoming le_rfl S.lt le_rfl).DerivativeBoundBefore Ctime q t →
        (S.restrictIncoming le_rfl S.lt le_rfl).GradientBoundBefore Cgrad q t →
        H.EventSlabsPinched phi →
        Perelman.PhiAlmostNonnegative (S.restrictIncoming le_rfl S.lt le_rfl).flow
          (Ico (H.time (Fin.last H.eventCount)) t) phi →
        H.TerminalNoncollapsedBefore hend (S.restrictIncoming le_rfl S.lt le_rfl) hS κ ρ t →
        Λ ≤ ρ * Real.sqrt (S.flow.scalar t y) →
        ∀ z ∈ riemannianBallOf (S.flow.base.metric t) y (A / Real.sqrt (S.flow.scalar t y)),
          S.flow.scalar t z ≤ Q * S.flow.scalar t y := by
  have hmin : 0 < min (neckModelTolerance (1 / 4000000 / 26000)) (1 / 4000000 / 26000 / 64) :=
    lt_min (neckModelTolerance_pos (by norm_num)) (by norm_num)
  refine ⟨min (neckModelTolerance (1 / 4000000 / 26000)) (1 / 4000000 / 26000 / 64) /
    (13000 * 13000), by positivity, ?_⟩
  intro ε hεle A hA
  have heps : 13000 * (13000 * ε) ≤
      min (neckModelTolerance (1 / 4000000 / 26000)) (1 / 4000000 / 26000 / 64) := by
    have h := (le_div_iff₀ (by norm_num : (0 : ℝ) < 13000 * 13000)).mp hεle
    linarith
  by_contra hcon
  push Not at hcon
  choose H hend t S hS y q ρ hq1 hΛq hwin hW hderiv hfinal hgrad hpinch hpinchF hnc hρ z hz
    hbad using fun n : ℕ => hcon ((n : ℝ) + 1) ((n : ℝ) + 1)
      (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]) (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
  have hn0 (n : ℕ) : (0 : ℝ) ≤ n := n.cast_nonneg
  have hR (n : ℕ) : (n : ℝ) + 1 < (S n).flow.scalar (t n) (y n) := by
    have h := hΛq n
    nlinarith [hq1 n, hn0 n]
  have hRpos (n : ℕ) : 0 < (S n).flow.scalar (t n) (y n) := by linarith [hR n, hn0 n]
  let x : ∀ n, ((S n).restrictIncoming le_rfl (S n).lt le_rfl).terminalRegularOpen := fun n =>
    ⟨y n, by
      change y n ∈ ((S n).restrictIncoming le_rfl (S n).lt le_rfl).terminalRegularRegion
      rw [(S n).terminalRegularRegion_eq_univ _]
      trivial⟩
  have hQ (n : ℕ) : 1 ≤ (S n).flow.scalar (t n) (x n).val := by
    change 1 ≤ (S n).flow.scalar (t n) (y n)
    linarith [hR n, hn0 n]
  have hqQ (n : ℕ) : q n ≤ (S n).flow.scalar (t n) (x n).val := by
    change q n ≤ (S n).flow.scalar (t n) (y n)
    nlinarith [hΛq n, hq1 n, hn0 n]
  have hQlim : Tendsto (fun n => (S n).flow.scalar (t n) (x n).val) atTop atTop :=
    tendsto_atTop_mono (fun n => (hR n).le)
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hqlim : Tendsto (fun n => q n / (S n).flow.scalar (t n) (x n).val) atTop (𝓝 0) := by
    have hlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
    refine squeeze_zero (fun n => div_nonneg (by linarith [hq1 n]) (hRpos n).le) (fun n => ?_) hlim
    change q n / (S n).flow.scalar (t n) (y n) ≤ 1 / ((n : ℝ) + 1)
    rw [div_le_div_iff₀ (hRpos n) (by linarith [hn0 n])]
    nlinarith [hΛq n]
  have hwindow (n : ℕ) : (H n).time (Fin.last (H n).eventCount) ≤
      t n - 1 / (S n).flow.scalar (t n) (x n).val := by
    change (H n).time (Fin.last (H n).eventCount) ≤ t n - 1 / (S n).flow.scalar (t n) (y n)
    have h := hwin n
    have hdiv : 1 / (S n).flow.scalar (t n) (y n) ≤
        ((n : ℝ) + 1) / (S n).flow.scalar (t n) (y n) :=
      div_le_div_of_nonneg_right (by linarith [hn0 n]) (hRpos n).le
    linarith
  have hσQ (n : ℕ) : 1 ≤ ρ n * Real.sqrt ((S n).flow.scalar (t n) (x n).val) :=
    le_trans (by linarith [hn0 n]) (hρ n)
  obtain ⟨B, hB⟩ := RetainedCoreHistory.exists_normalized_scalar_bound_of_final_slab_window
    H t S hS (fun n => by rw [← hend n]; exact (S n).lt) Ctime Cgrad q
    (fun n => by linarith [hq1 n]) (fun n j y' t' ht hqy => hderiv n j (Fin.castSucc_lt_last j)
      y' t' ht hqy) (fun n y' t' ht hqy => hfinal n y' t' ht hqy)
    (fun n y' t' ht hqy => hgrad n y' t' ht hqy) x hQ hqQ hQlim hqlim one_pos hwindow hphi
    (fun n => hpinch n) (fun n => hpinchF n) ρ hκ one_pos hσQ
    (fun n T hT hTs => by
      intro _ tm yy b _ hbρ hball
      exact hnc n T (by rw [hend n]; exact hT) hTs hTs.le tm yy b le_rfl hbρ hball)
    heps (fun n => hW n) (A + 1) (by linarith)
  obtain ⟨n, hn, hnB⟩ := (hB.and (eventually_gt_atTop ⌈B⌉₊)).exists
  let z' : ((S n).restrictIncoming le_rfl (S n).lt le_rfl).terminalRegularOpen :=
    ⟨z n, by
      change z n ∈ ((S n).restrictIncoming le_rfl (S n).lt le_rfl).terminalRegularRegion
      rw [(S n).terminalRegularRegion_eq_univ _]
      trivial⟩
  have hsq := Real.sqrt_pos.mpr (hRpos n)
  have hdist : riemannianEDistOf (scaleMetric ((S n).flow.scalar (t n) (x n).val)
      (zero_lt_one.trans_le (hQ n)) ((S n).endpointTerminalLimitMetric _).metric) (x n) z' <
        ENNReal.ofReal (A + 1) := by
    rw [DifferentialGeometry.edistOf_scale, (S n).riemannianEDistOf_endpointTerminalLimitMetric]
    change ENNReal.ofReal (Real.sqrt ((S n).flow.scalar (t n) (y n))) *
      riemannianEDistOf ((S n).flow.base.metric (t n)) (y n) (z n) < _
    calc ENNReal.ofReal (Real.sqrt ((S n).flow.scalar (t n) (y n))) *
          riemannianEDistOf ((S n).flow.base.metric (t n)) (y n) (z n) <
        ENNReal.ofReal (Real.sqrt ((S n).flow.scalar (t n) (y n))) *
          ENNReal.ofReal (A / Real.sqrt ((S n).flow.scalar (t n) (y n))) :=
          ENNReal.mul_lt_mul_right (ENNReal.ofReal_pos.mpr hsq).ne' ENNReal.ofReal_ne_top (hz n)
      _ = ENNReal.ofReal A := by
          rw [← ENNReal.ofReal_mul hsq.le]
          congr 1
          field_simp
      _ < ENNReal.ofReal (A + 1) := (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
  have hle := hn z' hdist
  have hscal : metricScalarAt ((S n).endpointTerminalLimitMetric _).metric z' =
      (S n).flow.scalar (t n) (z n) := metricScalarAt_restrictOpen _ _ _
  rw [hscal] at hle
  change (S n).flow.scalar (t n) (z n) / (S n).flow.scalar (t n) (y n) ≤ B at hle
  have hbig := (le_div_iff₀ (hRpos n)).mpr (hbad n).le
  have hceil : B ≤ (n : ℝ) := (Nat.le_ceil B).trans (by exact_mod_cast hnB.le)
  linarith

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
