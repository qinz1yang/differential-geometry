import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6StageEscapeRayCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6MinimizerStrongNeckCXSP
import DifferentialGeometry.Geometry.Neck.PointedRay
import DifferentialGeometry.Geometry.Neck.SpatialTolerance

set_option autoImplicit false

/-!
# CX-SPINE：原 stage scalar-blowup ray 继承 canonical spatial necks

消费 StageEscapeRay 实产的 gamma/ray、inverse/scalar convergence，
以及同 Awork 的整段包含。固定 ray point 后，TimeCore 实际生产该点的 W；
两端 scalar gaps 由 pointwise convergence 与终点 scalar blowup 支付。
G33 证明同一个 scaled W 的 alternative 是 neck。
随后公共 PointedRay:22 将 source necks 传入极限；不重做 metric neck transfer。
目标精度 alpha=1/4000000，粗 epsilon<=coneAccuracy 足够。
不调用 Gamma_f 的 analytic 常数。
不增加 source-neck、Good、Dt、gradient、kappa 或 S16 前提；Awork 不冒充 hw(A)。
-/

noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace GC.LongTime.Ch11

universe u

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

/-- 在实产 minimizing segments 上从 TimeCore 的同一 W 生产 neck；
公共 metric transfer 随后给固定精度的 limit-ray necks。 -/
theorem eventually_stage_ray_necks_of_timeCore_CXSP
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    (hcore : CanonicalLateTimeCore_P6X F ε C1 C2 Ctime) (hε : ε ≤ coneAccuracy)
    (Awork : ℝ) (hA : 0 < Awork) (idx : ℕ → ℕ)
    (t : ∀ i, Icc (0 : ℝ) (F.tower.history (idx i)).horizon)
    (p anchor : ∀ i, ((F.tower.history (idx i)).toHistory.stageAt (t i)).Carrier)
    (r : ℕ → ℝ) (htime : ∀ i, 2 * r i ^ 2 < (t i : ℝ))
    (hsmall : ∀ i, hasSmallParabolicCurvature (F.tower.history (idx i)).toHistory
      (t i) (p i) (r i))
    (hvol : ∀ i, ENNReal.ofReal (Awork⁻¹ * r i ^ 3) ≤ ballVolume
      ((F.tower.history (idx i)).toHistory.stageMetric
        ((F.tower.history (idx i)).toHistory.activeStage (t i)) (t i)) (p i) (r i))
    (htlim : Tendsto (fun i => (t i : ℝ)) atTop atTop)
    (Hbase : ℝ) (hHbase : 0 < Hbase) (Q : ℕ → ℝ) (hQ : ∀ i, 0 < Q i)
    (hscale : ∀ i, Q i * r i ^ 2 = Hbase)
    (hanchorR : ∀ i, metricScalarAt
      ((F.tower.history (idx i)).toHistory.stageMetric
        ((F.tower.history (idx i)).toHistory.activeStage (t i)) (t i)) (anchor i) = Q i)
    (rho : ℝ) (hrho : 0 < rho) :
    let stage := fun i => (F.tower.history (idx i)).toHistory.stageAt (t i)
    let metric := fun i => (F.tower.history (idx i)).toHistory.stageMetric
      ((F.tower.history (idx i)).toHistory.activeStage (t i)) (t i)
    let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel :=
      { obj := fun i =>
          { M := (stage i).Carrier
            basepoint := anchor i
            metric := scaleMetric (Q i) (hQ i) (metric i) } }
    ∀ (σ : ℕ → ℕ), StrictMono σ →
    ∀ (Pl : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
      (maps : PointedRiemannianConvergenceMaps X Pl σ)
      (M : MetricConvergenceData maps),
      (∀ n, M.domain n = CanonicalMetricCompactness.canonicalSourceData maps n) →
      (∀ R : ℝ, 0 ≤ R → R < rho →
        IsCompact (riemannianClosedBallOf Pl.metric Pl.basepoint R)) →
    ∀ (ell : ℕ → ℝ) (γ : ∀ n, ℝ → (stage (σ n)).Carrier),
      Tendsto ell atTop (𝓝 rho) →
      (∀ n, γ n 0 = anchor (σ n)) →
      (∀ n, ∀ v ∈ Icc (0 : ℝ) (ell n), ∀ w ∈ Icc (0 : ℝ) (ell n),
        riemannianEDistOf (X.obj (σ n)).metric (γ n v) (γ n w) =
          ENNReal.ofReal |v - w|) →
      (∀ᶠ n in atTop, ∀ v ∈ Icc (0 : ℝ) (ell n),
        γ n v ∈ riemannianBallOf (metric (σ n)) (p (σ n)) (Awork * r (σ n))) →
      Tendsto (fun n => metricScalarAt (metric (σ n)) (γ n (ell n)) / Q (σ n))
        atTop atTop →
    ∀ ray : Ico (0 : ℝ) rho → Pl.M,
      (∀ v : Ico (0 : ℝ) rho, Tendsto (fun n =>
        (maps.partialDiffeomorph n).symm (γ n v)) atTop (𝓝 (ray v))) →
      (∀ v : Ico (0 : ℝ) rho, Tendsto (fun n =>
        metricScalarAt (metric (σ n)) (γ n v) / Q (σ n))
        atTop (𝓝 (metricScalarAt Pl.metric (ray v)))) →
      Tendsto (fun v => metricScalarAt Pl.metric (ray v))
        (comap (Subtype.val : Ico (0 : ℝ) rho → ℝ) (𝓝 rho)) atTop →
      (∀ᶠ v : Ico (0 : ℝ) rho in
          comap (Subtype.val : Ico (0 : ℝ) rho → ℝ) (𝓝 rho),
        ∀ᶠ n in atTop,
          ∃ W : SpatialCanonicalWitness (X.obj (σ n)).metric ε C1 C2 (γ n v),
            W.capTubeHasNeckChart ε ∧
              ∃ neck : SpatialLocalNeck (X.obj (σ n)).metric ε (γ n v) W.domain.carrier,
                W.alternative = SpatialCanonicalAlternative.neck neck) ∧
      ∀ᶠ v : Ico (0 : ℝ) rho in
          comap (Subtype.val : Ico (0 : ℝ) rho → ℝ) (𝓝 rho),
        Nonempty (SpatialNeck Pl.metric (1 / 4000000) (ray v)) := by
  intro stage metric X σ hσ Pl maps M hcanonical hcompact ell γ hell
    hstart hmin hsegment hhigh ray hconv hscalar hblow
  obtain ⟨Kb, Tb, _hKb, _hTb, hcan⟩ := hcore Awork hA
  have hnorm (n : ℕ) (v : ℝ) :
      metricScalarAt (X.obj (σ n)).metric (γ n v) =
        metricScalarAt (metric (σ n)) (γ n v) / Q (σ n) := by
    change metricScalarAt (scaleMetric (Q (σ n)) (hQ (σ n)) (metric (σ n))) _ = _
    rw [metricScalarAt_scaleMetric, inv_mul_eq_div]
  have hbase (n : ℕ) : metricScalarAt (X.obj (σ n)).metric (anchor (σ n)) = 1 := by
    change metricScalarAt (scaleMetric (Q (σ n)) (hQ (σ n)) (metric (σ n))) _ = 1
    rw [metricScalarAt_scaleMetric, hanchorR (σ n), inv_mul_cancel₀ (hQ (σ n)).ne']
  let threshold : ℝ := max 2 (max (C2 + 1) (Kb / Hbase + 1))
  have hsource : ∀ᶠ v : Ico (0 : ℝ) rho in
      comap (Subtype.val : Ico (0 : ℝ) rho → ℝ) (𝓝 rho),
      ∀ᶠ n in atTop,
        ∃ W : SpatialCanonicalWitness (X.obj (σ n)).metric ε C1 C2 (γ n v),
          W.capTubeHasNeckChart ε ∧
            ∃ neck : SpatialLocalNeck (X.obj (σ n)).metric ε (γ n v) W.domain.carrier,
              W.alternative = SpatialCanonicalAlternative.neck neck := by
    have hvpos : ∀ᶠ v : Ico (0 : ℝ) rho in
        comap (Subtype.val : Ico (0 : ℝ) rho → ℝ) (𝓝 rho), 0 < (v : ℝ) :=
      (tendsto_comap : Tendsto (Subtype.val : Ico (0 : ℝ) rho → ℝ) _ (𝓝 rho)).eventually
        (Ioi_mem_nhds hrho)
    filter_upwards [hblow.eventually_gt_atTop threshold, hvpos] with v hv hvpos
    filter_upwards [hell.eventually_const_lt v.property.2,
      (hscalar v).eventually (Ioi_mem_nhds hv),
      (hscalar v).eventually (Iio_mem_nhds (lt_add_one (metricScalarAt Pl.metric (ray v)))),
      hhigh.eventually_gt_atTop (C2 * (metricScalarAt Pl.metric (ray v) + 1)),
      hσ.tendsto_atTop.eventually (htlim.eventually_ge_atTop Tb), hsegment]
      with n hvell hmid hmidup hend hlate hseg
    have hthreshold : Kb * (r (σ n) ^ 2)⁻¹ ≤
        metricScalarAt (metric (σ n)) (γ n v) := by
      have hqbar : Kb / Hbase < metricScalarAt (metric (σ n)) (γ n v) / Q (σ n) := by
        have h := (le_max_right (C2 + 1) (Kb / Hbase + 1)).trans
          (le_max_right 2 (max (C2 + 1) (Kb / Hbase + 1)))
        change threshold < _ at hmid
        dsimp only [threshold] at hmid
        linarith
      rw [← div_eq_mul_inv, div_le_iff₀ (sq_pos_of_pos (hsmall (σ n)).1)]
      calc
        Kb ≤ (metricScalarAt (metric (σ n)) (γ n v) / Q (σ n)) * Hbase :=
          (div_le_iff₀ hHbase).mp hqbar.le
        _ = metricScalarAt (metric (σ n)) (γ n v) * r (σ n) ^ 2 := by
          rw [← hscale (σ n), ← mul_assoc, div_mul_cancel₀ _ (hQ (σ n)).ne']
    obtain ⟨Wraw, hchart⟩ := (hcan (idx (σ n)) (t (σ n)) (p (σ n)) (r (σ n))
      hlate (htime (σ n)) (hsmall (σ n)) (hvol (σ n)) (γ n v)
      (hseg v ⟨v.property.1, hvell.le⟩) hthreshold).1
    let W := Wraw.scaleMetric (Q (σ n)) (hQ (σ n))
    have hchartW : W.capTubeHasNeckChart ε := hchart.scaleMetric (Q (σ n)) (hQ (σ n))
    have hleft : C2 * metricScalarAt (X.obj (σ n)).metric (γ n 0) <
        metricScalarAt (X.obj (σ n)).metric (γ n v) := by
      rw [hstart n, hbase n, mul_one, hnorm]
      have h := (le_max_left (C2 + 1) (Kb / Hbase + 1)).trans
        (le_max_right 2 (max (C2 + 1) (Kb / Hbase + 1)))
      dsimp only [threshold] at hmid
      linarith
    have hright : C2 * metricScalarAt (X.obj (σ n)).metric (γ n v) <
        metricScalarAt (X.obj (σ n)).metric (γ n (ell n)) := by
      rw [hnorm, hnorm]
      have hC2 : 0 ≤ C2 := zero_le_one.trans Wraw.one_le_comparison_constant
      exact (mul_le_mul_of_nonneg_left hmidup.le hC2).trans_lt hend
    obtain ⟨neck, hneck⟩ := W.alternative_eq_neck_of_minimizing_scalar_gaps_CXSP
      hchartW hε hvpos hvell (hmin n) rfl hleft hright
    exact ⟨W, hchartW, neck, hneck⟩
  refine ⟨hsource, ?_⟩
  let alpha : ℝ := 1 / 4000000
  let tol : ℝ := min (neckModelTolerance (alpha / 26000)) (alpha / 26000 / 64)
  have halpha : 0 < alpha := by norm_num [alpha]
  have halphaSmall : alpha < 1 / 11 := by norm_num [alpha]
  have htol : 0 < tol := lt_min (neckModelTolerance_pos (by positivity)) (by positivity)
  have hεtol : ε ≤ tol := by
    have hh : ε ≤ tol / (13000 * 13000) := hε
    exact hh.trans (div_le_self htol.le (by norm_num))
  have htolSmall : tol < 1 / 11 :=
    (min_le_right _ _).trans_lt (by norm_num [alpha])
  have hhighNorm : Tendsto (fun n =>
      metricScalarAt (X.obj (σ n)).metric (γ n (ell n))) atTop atTop := by
    exact hhigh.congr fun n => (hnorm n (ell n)).symm
  exact eventually_spatial_neck_on_limit_ray_of_source_necks M hcanonical halpha halphaSmall
    ell hell hcompact γ hstart hmin ray hconv hhighNorm hblow
    (hsource.mono fun v hv => hv.mono fun n hn _hR => by
      obtain ⟨_W, _hchart, neck, _hneck⟩ := hn
      exact ⟨neck.neck.mono hεtol htolSmall⟩)

end GC.LongTime.Ch11

end
